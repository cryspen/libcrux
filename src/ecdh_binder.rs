//! # ECDH Binder
//!
//! This module implements a protocol binder that binds a post-quantum
//! pre-shared key component to an outer ECDH based key agreement.

use libcrux::aead::{decrypt_detached, Algorithm};
use libcrux_ecdh::{X25519PrivateKey, X25519PublicKey};
use std::time::{Duration, SystemTime};

use rand::{CryptoRng, Rng};

use crate::{
    psq::{PrivateKey, PublicKey},
    Error, Psk,
};

const DH_PSK_CONTEXT: &[u8] = b"DH-PSK";
const DH_PSK_LENGTH: usize = 32;

const AEAD_RECEIVER: &[u8] = b"AEAD-Responder";
const AEAD_INITIATOR: &[u8] = b"AEAD-Initiator";
const AEAD_KEY_NONCE: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305)
    + Algorithm::nonce_size(Algorithm::Chacha20Poly1305);

const AEAD_KEY_LENGTH: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305);

/// An ECDH-bound PSQ encapsulation.
pub struct ECDHPsk {
    encapsulation: crate::psq::Ciphertext,
    initiator_dh_pk: Vec<u8>,
    aead_mac: (libcrux::aead::Tag, Vec<u8>),
    psk_ttl: Duration,
    ts: Duration,
}

/// Generates a post-quantum pre-shared key (PQ-PSK) bound to an ECDH key.
///
/// The encapsulated PSK is valid for the given duration
/// `psk_ttl`, based on milliseconds since the UNIX epoch until
/// current system time. Parameter `sctx` is used to
/// cryptographically bind the generated PSK to a given outer
/// protocol context and may be considered public.
pub fn send_ecdh_bound_psq(
    psq_pk: &PublicKey,
    receiver_dh_pk: &X25519PublicKey,
    initiator_dh_sk: &X25519PrivateKey,
    psk_ttl: Duration,
    sctx: &[u8],
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Psk, ECDHPsk), Error> {
    let now = SystemTime::now();
    let ts = now
        .duration_since(SystemTime::UNIX_EPOCH)
        .expect("now cannot be before UNIX_EPOCH");
    let ts_seconds = ts.as_secs();
    let ts_subsec_millis = ts.subsec_millis();
    let mut ts_ttl = ts_seconds.to_be_bytes().to_vec();
    ts_ttl.extend_from_slice(&ts_subsec_millis.to_be_bytes());
    ts_ttl.extend_from_slice(&psk_ttl.as_millis().to_be_bytes());

    let (ss_q, encapsulation) = psq_pk.gen_pq_psk(sctx, rng)?;
    let ss_dh = libcrux_ecdh::x25519_derive(receiver_dh_pk, initiator_dh_sk)
        .map_err(|_| Error::CryptoError)?;

    // ikm = ss_q || ss_dh
    let mut ikm = Vec::from(ss_q);
    ikm.extend_from_slice(&ss_dh.0);

    let prk = libcrux_hkdf::extract(libcrux_hkdf::Algorithm::Sha256, b"", ikm);

    let psk: [u8; DH_PSK_LENGTH] = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        prk,
        DH_PSK_CONTEXT,
        DH_PSK_LENGTH,
    )
    .map_err(|_| Error::CryptoError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");

    // NOTE: Make this a real cipherstate and pass it outside?
    let (initiator_iv, initiator_key, _receiver_iv, _receiver_key) = derive_cipherstate(psk)?;

    let aad = ts_ttl;
    let initiator_dh_pk =
        libcrux_ecdh::secret_to_public(libcrux_ecdh::Algorithm::X25519, initiator_dh_sk)
            .map_err(|_| Error::CryptoError)?;
    let aead_mac =
        libcrux::aead::encrypt_detached(&initiator_key, &initiator_dh_pk, initiator_iv, aad)
            .map_err(|_| Error::CryptoError)?;

    Ok((
        psk,
        ECDHPsk {
            encapsulation,
            initiator_dh_pk,
            aead_mac,
            psk_ttl,
            ts,
        },
    ))
}

/// Derive an ECDH-bound PSK from a PQ-PSK message.
///
/// Errors if the PQ-PSK message lifetime is elapsed.
pub fn receive_ecdh_bound_psq(
    receiver_pqsk: &PrivateKey,
    receiver_pqpk: &PublicKey,
    receiver_dh_sk: &X25519PrivateKey,
    ecdh_psk_message: &ECDHPsk,
    sctx: &[u8],
) -> Result<Psk, Error> {
    let ECDHPsk {
        encapsulation,
        initiator_dh_pk,
        aead_mac,
        psk_ttl,
        ts,
    } = ecdh_psk_message;
    let ss_q = receiver_pqsk.derive_pq_psk(receiver_pqpk, encapsulation, sctx)?;
    let initiator_dh_pk_bytes: [u8; 32] = initiator_dh_pk[0..32]
        .try_into()
        .map_err(|_| Error::InvalidPublicKey)?;
    let initiator_dh_pk_point = libcrux_ecdh::X25519PublicKey(initiator_dh_pk_bytes);
    let ss_dh = libcrux_ecdh::x25519_derive(&initiator_dh_pk_point, receiver_dh_sk)
        .map_err(|_| Error::CryptoError)?;

    // ikm = ss_q || ss_dh
    let mut ikm = Vec::from(ss_q);
    ikm.extend_from_slice(&ss_dh.0);

    let prk = libcrux_hkdf::extract(libcrux_hkdf::Algorithm::Sha256, b"", ikm);

    let psk: [u8; DH_PSK_LENGTH] = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        prk,
        DH_PSK_CONTEXT,
        DH_PSK_LENGTH,
    )
    .map_err(|_| Error::CryptoError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");

    // NOTE: Make this a real cipherstate and pass it outside?
    let (initiator_iv, initiator_key, _receiver_iv, _receiver_key) = derive_cipherstate(psk)?;

    let ts_seconds = ts.as_secs();
    let ts_subsec_millis = ts.subsec_millis();
    let mut ts_ttl = ts_seconds.to_be_bytes().to_vec();
    ts_ttl.extend_from_slice(&ts_subsec_millis.to_be_bytes());
    ts_ttl.extend_from_slice(&psk_ttl.as_millis().to_be_bytes());

    let aad = ts_ttl;
    let initiator_dh_pk_decrypted =
        decrypt_detached(&initiator_key, &aead_mac.1, initiator_iv, aad, &aead_mac.0)
            .map_err(|_| Error::CryptoError)?;

    // validate TTL
    let now = SystemTime::now();
    let ts_since_epoch =
        Duration::from_secs(ts_seconds) + Duration::from_millis((ts_subsec_millis).into());
    if initiator_dh_pk_decrypted != *initiator_dh_pk
        || now
            .duration_since(SystemTime::UNIX_EPOCH)
            .expect("now cannot be before UNIX_EPOCH")
            - ts_since_epoch
            >= *psk_ttl
    {
        Err(Error::BinderError)
    } else {
        Ok(psk)
    }
}

fn derive_cipherstate(
    psk: [u8; 32],
) -> Result<
    (
        libcrux::aead::Iv,
        libcrux::aead::Key,
        libcrux::aead::Iv,
        libcrux::aead::Key,
    ),
    Error,
> {
    let (initiator_iv, initiator_key) = derive_key_iv(psk, AEAD_INITIATOR)?;
    let (receiver_iv, receiver_key) = derive_key_iv(psk, AEAD_RECEIVER)?;

    Ok((initiator_iv, initiator_key, receiver_iv, receiver_key))
}

fn derive_key_iv(
    psk: [u8; 32],
    info: &[u8],
) -> Result<(libcrux::aead::Iv, libcrux::aead::Key), Error> {
    let key_iv_bytes =
        libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, psk, info, AEAD_KEY_NONCE)
            .map_err(|_| Error::CryptoError)?;
    let (key_bytes, iv_bytes) = key_iv_bytes.split_at(AEAD_KEY_LENGTH);
    let key = libcrux::aead::Key::from_bytes(
        libcrux::aead::Algorithm::Chacha20Poly1305,
        key_bytes.to_vec(),
    )
    .map_err(|_| Error::CryptoError)?;
    let iv = libcrux::aead::Iv(
        iv_bytes
            .try_into()
            .expect("should receive the correct number of bytes"),
    );
    Ok((iv, key))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    #[test]
    fn simple() {
        let mut rng = rand::thread_rng();
        let (receiver_pqsk, receiver_pqpk) =
            crate::psq::generate_key_pair(crate::psq::Algorithm::MlKem768, &mut rng).unwrap();
        let (receiver_dh_sk, receiver_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
        let (initiator_dh_sk, _initiator_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();

        let sctx = b"test context";
        let (_psk_initiator, ecdh_psk_message) = send_ecdh_bound_psq(
            &receiver_pqpk,
            &receiver_dh_pk,
            &initiator_dh_sk,
            Duration::from_secs(3600),
            sctx,
            &mut rng,
        )
        .unwrap();

        let _psk_receiver = receive_ecdh_bound_psq(
            &receiver_pqsk,
            &receiver_pqpk,
            &receiver_dh_sk,
            &ecdh_psk_message,
            sctx,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn zero_ttl() {
        let mut rng = rand::thread_rng();
        let (receiver_pqsk, receiver_pqpk) =
            crate::psq::generate_key_pair(crate::psq::Algorithm::X25519, &mut rng).unwrap();
        let (receiver_dh_sk, receiver_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
        let (initiator_dh_sk, _initiator_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();

        let sctx = b"test context";
        let (_psk_initiator, ecdh_psk_message) = send_ecdh_bound_psq(
            &receiver_pqpk,
            &receiver_dh_pk,
            &initiator_dh_sk,
            Duration::from_secs(0),
            sctx,
            &mut rng,
        )
        .unwrap();

        let _psk_receiver = receive_ecdh_bound_psq(
            &receiver_pqsk,
            &receiver_pqpk,
            &receiver_dh_sk,
            &ecdh_psk_message,
            sctx,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn expired_timestamp() {
        let mut rng = rand::thread_rng();
        let (receiver_pqsk, receiver_pqpk) =
            crate::psq::generate_key_pair(crate::psq::Algorithm::X25519, &mut rng).unwrap();
        let (receiver_dh_sk, receiver_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
        let (initiator_dh_sk, _initiator_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();

        let sctx = b"test context";
        let (_psk_initiator, ecdh_psk_message) = send_ecdh_bound_psq(
            &receiver_pqpk,
            &receiver_dh_pk,
            &initiator_dh_sk,
            Duration::from_secs(1),
            sctx,
            &mut rng,
        )
        .unwrap();

        std::thread::sleep(Duration::from_secs(2));

        let _psk_receiver = receive_ecdh_bound_psq(
            &receiver_pqsk,
            &receiver_pqpk,
            &receiver_dh_sk,
            &ecdh_psk_message,
            sctx,
        )
        .unwrap();
    }
}
