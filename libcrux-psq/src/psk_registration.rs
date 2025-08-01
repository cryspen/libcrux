//! # PSK Registration Protocol
//!
//! This module implements a protocol for mutual registration of a
//! PQ-PSK between an initiator and a responder.

use libcrux_chacha20poly1305::{decrypt_detached, encrypt_detached, KEY_LEN, NONCE_LEN, TAG_LEN};
use libcrux_traits::kem::KEM;
use rand::CryptoRng;
use std::{
    io::Cursor,
    time::{Duration, SystemTime},
};
use tls_codec::{Deserialize, Serialize, Size, TlsDeserialize, TlsSerialize, TlsSize};

use crate::{cred::Authenticator, traits::*, Error, Psk};

const PSK_REGISTRATION_CONTEXT: &[u8] = b"PSK-Registration";
const PSK_LENGTH: usize = 32;

const AEAD_RESPONDER: &[u8] = b"AEAD-Responder-Initiator";
const AEAD_INITIATOR: &[u8] = b"AEAD-Initiator-Responder";
const AEAD_KEY_NONCE: usize = KEY_LEN + NONCE_LEN;
const AEAD_KEY_LENGTH: usize = KEY_LEN;

const TS_TTL_LEN: usize = 28;

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
struct AeadMac {
    tag: [u8; TAG_LEN],
    ctxt: Vec<u8>,
}

/// The Initiator's message to the responder.
#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
pub struct InitiatorMsg<
    T: KEM<
        Ciphertext: Deserialize + Serialize + Size,
        SharedSecret: Serialize + Size,
        EncapsulationKey: Serialize + Size,
    >,
> {
    encapsulation: Ciphertext<T>,
    aead_mac: AeadMac,
}

/// The Responder's message to the initiator.
#[derive(TlsSize, TlsSerialize, TlsDeserialize)]
pub struct ResponderMsg {
    aead_mac: AeadMac,
}

/// A finished PSK with an attached storage handle.
pub struct RegisteredPsk {
    /// The PSK
    pub psk: Psk,
    /// The PSK's handle for storing
    pub psk_handle: Vec<u8>,
}

/// The protocol initiator.
pub struct Initiator {
    k_pq: [u8; 32],
}

/// The protocol responder.
///
/// Is in charge of designating a PSK storage handle.
pub struct Responder {}

impl Initiator {
    /// Send the initial message encapsulating a PQ-PrePSK.
    pub fn send_initial_message<C: Authenticator, T: PSQ>(
        sctx: &[u8],
        psk_ttl: Duration,
        pqpk_responder: &<T::InnerKEM as KEM>::EncapsulationKey,
        signing_key: &C::SigningKey,
        credential: &C::Credential,
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, InitiatorMsg<T::InnerKEM>), Error> {
        let (k_pq, enc_pq) = T::encapsulate_psq(pqpk_responder, sctx, rng)?;
        let (initiator_iv, initiator_key, _receiver_iv, _receiver_key) = derive_cipherstate(&k_pq)?;

        let now = SystemTime::now();
        let ts = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| Error::OsError)?;

        let ts_ttl = serialize_ts_ttl(&ts, &psk_ttl);

        let mut enc_pq_serialized = vec![0u8; enc_pq.tls_serialized_len()];
        enc_pq
            .tls_serialize(&mut &mut enc_pq_serialized[..])
            .map_err(|_| Error::Serialization)?;

        let signature = C::sign(signing_key, &enc_pq_serialized)?;

        let mut message = Vec::new();
        message.extend_from_slice(&ts_ttl);
        let _ = signature
            .tls_serialize(&mut &mut message)
            .map_err(|_| Error::Serialization)?;
        let _ = credential
            .tls_serialize(&mut &mut message)
            .map_err(|_| Error::Serialization)?;

        let mut ctxt = message.clone();
        let mut tag = [0u8; TAG_LEN];
        let _ = encrypt_detached(
            &initiator_key,
            &message,
            &mut ctxt,
            &mut tag,
            b"",
            &initiator_iv,
        )?;
        let aead_mac = AeadMac { tag, ctxt };

        Ok((
            Self { k_pq },
            InitiatorMsg {
                encapsulation: enc_pq,
                aead_mac,
            },
        ))
    }

    /// Receive the responder's response and derive a PSK under the
    /// given handle.
    pub fn complete_handshake(
        &self,
        responder_message: &ResponderMsg,
    ) -> Result<RegisteredPsk, Error> {
        let (_initiator_iv, _initiator_key, responder_iv, responder_key) =
            derive_cipherstate(&self.k_pq)?;

        let mut psk_handle = responder_message.aead_mac.ctxt.clone();
        let _ = decrypt_detached(
            &responder_key,
            &mut psk_handle,
            &responder_message.aead_mac.ctxt,
            &responder_message.aead_mac.tag,
            b"",
            &responder_iv,
        )?;

        let psk = derive_psk(&self.k_pq)?;

        Ok(RegisteredPsk { psk, psk_handle })
    }
}

fn serialize_ts_ttl(ts: &Duration, psk_ttl: &Duration) -> [u8; TS_TTL_LEN] {
    let ts_seconds = ts.as_secs();
    let ts_subsec_millis = ts.subsec_millis();
    let mut ts_ttl = [0u8; TS_TTL_LEN];
    ts_ttl[0..8].copy_from_slice(&ts_seconds.to_be_bytes());
    ts_ttl[8..12].copy_from_slice(&ts_subsec_millis.to_be_bytes());
    ts_ttl[12..].copy_from_slice(&psk_ttl.as_millis().to_be_bytes());

    ts_ttl
}

fn deserialize_ts(bytes: &[u8]) -> Result<(u64, u32), Error> {
    let ts_seconds = u64::from_be_bytes(
        bytes[0..8]
            .try_into()
            .map_err(|_| Error::RegistrationError)?,
    );
    let ts_subsec_millis = u32::from_be_bytes(
        bytes[8..12]
            .try_into()
            .map_err(|_| Error::RegistrationError)?,
    );

    Ok((ts_seconds, ts_subsec_millis))
}

impl Responder {
    /// On successful decapsulation of the PQ-PrePSK, send the response.
    pub fn send<C: Authenticator, T: PSQ>(
        psk_handle: &[u8],
        psk_ttl: Duration,
        sctxt: &[u8],
        pqpk: &<T::InnerKEM as KEM>::EncapsulationKey,
        pqsk: &<T::InnerKEM as KEM>::DecapsulationKey,
        client_certificate: &C::Certificate,
        initiator_message: &InitiatorMsg<T::InnerKEM>,
    ) -> Result<(RegisteredPsk, ResponderMsg), Error> {
        let k_pq = T::decapsulate_psq(pqsk, pqpk, &initiator_message.encapsulation, sctxt)?;
        let (initiator_iv, initiator_key, responder_iv, responder_key) = derive_cipherstate(&k_pq)?;

        let mut msg_bytes = initiator_message.aead_mac.ctxt.clone();
        let _ = decrypt_detached(
            &initiator_key,
            &mut msg_bytes,
            &initiator_message.aead_mac.ctxt,
            &initiator_message.aead_mac.tag,
            b"",
            &initiator_iv,
        )?;

        let mut encapsulation_serialized =
            vec![0u8; initiator_message.encapsulation.tls_serialized_len()];
        initiator_message
            .encapsulation
            .tls_serialize(&mut &mut encapsulation_serialized[..])
            .map_err(|_| Error::Serialization)?;

        let (ts_bytes, sig_cred_bytes) = msg_bytes.split_at(TS_TTL_LEN);
        let mut sig_cred_cursor = Cursor::new(sig_cred_bytes);
        let signature =
            C::Signature::tls_deserialize(&mut sig_cred_cursor).map_err(|_| Error::Decoding)?;
        let credential =
            C::Credential::tls_deserialize(&mut sig_cred_cursor).map_err(|_| Error::Decoding)?;
        let verification_key = C::validate_credential(credential, client_certificate)?;
        if C::verify(&verification_key, &signature, &encapsulation_serialized).is_err() {
            return Err(Error::RegistrationError);
        }

        let (ts_seconds, ts_subsec_millis) = deserialize_ts(ts_bytes)?;

        // validate TTL
        let now = SystemTime::now();
        let ts_since_epoch =
            Duration::from_secs(ts_seconds) + Duration::from_millis((ts_subsec_millis).into());
        let now = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| Error::OsError)?;

        let psk = derive_psk(&k_pq)?;

        let mut tag = [0u8; TAG_LEN];
        let mut ctxt = psk_handle.to_vec();
        let _ = encrypt_detached(
            &responder_key,
            psk_handle,
            &mut ctxt,
            &mut tag,
            b"",
            &responder_iv,
        )?;

        let aead_mac = AeadMac {
            tag,
            ctxt: ctxt.to_owned(),
        };

        if now < ts_since_epoch {
            // time seems to have gone backwards
            Err(Error::OsError)
        } else if now - ts_since_epoch >= psk_ttl {
            Err(Error::RegistrationError)
        } else {
            Ok((
                RegisteredPsk {
                    psk,
                    psk_handle: psk_handle.to_owned(),
                },
                ResponderMsg { aead_mac },
            ))
        }
    }
}

fn derive_psk(prk: &[u8; 32]) -> Result<Psk, Error> {
    let psk: [u8; PSK_LENGTH] = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        prk,
        PSK_REGISTRATION_CONTEXT,
        PSK_LENGTH,
    )?
    .try_into()
    .map_err(|_| Error::CryptoError)?;

    Ok(psk)
}

fn derive_cipherstate(
    psk: &[u8; 32],
) -> Result<
    (
        [u8; NONCE_LEN],
        [u8; KEY_LEN],
        [u8; NONCE_LEN],
        [u8; KEY_LEN],
    ),
    Error,
> {
    let (initiator_iv, initiator_key) = derive_key_iv(psk, AEAD_INITIATOR)?;
    let (receiver_iv, receiver_key) = derive_key_iv(psk, AEAD_RESPONDER)?;

    Ok((initiator_iv, initiator_key, receiver_iv, receiver_key))
}

fn derive_key_iv(psk: &[u8; 32], info: &[u8]) -> Result<([u8; NONCE_LEN], [u8; KEY_LEN]), Error> {
    let key_iv_bytes =
        libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, psk, info, AEAD_KEY_NONCE)?;
    let (key_bytes, iv_bytes) = key_iv_bytes.split_at(AEAD_KEY_LENGTH);
    let key = <[u8; AEAD_KEY_LENGTH]>::try_from(key_bytes)?;
    let iv = <[u8; NONCE_LEN]>::try_from(iv_bytes)?;
    Ok((iv, key))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::{
        cred::{Ed25519, NoAuth},
        impls::MlKem768,
    };

    use super::*;

    #[test]
    fn registration_no_auth_mlkem768() {
        let mut rng = rand::rng();
        let (receiver_pqsk, receiver_pqpk) = MlKem768::generate_key_pair(&mut rng).unwrap();

        let sctx = b"test context";
        let psk_handle = b"test handle";
        let (initiator, initiator_msg) = Initiator::send_initial_message::<NoAuth, MlKem768>(
            sctx,
            Duration::from_secs(3600),
            &receiver_pqpk,
            &[0; 0],
            &[0; 0],
            &mut rng,
        )
        .unwrap();

        let (handled_psk_responder, respone_msg) = Responder::send::<NoAuth, MlKem768>(
            psk_handle,
            Duration::from_secs(3600),
            sctx,
            &receiver_pqpk,
            &receiver_pqsk,
            &[],
            &initiator_msg,
        )
        .unwrap();

        assert_eq!(handled_psk_responder.psk_handle, psk_handle);

        let handled_psk_initiator = initiator.complete_handshake(&respone_msg).unwrap();

        assert_eq!(
            handled_psk_initiator.psk_handle,
            handled_psk_responder.psk_handle
        );
        assert_eq!(handled_psk_initiator.psk, handled_psk_responder.psk);
    }

    #[test]
    fn registration_ed25519_mlkem768() {
        let mut rng = rand::rng();
        let (receiver_pqsk, receiver_pqpk) = MlKem768::generate_key_pair(&mut rng).unwrap();
        let (sk, pk) = libcrux_ed25519::generate_key_pair(&mut rng).unwrap();

        let sctx = b"test context";
        let psk_handle = b"test handle";
        let (initiator, initiator_msg) = Initiator::send_initial_message::<Ed25519, MlKem768>(
            sctx,
            Duration::from_secs(3600),
            &receiver_pqpk,
            sk.as_ref(),
            &pk,
            &mut rng,
        )
        .unwrap();

        let (handled_psk_responder, respone_msg) = Responder::send::<Ed25519, MlKem768>(
            psk_handle,
            Duration::from_secs(3600),
            sctx,
            &receiver_pqpk,
            &receiver_pqsk,
            &pk,
            &initiator_msg,
        )
        .unwrap();

        assert_eq!(handled_psk_responder.psk_handle, psk_handle);

        let handled_psk_initiator = initiator.complete_handshake(&respone_msg).unwrap();

        assert_eq!(
            handled_psk_initiator.psk_handle,
            handled_psk_responder.psk_handle
        );
        assert_eq!(handled_psk_initiator.psk, handled_psk_responder.psk);
    }

    #[test]
    #[cfg(feature = "classic-mceliece")]
    fn registration_ed25519_classic_mceliece() {
        use crate::classic_mceliece::ClassicMcEliece;

        let mut rng = rand::rng();
        let (receiver_pqsk, receiver_pqpk) =
            crate::classic_mceliece::ClassicMcEliece::generate_key_pair(&mut rng).unwrap();
        let (sk, pk) = libcrux_ed25519::generate_key_pair(&mut rng).unwrap();

        let sctx = b"test context";
        let psk_handle = b"test handle";
        let (initiator, initiator_msg) =
            Initiator::send_initial_message::<Ed25519, ClassicMcEliece>(
                sctx,
                Duration::from_secs(3600),
                &receiver_pqpk,
                sk.as_ref(),
                &pk,
                &mut rng,
            )
            .unwrap();

        let (handled_psk_responder, respone_msg) = Responder::send::<Ed25519, ClassicMcEliece>(
            psk_handle,
            Duration::from_secs(3600),
            sctx,
            &receiver_pqpk,
            &receiver_pqsk,
            &pk,
            &initiator_msg,
        )
        .unwrap();

        assert_eq!(handled_psk_responder.psk_handle, psk_handle);

        let handled_psk_initiator = initiator.complete_handshake(&respone_msg).unwrap();

        assert_eq!(
            handled_psk_initiator.psk_handle,
            handled_psk_responder.psk_handle
        );
        assert_eq!(handled_psk_initiator.psk, handled_psk_responder.psk);
    }
}
