//! # PSK Registration Protocol
//!
//! This module implements a protocol for mutual registration of a
//! PQ-PSK between an initiator and a responder.

use libcrux::aead::Algorithm;
use std::time::{Duration, SystemTime};

use rand::{CryptoRng, Rng};

use crate::{
    cred::Credential,
    psq::{self, Ciphertext},
    Error, Psk,
};

const PSK_REGISTRATION_CONTEXT: &[u8] = b"PSK-Registration";
const PSK_LENGTH: usize = 32;

const AEAD_RESPONDER: &[u8] = b"AEAD-Responder-Initiator";
const AEAD_INITIATOR: &[u8] = b"AEAD-Initiator-Responder";
const AEAD_KEY_NONCE: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305)
    + Algorithm::nonce_size(Algorithm::Chacha20Poly1305);

const AEAD_KEY_LENGTH: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305);

struct AeadMac {
    tag: libcrux::aead::Tag,
    ctxt: Vec<u8>,
}

/// The Initiator's message to the responder.
pub struct InitiatorMsg {
    encapsulation: Ciphertext,
    aead_mac: AeadMac,
}

/// The Responder's message to the initiator.
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
    pub fn send_initial_message<C: Credential>(
        sctx: &[u8],
        psk_ttl: Duration,
        pqpk_responder: &psq::PublicKey,
        signing_key: &C::SigningKey,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Self, InitiatorMsg), Error> {
        let (k_pq, enc_pq) = pqpk_responder.gen_pq_psk(sctx, rng)?;
        let (initiator_iv, initiator_key, _receiver_iv, _receiver_key) = derive_cipherstate(&k_pq)?;

        let now = SystemTime::now();
        let ts = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| Error::OsError)?;

        let ts_ttl = serialize_ts_ttl(&ts, &psk_ttl);

        let (signature, verification_key) = C::sign(signing_key, &enc_pq.serialize())?;
        let signature_bytes = C::serialize_signature(&signature);
        let vk_bytes = C::serialize_verification_key(&verification_key);

        let mut message = Vec::new();
        message.extend_from_slice(&ts_ttl);
        message.extend_from_slice(&vk_bytes);
        message.extend_from_slice(&signature_bytes);

        let (tag, ctxt) =
            libcrux::aead::encrypt_detached(&initiator_key, &mut message, initiator_iv, b"")
                .map_err(|_| Error::CryptoError)?;
        let aead_mac = AeadMac {
            tag,
            ctxt: ctxt.to_owned(),
        };

        Ok((
            Self { k_pq },
            InitiatorMsg {
                encapsulation: enc_pq,
                aead_mac,
            },
        ))
    }

    /// Receive the responder's respone and derive a PSK under the
    /// given handle.
    pub fn complete_handshake(
        &self,
        responder_message: &ResponderMsg,
    ) -> Result<RegisteredPsk, Error> {
        let (_initiator_iv, _initiator_key, responder_iv, responder_key) =
            derive_cipherstate(&self.k_pq)?;

        let psk_handle = libcrux::aead::decrypt_detached(
            &responder_key,
            responder_message.aead_mac.ctxt.clone(),
            responder_iv,
            b"",
            &responder_message.aead_mac.tag,
        )
        .map_err(|_| Error::CryptoError)?;

        let psk = derive_psk(&self.k_pq)?;

        Ok(RegisteredPsk { psk, psk_handle })
    }
}

fn serialize_ts_ttl(ts: &Duration, psk_ttl: &Duration) -> [u8; 28] {
    let ts_seconds = ts.as_secs();
    let ts_subsec_millis = ts.subsec_millis();
    let mut ts_ttl = [0u8; 28];
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
    pub fn send<C: Credential>(
        psk_handle: &[u8],
        psk_ttl: Duration,
        sctxt: &[u8],
        pqpk: &psq::PublicKey,
        pqsk: &psq::PrivateKey,
        initiator_message: &InitiatorMsg,
    ) -> Result<(RegisteredPsk, ResponderMsg), Error> {
        let k_pq = pqsk.derive_pq_psk(pqpk, &initiator_message.encapsulation, sctxt)?;
        let (initiator_iv, initiator_key, responder_iv, responder_key) = derive_cipherstate(&k_pq)?;

        let msg_bytes = libcrux::aead::decrypt_detached(
            &initiator_key,
            initiator_message.aead_mac.ctxt.clone(),
            initiator_iv,
            b"",
            &initiator_message.aead_mac.tag,
        )
        .map_err(|_| Error::CryptoError)?;

        let verification_key = C::deserialize_verification_key(&msg_bytes[28..28 + C::VK_LEN])?;
        let signature = C::deserialize_signature(&msg_bytes[28 + C::VK_LEN..])?;

        if C::verify(
            &verification_key,
            &signature,
            &initiator_message.encapsulation.serialize(),
        )
        .is_err()
        {
            return Err(Error::RegistrationError);
        }

        let (ts_seconds, ts_subsec_millis) = deserialize_ts(&msg_bytes)?;

        // validate TTL
        let now = SystemTime::now();
        let ts_since_epoch =
            Duration::from_secs(ts_seconds) + Duration::from_millis((ts_subsec_millis).into());
        let now = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| Error::OsError)?;

        let psk = derive_psk(&k_pq)?;

        let (tag, ctxt) =
            libcrux::aead::encrypt_detached(&responder_key, psk_handle, responder_iv, b"")
                .map_err(|_| Error::CryptoError)?;

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
    )
    .map_err(|_| Error::CryptoError)?
    .try_into()
    .map_err(|_| Error::CryptoError)?;

    Ok(psk)
}

fn derive_cipherstate(
    psk: &[u8; 32],
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
    let (receiver_iv, receiver_key) = derive_key_iv(psk, AEAD_RESPONDER)?;

    Ok((initiator_iv, initiator_key, receiver_iv, receiver_key))
}

fn derive_key_iv(
    psk: &[u8; 32],
    info: &[u8],
) -> Result<(libcrux::aead::Iv, libcrux::aead::Key), Error> {
    let key_iv_bytes =
        libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, psk, info, AEAD_KEY_NONCE)
            .map_err(|_| Error::CryptoError)?;
    let (key_bytes, iv_bytes) = key_iv_bytes.split_at(AEAD_KEY_LENGTH);
    let key = libcrux::aead::Key::from_slice(libcrux::aead::Algorithm::Chacha20Poly1305, key_bytes)
        .map_err(|_| Error::CryptoError)?;
    let iv = libcrux::aead::Iv(iv_bytes.try_into().map_err(|_| Error::CryptoError)?);
    Ok((iv, key))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::cred::NoAuth;

    use super::*;

    #[test]
    fn simple() {
        let mut rng = rand::thread_rng();
        let (receiver_pqsk, receiver_pqpk) =
            crate::psq::generate_key_pair(crate::psq::Algorithm::MlKem768, &mut rng).unwrap();
        let sctx = b"test context";
        let psk_handle = b"test handle";
        let (initiator, initiator_msg) = Initiator::send_initial_message::<NoAuth>(
            sctx,
            Duration::from_secs(3600),
            &receiver_pqpk,
            &(),
            &mut rng,
        )
        .unwrap();

        let (handled_psk_responder, respone_msg) = Responder::send::<NoAuth>(
            psk_handle,
            Duration::from_secs(3600),
            sctx,
            &receiver_pqpk,
            &receiver_pqsk,
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
