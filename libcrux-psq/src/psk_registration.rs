//! # PSK Registration Protocol
//!
//! This module implements a protocol for mutual registration of a
//! PQ-PSK between an initiator and a responder.

use libcrux::aead::{decrypt_detached, encrypt_detached, Algorithm};
use libcrux_kem::Ct;
use libcrux_traits::kem::KEM;
use rand::CryptoRng;
use std::time::{Duration, SystemTime};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::ClassicMcEliece;

use crate::{cred::Authenticator, impls::MlKem768, traits::*, Error, Psk};

const PSK_REGISTRATION_CONTEXT: &[u8] = b"PSK-Registration";
const PSK_LENGTH: usize = 32;

const AEAD_RESPONDER: &[u8] = b"AEAD-Responder-Initiator";
const AEAD_INITIATOR: &[u8] = b"AEAD-Initiator-Responder";
const AEAD_KEY_NONCE: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305)
    + Algorithm::nonce_size(Algorithm::Chacha20Poly1305);

const AEAD_KEY_LENGTH: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305);

const TS_TTL_LEN: usize = 28;

struct AeadMac {
    tag: libcrux::aead::Tag,
    ctxt: Vec<u8>,
}

impl Encode for AeadMac {
    fn encode(&self) -> Vec<u8> {
        let mut out = vec![];

        out.extend_from_slice(self.tag.as_ref());
        out.extend_from_slice(&self.ctxt);

        out
    }
}

impl Decode for AeadMac {
    fn decode(bytes: &[u8]) -> Result<(Self, usize), Error> {
        let tag = libcrux::aead::Tag::from_slice(&bytes[0..16]).map_err(|_| Error::Decoding)?;
        let ctxt = bytes[16..].to_vec();

        let out = Self { tag, ctxt };
        let len = 16 + out.ctxt.len();

        Ok((out, len))
    }
}

/// The Initiator's message to the responder.
pub struct InitiatorMsg<T: KEM> {
    encapsulation: Ciphertext<T>,
    aead_mac: AeadMac,
}

impl<T: KEM<Ciphertext: Encode>> Encode for InitiatorMsg<T> {
    fn encode(&self) -> Vec<u8> {
        let mut out = vec![];

        out.extend_from_slice(&self.encapsulation.encode());
        out.extend_from_slice(&self.aead_mac.encode());

        out
    }
}

#[cfg(feature = "classic-mceliece")]
impl Decode for InitiatorMsg<ClassicMcEliece> {
    fn decode(bytes: &[u8]) -> Result<(Self, usize), Error> {
        let mut ct = [0u8; 188];
        let (ct_bytes, rest) = bytes.split_at(188);
        let (mac_bytes, aead_bytes) = rest.split_at(32);
        ct.copy_from_slice(ct_bytes);
        let ct = classic_mceliece_rust::Ciphertext::from(ct);
        let mut mac = [0u8; MAC_LENGTH];
        mac.copy_from_slice(mac_bytes);

        let (aead_mac, _len) = AeadMac::decode(aead_bytes)?;

        let out = Self {
            encapsulation: Ciphertext::<ClassicMcEliece> {
                inner_ctxt: ct,
                mac,
            },
            aead_mac,
        };

        Ok((out, bytes.len()))
    }
}

impl Decode for InitiatorMsg<MlKem768> {
    fn decode(bytes: &[u8]) -> Result<(Self, usize), Error> {
        let ct = Ct::decode(libcrux_kem::Algorithm::MlKem768, &bytes[0..1088]).unwrap();
        let mut mac = [0u8; MAC_LENGTH];
        mac.copy_from_slice(&bytes[1088..1088 + 32]);

        let (aead_mac, _len) = AeadMac::decode(&bytes[1088 + 32..])?;

        let out = Self {
            encapsulation: Ciphertext::<MlKem768> {
                inner_ctxt: ct,
                mac,
            },
            aead_mac,
        };

        Ok((out, bytes.len()))
    }
}

/// The Responder's message to the initiator.
pub struct ResponderMsg {
    aead_mac: AeadMac,
}

impl Encode for ResponderMsg {
    fn encode(&self) -> Vec<u8> {
        self.aead_mac.encode()
    }
}

impl Decode for ResponderMsg {
    fn decode(bytes: &[u8]) -> Result<(Self, usize), Error> {
        let (aead_mac, read) = AeadMac::decode(bytes)?;
        let out = Self { aead_mac };

        Ok((out, read))
    }
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

        let signature = C::sign(signing_key, &enc_pq.encode())?;

        let mut message = Vec::new();
        message.extend_from_slice(&ts_ttl);
        message.extend_from_slice(signature.as_ref());
        message.extend_from_slice(credential.as_ref());

        let (tag, ctxt) = encrypt_detached(&initiator_key, &mut message, initiator_iv, b"")
            .map_err(|_| Error::CryptoError)?;
        let aead_mac = AeadMac { tag, ctxt };

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

        let psk_handle = decrypt_detached(
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

fn deserialize_sig_cred<C: Authenticator>(
    bytes: &[u8],
) -> Result<(C::Signature, C::Credential), Error> {
    let (sig_bytes, cred_bytes) = bytes.split_at(C::SIG_LEN);
    let signature = C::deserialize_signature(sig_bytes)?;
    let credential = C::deserialize_credential(cred_bytes)?;
    Ok((signature, credential))
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

        let msg_bytes = decrypt_detached(
            &initiator_key,
            initiator_message.aead_mac.ctxt.clone(),
            initiator_iv,
            b"",
            &initiator_message.aead_mac.tag,
        )
        .map_err(|_| Error::CryptoError)?;

        let (ts_bytes, sig_cred_bytes) = msg_bytes.split_at(TS_TTL_LEN);
        let (signature, credential) = deserialize_sig_cred::<C>(sig_cred_bytes)?;
        let verification_key = C::validate_credential(credential, client_certificate)?;
        if C::verify(
            &verification_key,
            &signature,
            &initiator_message.encapsulation.encode(),
        )
        .is_err()
        {
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

        let (tag, ctxt) = encrypt_detached(&responder_key, psk_handle, responder_iv, b"")
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
            pk.as_ref(),
            &mut rng,
        )
        .unwrap();

        let (handled_psk_responder, respone_msg) = Responder::send::<Ed25519, MlKem768>(
            psk_handle,
            Duration::from_secs(3600),
            sctx,
            &receiver_pqpk,
            &receiver_pqsk,
            pk.as_ref(),
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
