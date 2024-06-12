//! # PQ-PSK establishment protocol
//!
//! This crate implements a post-quantum (PQ) pre-shared key (PSK) establishment
//! protocol.

use chrono::{DateTime, Duration, Utc};
use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use libcrux_hmac::hmac;
use rand::{CryptoRng, Rng};

pub const PSK_EXPIRATION: Duration = Duration::hours(2);
pub const PSK_LENGTH: usize = 32;
pub const K0_LENGTH: usize = 32;
pub const KM_LENGTH: usize = 32;
pub const MAC_LENGTH: usize = 32;

type Psk = [u8; PSK_LENGTH];
type Mac = [u8; MAC_LENGTH];

#[derive(Debug)]
pub enum Error {
    InvalidPublicKey,
    InvalidPrivateKey,
    GenerationError,
    DerivationError,
}

pub enum Algorithm {
    X25519,
    MlKem768,
    ClassicMcEliece,
}

pub enum Ciphertext {
    X25519(libcrux_kem::Ct),
    MlKem768(libcrux_kem::Ct),
    ClassicMcEliece(classic_mceliece_rust::Ciphertext),
}

pub enum PublicKey<'a> {
    X25519(libcrux_kem::PublicKey),
    MlKem768(libcrux_kem::PublicKey),
    ClassicMcEliece(classic_mceliece_rust::PublicKey<'a>),
}

pub enum PrivateKey<'a> {
    X25519(libcrux_kem::PrivateKey),
    MlKem768(libcrux_kem::PrivateKey),
    ClassicMcEliece(classic_mceliece_rust::SecretKey<'a>),
}

pub enum SharedSecret<'a> {
    X25519(libcrux_kem::Ss),
    MlKem768(libcrux_kem::Ss),
    ClassicMcEliece(classic_mceliece_rust::SharedSecret<'a>),
}

impl SharedSecret<'_> {
    fn encode(&self) -> Vec<u8> {
        match self {
            SharedSecret::X25519(ss) => ss.encode(),
            SharedSecret::MlKem768(ss) => ss.encode(),
            SharedSecret::ClassicMcEliece(ss) => ss.as_ref().to_owned(),
        }
    }
}

impl Ciphertext {
    fn encode(&self) -> Vec<u8> {
        match self {
            Ciphertext::X25519(ct) => ct.encode(),
            Ciphertext::MlKem768(ct) => ct.encode(),
            Ciphertext::ClassicMcEliece(ct) => ct.as_ref().to_owned(),
        }
    }
    fn decapsulate(&self, sk: &PrivateKey) -> Result<SharedSecret, Error> {
        match self {
            Ciphertext::X25519(ct) => {
                if let PrivateKey::X25519(sk) = sk {
                    let ss = ct.decapsulate(sk).unwrap();
                    Ok(SharedSecret::X25519(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            Ciphertext::MlKem768(ct) => {
                if let PrivateKey::MlKem768(sk) = sk {
                    let ss = ct.decapsulate(sk).unwrap();
                    Ok(SharedSecret::MlKem768(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            Ciphertext::ClassicMcEliece(ct) => {
                if let PrivateKey::ClassicMcEliece(sk) = sk {
                    let ss = decapsulate_boxed(ct, sk);
                    Ok(SharedSecret::ClassicMcEliece(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
        }
    }
}

impl Into<libcrux_kem::Algorithm> for Algorithm {
    fn into(self) -> libcrux_kem::Algorithm {
        match self {
            Algorithm::X25519 => libcrux_kem::Algorithm::X25519,
            Algorithm::MlKem768 => libcrux_kem::Algorithm::MlKem768,
            Algorithm::ClassicMcEliece => {
                unimplemented!("libcrux does not support Classic McEliece")
            }
        }
    }
}

pub fn generate_key_pair(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(PrivateKey<'static>, PublicKey<'static>), Error> {
    match alg {
        Algorithm::X25519 => {
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng).unwrap();
            Ok((PrivateKey::X25519(sk), PublicKey::X25519(pk)))
        }
        Algorithm::MlKem768 => {
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng).unwrap();
            Ok((PrivateKey::MlKem768(sk), PublicKey::MlKem768(pk)))
        }
        Algorithm::ClassicMcEliece => {
            let (pk, sk) = classic_mceliece_rust::keypair_boxed(rng);
            Ok((
                PrivateKey::ClassicMcEliece(sk),
                PublicKey::ClassicMcEliece(pk),
            ))
        }
    }
}

impl PublicKey<'_> {
    pub(crate) fn encode(&self) -> Vec<u8> {
        match self {
            PublicKey::X25519(k) | PublicKey::MlKem768(k) => k.encode(),
            PublicKey::ClassicMcEliece(k) => k.as_ref().to_vec(),
        }
    }

    pub(crate) fn encapsulate(
        &self,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(SharedSecret, Ciphertext), Error> {
        match self {
            PublicKey::X25519(pk) => {
                let (ss, enc) = pk.encapsulate(rng).unwrap();
                Ok((SharedSecret::X25519(ss), Ciphertext::X25519(enc)))
            }
            PublicKey::MlKem768(pk) => {
                let (ss, enc) = pk.encapsulate(rng).unwrap();
                Ok((SharedSecret::MlKem768(ss), Ciphertext::MlKem768(enc)))
            }
            PublicKey::ClassicMcEliece(pk) => {
                let (enc, ss) = encapsulate_boxed(pk, rng);
                Ok((
                    SharedSecret::ClassicMcEliece(ss),
                    Ciphertext::ClassicMcEliece(enc),
                ))
            }
        }
    }
}

pub struct PskMessage {
    enc: Ciphertext,
    ts: i64,
    mac: Mac,
}

pub fn generate_psk(
    pk: &PublicKey,
    sctx: &[u8],
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Psk, PskMessage), Error> {
    let (ik, enc) = pk.encapsulate(rng).map_err(|_| Error::GenerationError)?;
    let mut info = pk.encode();
    info.extend_from_slice(&enc.encode());
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        ik.encode(),
        info,
        K0_LENGTH,
    )
    .map_err(|_| Error::GenerationError)?;

    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        &k0,
        b"Confirmation",
        KM_LENGTH,
    )
    .map_err(|_| Error::GenerationError)?;

    let psk: Psk = libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, &k0, b"PSK", PSK_LENGTH)
        .map_err(|_| Error::GenerationError)?
        .try_into()
        .expect("should receive the correct number of bytes from HKDF");

    let now = Utc::now();
    let ts = now.timestamp();

    let mac: Mac = hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        &ts.to_be_bytes(),
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    Ok((psk, PskMessage { enc, ts, mac }))
}

pub fn derive_psk(
    pk: &PublicKey,
    sk: &PrivateKey,
    message: &PskMessage,
    sctx: &[u8],
) -> Result<Psk, Error> {
    let PskMessage { enc, ts, mac } = message;

    let received_ts = if let Some(time) = DateTime::from_timestamp(*ts, 0) {
        time
    } else {
        return Err(Error::DerivationError);
    };

    let now = Utc::now();
    if now.signed_duration_since(received_ts) >= PSK_EXPIRATION {
        return Err(Error::DerivationError);
    }

    let ik = enc.decapsulate(sk).map_err(|_| Error::DerivationError)?;

    let mut info = pk.encode();
    info.extend_from_slice(&enc.encode());
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        ik.encode(),
        info,
        K0_LENGTH,
    )
    .map_err(|_| Error::DerivationError)?;

    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        &k0,
        b"Confirmation",
        KM_LENGTH,
    )
    .map_err(|_| Error::DerivationError)?;

    let recomputed_mac: Mac = hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        &ts.to_be_bytes(),
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    if recomputed_mac != *mac {
        return Err(Error::DerivationError);
    }

    let psk: Psk = libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, &k0, b"PSK", PSK_LENGTH)
        .map_err(|_| Error::DerivationError)?
        .try_into()
        .expect("should receive the correct number of bytes from HKDF");

    Ok(psk)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_x25519() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = generate_psk(&pk, sctx, &mut rng).unwrap();

        let psk_responder = derive_psk(&pk, &sk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_mlkem768() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = generate_psk(&pk, sctx, &mut rng).unwrap();

        let psk_responder = derive_psk(&pk, &sk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_classic_mceliece() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::ClassicMcEliece, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = generate_psk(&pk, sctx, &mut rng).unwrap();

        let psk_responder = derive_psk(&pk, &sk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
