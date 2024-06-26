//! # PQ-PSK establishment protocol
//!
//! This crate implements a post-quantum (PQ) pre-shared key (PSK) establishment
//! protocol.

#![deny(missing_docs)]
use std::time::{Duration, SystemTime};

use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use libcrux_hmac::hmac;
use rand::{CryptoRng, Rng};

const PSK_LENGTH: usize = 32;
const K0_LENGTH: usize = 32;
const KM_LENGTH: usize = 32;
const MAC_LENGTH: usize = 32;

const CONFIRMATION_CONTEXT: &[u8] = b"Confirmation";
const PSK_CONTEXT: &[u8] = b"PSK";

type Psk = [u8; PSK_LENGTH];
type Mac = [u8; MAC_LENGTH];

#[derive(Debug)]
/// PSQ Errors.
pub enum Error {
    /// An invalid public key was provided
    InvalidPublicKey,
    /// An invalid private key was provided
    InvalidPrivateKey,
    /// An error during PSK encapsulation
    GenerationError,
    /// An error during PSK decapsulation
    DerivationError,
}

/// The algorithm that should be used for the internal KEM.
pub enum Algorithm {
    /// An elliptic-curve Diffie-Hellman based KEM (Does not provide post-quantum security)
    X25519,
    /// ML-KEM 768, a lattice-based post-quantum KEM, as specified in FIPS 203 (Draft)
    MlKem768,
    /// A code-based post-quantum KEM & Round 4 candidate in the NIST PQ competition (Parameter Set `mceliece460896f`)
    ClassicMcEliece,
    /// A hybrid post-quantum KEM combining X25519 and ML-KEM 768
    XWingKemDraft02,
}

enum Ciphertext {
    X25519(libcrux_kem::Ct),
    MlKem768(libcrux_kem::Ct),
    XWingKemDraft02(libcrux_kem::Ct),
    ClassicMcEliece(classic_mceliece_rust::Ciphertext),
}

/// A PSQ public key
pub enum PublicKey<'a> {
    ///  for use with X25519-based protocol
    X25519(libcrux_kem::PublicKey),
    /// for use with ML-KEM-768-based protocol
    MlKem768(libcrux_kem::PublicKey),
    /// for use with hybrid KEM XWingDraft02-based protocol
    XWingKemDraft02(libcrux_kem::PublicKey),
    /// for use with Classic McEliece-based protocol
    ClassicMcEliece(classic_mceliece_rust::PublicKey<'a>),
}

/// A PSQ private key
pub enum PrivateKey<'a> {
    ///  for use with X25519-based protocol
    X25519(libcrux_kem::PrivateKey),
    /// for use with ML-KEM-768-based protocol
    MlKem768(libcrux_kem::PrivateKey),
    /// for use with hybrid KEM XWingDraft02-based protocol
    XWingKemDraft02(libcrux_kem::PrivateKey),
    /// for use with Classic McEliece-based protocol
    ClassicMcEliece(classic_mceliece_rust::SecretKey<'a>),
}

enum SharedSecret<'a> {
    X25519(libcrux_kem::Ss),
    MlKem768(libcrux_kem::Ss),
    XWingKemDraft02(libcrux_kem::Ss),
    ClassicMcEliece(classic_mceliece_rust::SharedSecret<'a>),
}

impl SharedSecret<'_> {
    fn encode(&self) -> Vec<u8> {
        match self {
            SharedSecret::X25519(ss) => ss.encode(),
            SharedSecret::MlKem768(ss) => ss.encode(),
            SharedSecret::ClassicMcEliece(ss) => ss.as_ref().to_owned(),
            SharedSecret::XWingKemDraft02(ss) => ss.encode(),
        }
    }
}

impl Ciphertext {
    fn encode(&self) -> Vec<u8> {
        match self {
            Ciphertext::X25519(ct) => ct.encode(),
            Ciphertext::MlKem768(ct) => ct.encode(),
            Ciphertext::ClassicMcEliece(ct) => ct.as_ref().to_owned(),
            Ciphertext::XWingKemDraft02(ct) => ct.encode(),
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
            Ciphertext::XWingKemDraft02(ct) => {
                if let PrivateKey::XWingKemDraft02(sk) = sk {
                    let ss = ct.decapsulate(sk).unwrap();
                    Ok(SharedSecret::XWingKemDraft02(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
        }
    }
}

impl From<Algorithm> for libcrux_kem::Algorithm {
    fn from(val: Algorithm) -> Self {
        match val {
            Algorithm::X25519 => libcrux_kem::Algorithm::X25519,
            Algorithm::MlKem768 => libcrux_kem::Algorithm::MlKem768,
            Algorithm::ClassicMcEliece => {
                unimplemented!("libcrux does not support Classic McEliece")
            }
            Algorithm::XWingKemDraft02 => libcrux_kem::Algorithm::XWingKemDraft02,
        }
    }
}

/// Generate a PSQ key pair.
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
        Algorithm::XWingKemDraft02 => {
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng).unwrap();
            Ok((
                PrivateKey::XWingKemDraft02(sk),
                PublicKey::XWingKemDraft02(pk),
            ))
        }
    }
}

impl PublicKey<'_> {
    /// Return the size (in bytes) of the PSQ public key.
    pub fn size(&self) -> usize {
        self.encode().len()
    }
    pub(crate) fn encode(&self) -> Vec<u8> {
        match self {
            PublicKey::X25519(k) => k.encode(),
            PublicKey::MlKem768(k) => k.encode(),
            PublicKey::XWingKemDraft02(k) => k.encode(),
            PublicKey::ClassicMcEliece(k) => k.as_ref().to_vec(),
        }
    }

    /// Use the underlying KEM to encapsulate a shared secret towards the receiver.
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
            PublicKey::XWingKemDraft02(pk) => {
                let (ss, enc) = pk.encapsulate(rng).unwrap();
                Ok((
                    SharedSecret::XWingKemDraft02(ss),
                    Ciphertext::XWingKemDraft02(enc),
                ))
            }
        }
    }

    /// Generate a fresh PSK, and a message encapsulating it for the
    /// receiver.
    ///
    /// The encapsulated PSK is valid for the given duration
    /// `psk_ttl`, based on milliseconds since the UNIX epoch until
    /// current system time. Parameter `sctx` is used to
    /// cryptographically bind the generated PSK to a given outer
    /// protocol context and may be considered public.
    pub fn send_psk(
        &self,
        sctx: &[u8],
        psk_ttl: Duration,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Psk, PskMessage), Error> {
        let (ik, enc) = self.encapsulate(rng).map_err(|_| Error::GenerationError)?;
        let mut info = self.encode();
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
            CONFIRMATION_CONTEXT,
            KM_LENGTH,
        )
        .map_err(|_| Error::GenerationError)?;

        let psk: Psk = libcrux_hkdf::expand(
            libcrux_hkdf::Algorithm::Sha256,
            &k0,
            PSK_CONTEXT,
            PSK_LENGTH,
        )
        .map_err(|_| Error::GenerationError)?
        .try_into()
        .expect("should receive the correct number of bytes from HKDF");

        let now = SystemTime::now();
        let ts = now.duration_since(SystemTime::UNIX_EPOCH).unwrap();
        let ts_seconds = ts.as_secs();
        let ts_subsec_millis = ts.subsec_millis();
        let mut mac_input = ts_seconds.to_be_bytes().to_vec();
        mac_input.extend_from_slice(&ts_subsec_millis.to_be_bytes());
        mac_input.extend_from_slice(&psk_ttl.as_millis().to_be_bytes());

        let mac: Mac = hmac(
            libcrux_hmac::Algorithm::Sha256,
            &km,
            &mac_input,
            Some(MAC_LENGTH),
        )
        .try_into()
        .expect("should receive the correct number of bytes from HMAC");

        Ok((
            psk,
            PskMessage {
                enc,
                ts: (ts_seconds, ts_subsec_millis),
                psk_ttl,
                mac,
            },
        ))
    }
}

impl PrivateKey<'_> {
    /// Derive a PSK from a PSQ message.
    ///
    /// Can error, if the given PSQ message is invalid, i.e. beyond
    /// its TTL or cryptographically invalid.
    pub fn receive_psk(
        &self,
        pk: &PublicKey,
        message: &PskMessage,
        sctx: &[u8],
    ) -> Result<Psk, Error> {
        let PskMessage {
            enc,
            ts: (ts_seconds, ts_subsec_millis),
            psk_ttl,
            mac,
        } = message;

        let now = SystemTime::now();
        let ts_since_epoch =
            Duration::from_secs(*ts_seconds) + Duration::from_millis((*ts_subsec_millis).into());
        if now.duration_since(SystemTime::UNIX_EPOCH).unwrap() - ts_since_epoch >= *psk_ttl {
            Err(Error::DerivationError)
        } else {
            let ik = enc.decapsulate(self).map_err(|_| Error::DerivationError)?;

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
                CONFIRMATION_CONTEXT,
                KM_LENGTH,
            )
            .map_err(|_| Error::DerivationError)?;

            let mut mac_input = ts_seconds.to_be_bytes().to_vec();
            mac_input.extend_from_slice(&ts_subsec_millis.to_be_bytes());
            mac_input.extend_from_slice(&psk_ttl.as_millis().to_be_bytes());

            let recomputed_mac: Mac = hmac(
                libcrux_hmac::Algorithm::Sha256,
                &km,
                &mac_input,
                Some(MAC_LENGTH),
            )
            .try_into()
            .expect("should receive the correct number of bytes from HMAC");

            if recomputed_mac != *mac {
                Err(Error::DerivationError)
            } else {
                let psk: Psk = libcrux_hkdf::expand(
                    libcrux_hkdf::Algorithm::Sha256,
                    &k0,
                    PSK_CONTEXT,
                    PSK_LENGTH,
                )
                .map_err(|_| Error::DerivationError)?
                .try_into()
                .expect("should receive the correct number of bytes from HKDF");

                Ok(psk)
            }
        }
    }
}

/// A message that encapsulates as post-quantum PSK of a certain
/// lifetime, tied to a specific outer protocol context.
pub struct PskMessage {
    enc: Ciphertext,
    ts: (u64, u32),
    psk_ttl: Duration,
    mac: Mac,
}

impl PskMessage {
    /// Returns the size (in bytes) of the ciphertext enclosed in the message.
    pub fn ct_size(&self) -> usize {
        self.enc.encode().len()
    }
    /// Returns the total size (in bytes) of the message.
    pub fn size(&self) -> usize {
        self.ct_size()
            + MAC_LENGTH // self.mac.len()
            + 8 // self.ts.to_be_bytes().len()
            + 8 // self.psk_ttl.num_milliseconds().to_be_bytes().len()
    }
}

#[cfg(test)]
mod tests {
    use std::thread::sleep;

    use super::*;

    #[test]
    fn simple_x25519() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk
            .send_psk(sctx, Duration::from_secs(2 * 3600), &mut rng)
            .unwrap();

        let psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    #[should_panic]
    fn zero_ttl() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
        let sctx = b"test context";
        let (_psk_initiator, message) =
            pk.send_psk(sctx, Duration::from_secs(0), &mut rng).unwrap();

        let _psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
    }

    #[test]
    #[should_panic]
    fn expired_timestamp() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
        let sctx = b"test context";
        let (_psk_initiator, message) =
            pk.send_psk(sctx, Duration::from_secs(1), &mut rng).unwrap();

        sleep(Duration::from_secs(2));

        let _psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
    }

    #[test]
    fn simple_mlkem768() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk
            .send_psk(sctx, Duration::from_secs(2 * 3600), &mut rng)
            .unwrap();

        let psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_xwing() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::XWingKemDraft02, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk
            .send_psk(sctx, Duration::from_secs(2 * 3600), &mut rng)
            .unwrap();

        let psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_classic_mceliece() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::ClassicMcEliece, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk
            .send_psk(sctx, Duration::from_secs(2 * 3600), &mut rng)
            .unwrap();

        let psk_responder = sk.receive_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
