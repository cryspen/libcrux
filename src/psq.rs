//! # PQ-PSK Component
//!
//! This module implements a post-quantum (PQ) pre-shared key (PSK) component
//! that can be bound to an outer protocol in a post-quantum pre-shared key
//! establishment protocol.

use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use rand::{CryptoRng, Rng};

use crate::Error;

const K0_LENGTH: usize = 32;
type PrePsk = [u8; K0_LENGTH];

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

pub(crate) enum Ciphertext {
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

pub(crate) enum SharedSecret<'a> {
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
                    let ss = ct.decapsulate(sk)?;
                    Ok(SharedSecret::X25519(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            Ciphertext::MlKem768(ct) => {
                if let PrivateKey::MlKem768(sk) = sk {
                    let ss = ct.decapsulate(sk)?;
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
                    let ss = ct.decapsulate(sk)?;
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
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng)?;
            Ok((PrivateKey::X25519(sk), PublicKey::X25519(pk)))
        }
        Algorithm::MlKem768 => {
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng)?;
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
            let (sk, pk) = libcrux_kem::key_gen(alg.into(), rng)?;
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
                let (ss, enc) = pk.encapsulate(rng)?;
                Ok((SharedSecret::X25519(ss), Ciphertext::X25519(enc)))
            }
            PublicKey::MlKem768(pk) => {
                let (ss, enc) = pk.encapsulate(rng)?;
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
                let (ss, enc) = pk.encapsulate(rng)?;
                Ok((
                    SharedSecret::XWingKemDraft02(ss),
                    Ciphertext::XWingKemDraft02(enc),
                ))
            }
        }
    }

    /// Generate a fresh PSQ component, and a message encapsulating it for the
    /// receiver.
    pub(crate) fn gen_pq_psk(
        &self,
        sctx: &[u8],
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(PrePsk, Ciphertext), Error> {
        let (ik, enc) = self
            .encapsulate(rng)
            .map_err(|_| Error::PSQGenerationError)?;
        let mut info = self.encode();
        info.extend_from_slice(&enc.encode());
        info.extend_from_slice(sctx);

        let k0 = libcrux_hkdf::expand(
            libcrux_hkdf::Algorithm::Sha256,
            ik.encode(),
            info,
            K0_LENGTH,
        )
        .map_err(|_| Error::PSQGenerationError)?;

        Ok((k0.try_into().map_err(|_| Error::CryptoError)?, enc))
    }
}

impl PrivateKey<'_> {
    /// Derive a PSQ component from a PSQ  component message.
    ///
    /// Can error, if the given PSQ message is cryptographically invalid.
    pub(crate) fn derive_pq_psk(
        &self,
        pk: &PublicKey,
        enc: &Ciphertext,
        sctx: &[u8],
    ) -> Result<PrePsk, Error> {
        let ik = enc
            .decapsulate(self)
            .map_err(|_| Error::PSQDerivationError)?;

        let mut info = pk.encode();
        info.extend_from_slice(&enc.encode());
        info.extend_from_slice(sctx);

        let k0 = libcrux_hkdf::expand(
            libcrux_hkdf::Algorithm::Sha256,
            ik.encode(),
            info,
            K0_LENGTH,
        )
        .map_err(|_| Error::PSQDerivationError)?;
        k0.try_into().map_err(|_| Error::CryptoError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_x25519() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk.gen_pq_psk(sctx, &mut rng).unwrap();

        let psk_responder = sk.derive_pq_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_mlkem768() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk.gen_pq_psk(sctx, &mut rng).unwrap();

        let psk_responder = sk.derive_pq_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_xwing() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::XWingKemDraft02, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk.gen_pq_psk(sctx, &mut rng).unwrap();

        let psk_responder = sk.derive_pq_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }

    #[test]
    fn simple_classic_mceliece() {
        let mut rng = rand::thread_rng();
        let (sk, pk) = generate_key_pair(Algorithm::ClassicMcEliece, &mut rng).unwrap();
        let sctx = b"test context";
        let (psk_initiator, message) = pk.gen_pq_psk(sctx, &mut rng).unwrap();

        let psk_responder = sk.derive_pq_psk(&pk, &message, sctx).unwrap();
        assert_eq!(psk_initiator, psk_responder);
    }
}
