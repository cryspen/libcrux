//! # PQ-PSK Component
//!
//! This module implements a post-quantum (PQ) pre-shared key (PSK) component
//! that can be bound to an outer protocol in a post-quantum pre-shared key
//! establishment protocol.

use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use rand::{CryptoRng, Rng};

use crate::Error;

const K0_LENGTH: usize = 32;
const KM_LENGTH: usize = 32;

const CONFIRMATION_CONTEXT: &[u8] = b"Confirmation";
const PSK_CONTEXT: &[u8] = b"PSK";
const MAC_INPUT: &[u8] = b"MAC-Input";

const PRE_PSK_LENGTH: usize = 32;
type PrePsk = [u8; PRE_PSK_LENGTH];

const MAC_LENGTH: usize = 32;
type Mac = [u8; MAC_LENGTH];

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

pub(crate) enum InnerCiphertext {
    X25519(libcrux_kem::Ct),
    MlKem768(libcrux_kem::Ct),
    XWingKemDraft02(libcrux_kem::Ct),
    ClassicMcEliece(classic_mceliece_rust::Ciphertext),
}

/// A PSQ ciphertext, including MAC.
pub struct Ciphertext {
    inner_ctxt: InnerCiphertext,
    mac: Mac,
}

impl Ciphertext {
    pub(crate) fn serialize(&self) -> Vec<u8> {
        let mut serialized = self.inner_ctxt.encode();
        serialized.extend_from_slice(&self.mac);
        serialized
    }
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

impl InnerCiphertext {
    fn encode(&self) -> Vec<u8> {
        match self {
            InnerCiphertext::X25519(ct) => ct.encode(),
            InnerCiphertext::MlKem768(ct) => ct.encode(),
            InnerCiphertext::ClassicMcEliece(ct) => ct.as_ref().to_owned(),
            InnerCiphertext::XWingKemDraft02(ct) => ct.encode(),
        }
    }

    fn decapsulate(&self, sk: &PrivateKey) -> Result<SharedSecret, Error> {
        match self {
            InnerCiphertext::X25519(ct) => {
                if let PrivateKey::X25519(sk) = sk {
                    let ss = ct.decapsulate(sk)?;
                    Ok(SharedSecret::X25519(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            InnerCiphertext::MlKem768(ct) => {
                if let PrivateKey::MlKem768(sk) = sk {
                    let ss = ct.decapsulate(sk)?;
                    Ok(SharedSecret::MlKem768(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            InnerCiphertext::ClassicMcEliece(ct) => {
                if let PrivateKey::ClassicMcEliece(sk) = sk {
                    let ss = decapsulate_boxed(ct, sk);
                    Ok(SharedSecret::ClassicMcEliece(ss))
                } else {
                    Err(Error::InvalidPrivateKey)
                }
            }
            InnerCiphertext::XWingKemDraft02(ct) => {
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
    ) -> Result<(SharedSecret, InnerCiphertext), Error> {
        match self {
            PublicKey::X25519(pk) => {
                let (ss, enc) = pk.encapsulate(rng)?;
                Ok((SharedSecret::X25519(ss), InnerCiphertext::X25519(enc)))
            }
            PublicKey::MlKem768(pk) => {
                let (ss, enc) = pk.encapsulate(rng)?;
                Ok((SharedSecret::MlKem768(ss), InnerCiphertext::MlKem768(enc)))
            }
            PublicKey::ClassicMcEliece(pk) => {
                let (enc, ss) = encapsulate_boxed(pk, rng);
                Ok((
                    SharedSecret::ClassicMcEliece(ss),
                    InnerCiphertext::ClassicMcEliece(enc),
                ))
            }
            PublicKey::XWingKemDraft02(pk) => {
                let (ss, enc) = pk.encapsulate(rng)?;
                Ok((
                    SharedSecret::XWingKemDraft02(ss),
                    InnerCiphertext::XWingKemDraft02(enc),
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
        let (ikm, enc) = self
            .encapsulate(rng)
            .map_err(|_| Error::PSQGenerationError)?;

        let k0 = compute_k0(self, &ikm, &enc, sctx)?;
        let mac = compute_mac(&k0)?;
        let psk = compute_psk(&k0)?;

        Ok((
            psk,
            Ciphertext {
                inner_ctxt: enc,
                mac,
            },
        ))
    }
}

fn compute_psk(k0: &[u8]) -> Result<PrePsk, Error> {
    let psk: PrePsk = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        k0,
        PSK_CONTEXT,
        PRE_PSK_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");
    Ok(psk)
}

fn compute_k0(
    pqpk: &PublicKey,
    ikm: &SharedSecret,
    enc: &InnerCiphertext,
    sctx: &[u8],
) -> Result<Vec<u8>, Error> {
    let mut info = pqpk.encode();
    info.extend_from_slice(&enc.encode());
    info.extend_from_slice(sctx);

    let k0 = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        ikm.encode(),
        info,
        K0_LENGTH,
    )
    .map_err(|_| Error::PSQDerivationError)?;

    Ok(k0)
}

fn compute_mac(k0: &[u8]) -> Result<Mac, Error> {
    let km = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        k0,
        CONFIRMATION_CONTEXT,
        KM_LENGTH,
    )
    .map_err(|_| Error::PSQGenerationError)?;

    let mac: Mac = libcrux_hmac::hmac(
        libcrux_hmac::Algorithm::Sha256,
        &km,
        MAC_INPUT,
        Some(MAC_LENGTH),
    )
    .try_into()
    .expect("should receive the correct number of bytes from HMAC");

    Ok(mac)
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
        let Ciphertext { inner_ctxt, mac } = enc;
        let ik = inner_ctxt
            .decapsulate(self)
            .map_err(|_| Error::PSQDerivationError)?;

        let k0 = compute_k0(pk, &ik, inner_ctxt, sctx)?;
        let recomputed_mac = compute_mac(&k0)?;

        if compare(&recomputed_mac, mac) == 0 {
            let psk = compute_psk(&k0)?;
            Ok(psk)
        } else {
            Err(Error::PSQDerivationError)
        }
    }
}

/// Return 1 if `value` is not zero and 0 otherwise.
fn inz(value: u8) -> u8 {
    let value = value as u16;
    let result = ((value | (!value).wrapping_add(1)) >> 8) & 1;
    result as u8
}

#[inline(never)] // Don't inline this to avoid that the compiler optimizes this out.
fn is_non_zero(value: u8) -> u8 {
    core::hint::black_box(inz(value))
}

/// Best-effort constant time comparison.
fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;
    for i in 0..lhs.len() {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
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
