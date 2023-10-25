//! # Key Encapsulation Mechanism
//!
//! A KEM interface.

use rand::{CryptoRng, Rng};

use crate::ecdh;
use crate::ecdh::p256;
use crate::ecdh::p256_derive;
use crate::ecdh::x25519;

pub(crate) mod kyber;

// TODO: These functions are currently exposed simply in order to make NIST KAT
// testing possible without an implementation of the NIST AES-CTR DRBG. Remove them
// (and change the visibility of the exported functions to pub(crate)) the
// moment we have an implementation of one. This is tracked by:
// https://github.com/cryspen/libcrux/issues/36
pub use kyber::kyber1024::decapsulate_1024 as kyber1024_decapsulate_derand;
pub use kyber::kyber1024::encapsulate_1024 as kyber1024_encapsulate_derand;
pub use kyber::kyber1024::generate_key_pair_1024 as kyber1024_generate_keypair_derand;
pub use kyber::kyber512::decapsulate_512 as kyber512_decapsulate_derand;
pub use kyber::kyber512::encapsulate_512 as kyber512_encapsulate_derand;
pub use kyber::kyber512::generate_key_pair_512 as kyber512_generate_keypair_derand;
pub use kyber::kyber768::decapsulate_768 as kyber768_decapsulate_derand;
pub use kyber::kyber768::encapsulate_768 as kyber768_encapsulate_derand;
pub use kyber::kyber768::generate_key_pair_768 as kyber768_generate_keypair_derand;

use self::kyber::{
    kyber1024::{Kyber1024Ciphertext, Kyber1024PrivateKey, Kyber1024PublicKey},
    kyber512::{Kyber512Ciphertext, Kyber512PrivateKey, Kyber512PublicKey},
    kyber768::{Kyber768Ciphertext, Kyber768PrivateKey, Kyber768PublicKey},
    KyberSharedSecret,
};
pub use kyber::{KyberCiphertext, KyberKeyPair};

/// KEM Algorithms
///
/// This includes named elliptic curves or dedicated KEM algorithms like Kyber.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Algorithm {
    X25519,
    X448,
    Secp256r1,
    Secp384r1,
    Secp521r1,
    Kyber512,
    Kyber768,
    Kyber768X25519,
    Kyber1024,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    EcDhError(ecdh::Error),
    KeyGen,
    Encapsulate,
    Decapsulate,
    UnsupportedAlgorithm,
    InvalidPrivateKey,
    InvalidPublicKey,
    InvalidCiphertext,
}

impl TryFrom<Algorithm> for ecdh::Algorithm {
    type Error = &'static str;

    fn try_from(value: Algorithm) -> Result<Self, Self::Error> {
        match value {
            Algorithm::X25519 => Ok(ecdh::Algorithm::X25519),
            Algorithm::X448 => Ok(ecdh::Algorithm::X448),
            Algorithm::Secp256r1 => Ok(ecdh::Algorithm::P256),
            Algorithm::Secp384r1 => Ok(ecdh::Algorithm::P384),
            Algorithm::Secp521r1 => Ok(ecdh::Algorithm::P521),
            Algorithm::Kyber768X25519 => Ok(ecdh::Algorithm::X25519),
            _ => Err("provided algorithm is not an ECDH algorithm"),
        }
    }
}

impl From<ecdh::Error> for Error {
    fn from(value: ecdh::Error) -> Self {
        Error::EcDhError(value)
    }
}

pub struct Kyber768X25519PrivateKey {
    pub kyber: Kyber768PrivateKey,
    pub x25519: x25519::PrivateKey,
}

impl Kyber768X25519PrivateKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            kyber: bytes[32..]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
            x25519: bytes[..32]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.x25519.0.to_vec();
        out.extend_from_slice(self.kyber.as_ref());
        out
    }
}

/// A KEM private key.
pub enum PrivateKey {
    X25519(x25519::PrivateKey),
    P256(p256::PrivateKey),
    Kyber512(Kyber512PrivateKey),
    Kyber768(Kyber768PrivateKey),
    Kyber768X25519(Kyber768X25519PrivateKey),
    Kyber1024(Kyber1024PrivateKey),
}

pub struct Kyber768X25519PublicKey {
    pub kyber: Kyber768PublicKey,
    pub x25519: x25519::PublicKey,
}

impl Kyber768X25519PublicKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            kyber: bytes[32..]
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)?,
            x25519: bytes[0..32]
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.x25519.0.to_vec();
        out.extend_from_slice(self.kyber.as_ref());
        out
    }
}

/// A KEM public key.
pub enum PublicKey {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    Kyber512(Kyber512PublicKey),
    Kyber768(Kyber768PublicKey),
    Kyber768X25519(Kyber768X25519PublicKey),
    Kyber1024(Kyber1024PublicKey),
}

/// A KEM ciphertext
pub enum Ct {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    Kyber512(Kyber512Ciphertext),
    Kyber768(Kyber768Ciphertext),
    Kyber768X25519(Kyber768Ciphertext, x25519::PublicKey),
    Kyber1024(Kyber1024Ciphertext),
}

/// A KEM shared secret
pub enum Ss {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    Kyber512(KyberSharedSecret),
    Kyber768(KyberSharedSecret),
    Kyber768X25519(KyberSharedSecret, x25519::PublicKey),
    Kyber1024(KyberSharedSecret),
}

impl PrivateKey {
    /// Encode a private key.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            PrivateKey::X25519(k) => k.0.to_vec(),
            PrivateKey::P256(k) => k.0.to_vec(),
            PrivateKey::Kyber512(k) => k.as_slice().to_vec(),
            PrivateKey::Kyber768(k) => k.as_slice().to_vec(),
            PrivateKey::Kyber768X25519(k) => k.encode(),
            PrivateKey::Kyber1024(k) => k.as_slice().to_vec(),
        }
    }

    /// Decode a private key.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(|k| Self::X25519(k)),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(|k| Self::P256(k)),
            Algorithm::Kyber512 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(|k| Self::Kyber512(k)),
            Algorithm::Kyber768 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(|k| Self::Kyber768(k)),
            Algorithm::Kyber768X25519 => {
                let key: [u8; kyber::kyber768::SECRET_KEY_SIZE_768 + 32] =
                    bytes.try_into().map_err(|_| Error::InvalidPrivateKey)?;
                let (ksk, xsk) = key.split_at(kyber::kyber768::SECRET_KEY_SIZE_768);
                Ok(Self::Kyber768X25519(Kyber768X25519PrivateKey {
                    kyber: ksk.try_into().map_err(|_| Error::InvalidPrivateKey)?,
                    x25519: xsk.try_into().map_err(|_| Error::InvalidPrivateKey)?,
                }))
            }
            Algorithm::Kyber1024 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(|k| Self::Kyber1024(k)),
            _ => Err(Error::UnsupportedAlgorithm),
        }
    }
}

impl PublicKey {
    /// Encode public key.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            PublicKey::X25519(k) => k.0.to_vec(),
            PublicKey::P256(k) => k.0.to_vec(),
            PublicKey::Kyber512(k) => k.as_ref().to_vec(),
            PublicKey::Kyber768(k) => k.as_ref().to_vec(),
            PublicKey::Kyber768X25519(k) => k.encode(),
            PublicKey::Kyber1024(k) => k.as_ref().to_vec(),
        }
    }

    /// Decode a public key.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)
                .map(|k| Self::X25519(k)),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)
                .map(|k| Self::P256(k)),
            Algorithm::Kyber768 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)
                .map(|k| Self::Kyber768(k)),
            Algorithm::Kyber768X25519 => {
                Kyber768X25519PublicKey::decode(bytes).map(|k| Self::Kyber768X25519(k))
            }
            Algorithm::Kyber1024 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)
                .map(|k| Self::Kyber1024(k)),
            _ => Err(Error::UnsupportedAlgorithm),
        }
    }
}

impl Ss {
    /// Encode a shared secret.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Ss::X25519(k) => k.0.to_vec(),
            Ss::P256(k) => k.0.to_vec(),
            Ss::Kyber512(k) => k.as_ref().to_vec(),
            Ss::Kyber768(k) => k.as_ref().to_vec(),
            Ss::Kyber768X25519(kk, xk) => {
                let mut out = xk.0.to_vec();
                out.extend_from_slice(kk.as_ref());
                out
            }
            Ss::Kyber1024(k) => k.as_ref().to_vec(),
        }
    }
}

impl Ct {
    /// Encode a ciphertext.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Ct::X25519(k) => k.0.to_vec(),
            Ct::P256(k) => k.0.to_vec(),
            Ct::Kyber512(k) => k.as_ref().to_vec(),
            Ct::Kyber768(k) => k.as_ref().to_vec(),
            Ct::Kyber768X25519(kk, xk) => {
                let mut out = xk.0.to_vec();
                out.extend_from_slice(kk.as_ref());
                out
            }
            Ct::Kyber1024(k) => k.as_ref().to_vec(),
        }
    }

    /// Decode a ciphertext.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(|ct| Self::X25519(ct)),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(|ct| Self::P256(ct)),
            Algorithm::Kyber768 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(|ct| Self::Kyber768(ct)),
            Algorithm::Kyber768X25519 => {
                let key: [u8; kyber::kyber768::CPA_PKE_CIPHERTEXT_SIZE_768 + 32] =
                    bytes.try_into().map_err(|_| Error::InvalidCiphertext)?;
                let (kct, xct) = key.split_at(kyber::kyber768::CPA_PKE_CIPHERTEXT_SIZE_768);
                Ok(Self::Kyber768X25519(
                    kct.try_into().map_err(|_| Error::InvalidCiphertext)?,
                    xct.try_into().map_err(|_| Error::InvalidCiphertext)?,
                ))
            }
            Algorithm::Kyber1024 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(|ct| Self::Kyber1024(ct)),
            _ => Err(Error::UnsupportedAlgorithm),
        }
    }
}

/// Compute the public key for a private key of the given [`Algorithm`].
/// Applicable only to X25519 and secp256r1.
pub fn secret_to_public(alg: Algorithm, sk: impl AsRef<[u8]>) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            ecdh::secret_to_public(alg.try_into().unwrap(), sk.as_ref()).map_err(|e| e.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

fn gen_kyber768(
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Kyber768PrivateKey, Kyber768PublicKey), Error> {
    let mut seed = [0; kyber::KEY_GENERATION_SEED_SIZE];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;

    if let Ok(KyberKeyPair { sk, pk }) = kyber768_generate_keypair_derand(seed) {
        Ok((sk, pk))
    } else {
        Err(Error::KeyGen)
    }
}

/// Generate a key pair for the [`Algorithm`] using the provided rng.
///
/// The function returns a fresh key or a [`Error::KeyGen`] error if
/// * not enough entropy was available
/// * it was not possible to generate a valid key within a reasonable amount of iterations.
pub fn key_gen(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(PrivateKey, PublicKey), Error> {
    match alg {
        Algorithm::X25519 => ecdh::x25519_key_gen(rng)
            .map_err(|e| e.into())
            .map(|(private, public)| (PrivateKey::X25519(private), PublicKey::X25519(public))),
        Algorithm::Secp256r1 => ecdh::p256_key_gen(rng)
            .map_err(|e| e.into())
            .map(|(private, public)| (PrivateKey::P256(private), PublicKey::P256(public))),
        Algorithm::Kyber768 => gen_kyber768(rng)
            .map(|(private, public)| (PrivateKey::Kyber768(private), PublicKey::Kyber768(public))),
        Algorithm::Kyber768X25519 => {
            let (kyber_private, kyber_public) = gen_kyber768(rng)?;
            let (x25519_private, x25519_public) = ecdh::x25519_key_gen(rng)?;
            Ok((
                PrivateKey::Kyber768X25519(Kyber768X25519PrivateKey {
                    kyber: kyber_private,
                    x25519: x25519_private,
                }),
                PublicKey::Kyber768X25519(Kyber768X25519PublicKey {
                    kyber: kyber_public,
                    x25519: x25519_public,
                }),
            ))
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Encapsulate a shared secret to the provided `pk` and return the `(Key, Enc)` tuple.
pub fn encapsulate(pk: &PublicKey, rng: &mut (impl CryptoRng + Rng)) -> Result<(Ss, Ct), Error> {
    match pk {
        PublicKey::X25519(pk) => {
            let (new_sk, new_pk) = ecdh::x25519_key_gen(rng)?;
            let gxy = x25519::derive(pk, &new_sk)?;
            Ok((Ss::X25519(gxy), Ct::X25519(new_pk)))
        }
        PublicKey::P256(pk) => {
            let (new_sk, new_pk) = ecdh::p256_key_gen(rng)?;
            let gxy = p256_derive(pk, &new_sk)?;
            Ok((Ss::P256(gxy), Ct::P256(new_pk)))
        }

        PublicKey::Kyber512(pk) => {
            let seed = kyber_rand(rng)?;
            if let Ok((ct, ss)) = kyber::kyber512::encapsulate_512(pk, seed) {
                Ok((Ss::Kyber512(ss), Ct::Kyber512(ct)))
            } else {
                Err(Error::Encapsulate)
            }
        }

        PublicKey::Kyber768(pk) => {
            let seed = kyber_rand(rng)?;
            if let Ok((ct, ss)) = kyber::kyber768::encapsulate_768(pk, seed) {
                Ok((Ss::Kyber768(ss), Ct::Kyber768(ct)))
            } else {
                Err(Error::Encapsulate)
            }
        }

        PublicKey::Kyber768X25519(Kyber768X25519PublicKey {
            kyber: kpk,
            x25519: xpk,
        }) => {
            let seed = kyber_rand(rng)?;
            let (kyber_ct, kyber_ss) =
                kyber::kyber768::encapsulate_768(kpk, seed).map_err(|_| Error::Encapsulate)?;
            let (x_sk, x_pk) = ecdh::x25519_key_gen(rng)?;
            let x_ss = x25519::derive(xpk, &x_sk)?;

            Ok((
                Ss::Kyber768X25519(kyber_ss, x_ss),
                Ct::Kyber768X25519(kyber_ct, x_pk),
            ))
        }

        PublicKey::Kyber1024(pk) => {
            let seed = kyber_rand(rng)?;
            if let Ok((ct, ss)) = kyber::kyber1024::encapsulate_1024(pk, seed) {
                Ok((Ss::Kyber1024(ss), Ct::Kyber1024(ct)))
            } else {
                Err(Error::Encapsulate)
            }
        }
    }
}

fn kyber_rand(
    rng: &mut (impl CryptoRng + Rng),
) -> Result<[u8; kyber::constants::SHARED_SECRET_SIZE], Error> {
    let mut seed = [0; kyber::constants::SHARED_SECRET_SIZE];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;
    Ok(seed)
}

/// Decapsulate the shared secret in `ct` using the private key `sk`.
pub fn decapsulate(ct: &Ct, sk: &PrivateKey) -> Result<Ss, Error> {
    match ct {
        Ct::X25519(ct) => {
            let sk = if let PrivateKey::X25519(k) = sk {
                k
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            x25519::derive(ct, sk)
                .map_err(|e| e.into())
                .map(|k| Ss::X25519(k))
        }
        Ct::P256(ct) => {
            let sk = if let PrivateKey::P256(k) = sk {
                k
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            p256_derive(ct, sk)
                .map_err(|e| e.into())
                .map(|k| Ss::P256(k))
        }
        Ct::Kyber512(ct) => {
            let sk = if let PrivateKey::Kyber512(k) = sk {
                k
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            let ss = kyber::kyber512::decapsulate_512(sk, ct);

            Ok(Ss::Kyber768(ss.into()))
        }
        Ct::Kyber768(ct) => {
            let sk = if let PrivateKey::Kyber768(k) = sk {
                k
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            let ss = kyber::kyber768::decapsulate_768(sk, ct);

            Ok(Ss::Kyber768(ss.into()))
        }
        Ct::Kyber768X25519(kct, xct) => {
            let (ksk, xsk) = if let PrivateKey::Kyber768X25519(Kyber768X25519PrivateKey {
                kyber: kk,
                x25519: xk,
            }) = sk
            {
                (kk, xk)
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            let kss = kyber::kyber768::decapsulate_768(ksk, kct);
            let xss = x25519::derive(xct, xsk)?;

            Ok(Ss::Kyber768X25519(kss.into(), xss))
        }

        Ct::Kyber1024(ct) => {
            let sk = if let PrivateKey::Kyber1024(k) = sk {
                k
            } else {
                return Err(Error::InvalidPrivateKey);
            };
            let ss = kyber::kyber1024::decapsulate_1024(sk, ct);

            Ok(Ss::Kyber1024(ss.into()))
        }
    }
}
