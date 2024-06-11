//! # Key Encapsulation Mechanism
//!
//! A KEM interface.
//!
//! For ECDH structs, check the [`libcrux::ecdh`] module.
//!
//! Available algorithms:
//! * [`Algorithm::X25519`]\: x25519 ECDH KEM. Also see [`libcrux::ecdh#x25519`].
//! * [`Algorithm::Secp256r1`]\: NIST P256 ECDH KEM. Also see [`libcrux::ecdh#P256`].
//! * [`Algorithm::MlKem512`]\: ML-KEM 512 from [FIPS 203].
//! * [`Algorithm::MlKem768`]\: ML-KEM 768 from [FIPS 203].
//! * [`Algorithm::MlKem1024`]\: ML-KEM 1024 from [FIPS 203].
//! * [`Algorithm::X25519MlKem768Draft00`]\: Hybrid x25519 - ML-KEM 768 [draft kem for hpke](https://www.ietf.org/archive/id/draft-westerbaan-cfrg-hpke-xyber768d00-00.html).
//! * [`Algorithm::XWingKemDraft02`]\: Hybrid x25519 - ML-KEM 768 [draft xwing kem for hpke](https://www.ietf.org/archive/id/draft-connolly-cfrg-xwing-kem-02.html).
//!
//! ```
//! use libcrux::{drbg::Drbg, digest::Algorithm::Sha256};
//! use libcrux_kem::*;
//!
//! let mut rng = Drbg::new(Sha256).unwrap();
//! let (sk_a, pk_a) = key_gen(Algorithm::MlKem768, &mut rng).unwrap();
//! let received_pk = pk_a.encode();
//!
//! let pk = PublicKey::decode(Algorithm::MlKem768, &received_pk).unwrap();
//! let (ss_b, ct_b) = pk.encapsulate(&mut rng).unwrap();
//! let received_ct = ct_b.encode();
//!
//! let ct_a = Ct::decode(Algorithm::MlKem768, &received_ct).unwrap();
//! let ss_a = ct_a.decapsulate(&sk_a).unwrap();
//! assert_eq!(ss_b.encode(), ss_a.encode());
//! ```
//!
//! [FIPS 203]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.ipd.pdf

use rand::{CryptoRng, Rng};

// use crate::{
//     ecdh::{self, p256, p256_derive, x25519},
//     hacl::sha3,
// };
use libcrux::ecdh::p256_derive;
use libcrux::ecdh::{self, p256, x25519};
use libcrux_sha3 as sha3;

use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768};

// TODO: These functions are currently exposed simply in order to make NIST KAT
// testing possible without an implementation of the NIST AES-CTR DRBG. Remove them
// (and change the visibility of the exported functions to pub(crate)) the
// moment we have an implementation of one. This is tracked by:
// https://github.com/cryspen/libcrux/issues/36
#[cfg(feature = "tests")]
pub mod deterministic {
    pub use libcrux_ml_kem::mlkem1024::decapsulate as mlkem1024_decapsulate_derand;
    pub use libcrux_ml_kem::mlkem1024::encapsulate as mlkem1024_encapsulate_derand;
    pub use libcrux_ml_kem::mlkem1024::generate_key_pair as mlkem1024_generate_keypair_derand;
    pub use libcrux_ml_kem::mlkem512::decapsulate as mlkem512_decapsulate_derand;
    pub use libcrux_ml_kem::mlkem512::encapsulate as mlkem512_encapsulate_derand;
    pub use libcrux_ml_kem::mlkem512::generate_key_pair as mlkem512_generate_keypair_derand;
    pub use libcrux_ml_kem::mlkem768::decapsulate as mlkem768_decapsulate_derand;
    pub use libcrux_ml_kem::mlkem768::encapsulate as mlkem768_encapsulate_derand;
    pub use libcrux_ml_kem::mlkem768::generate_key_pair as mlkem768_generate_keypair_derand;
}

use libcrux_ml_kem::MlKemSharedSecret;
pub use libcrux_ml_kem::{
    mlkem1024::{MlKem1024Ciphertext, MlKem1024PrivateKey, MlKem1024PublicKey},
    mlkem512::{MlKem512Ciphertext, MlKem512PrivateKey, MlKem512PublicKey},
    mlkem768::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey},
    MlKemCiphertext, MlKemKeyPair,
};

#[cfg(feature = "tests")]
pub use libcrux_ml_kem::{
    mlkem1024::validate_public_key as ml_kem1024_validate_public_key,
    mlkem512::validate_public_key as ml_kem512_validate_public_key,
    mlkem768::validate_public_key as ml_kem768_validate_public_key,
};

/// KEM Algorithms
///
/// This includes named elliptic curves or dedicated KEM algorithms like ML-KEM.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Algorithm {
    X25519,
    X448,
    Secp256r1,
    Secp384r1,
    Secp521r1,
    MlKem512,
    MlKem768,
    X25519MlKem768Draft00,
    XWingKemDraft02,
    MlKem1024,
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
            Algorithm::X25519MlKem768Draft00 => Ok(ecdh::Algorithm::X25519),
            Algorithm::XWingKemDraft02 => Ok(ecdh::Algorithm::X25519),
            _ => Err("provided algorithm is not an ECDH algorithm"),
        }
    }
}

impl From<ecdh::Error> for Error {
    fn from(value: ecdh::Error) -> Self {
        Error::EcDhError(value)
    }
}

/// An ML-KEM768-x25519 private key.
pub struct X25519MlKem768Draft00PrivateKey {
    pub mlkem: MlKem768PrivateKey,
    pub x25519: x25519::PrivateKey,
}

impl X25519MlKem768Draft00PrivateKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            mlkem: bytes[32..]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
            x25519: bytes[..32]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.x25519.0.to_vec();
        out.extend_from_slice(self.mlkem.as_ref());
        out
    }
}

/// An X-Wing private key.
pub struct XWingKemDraft02PrivateKey {
    pub sk_m: MlKem768PrivateKey,
    pub sk_x: x25519::PrivateKey,
    pub pk_x: x25519::PublicKey,
}

impl XWingKemDraft02PrivateKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            sk_m: bytes[..2400]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
            sk_x: bytes[2400..2432]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
            pk_x: bytes[2432..2464]
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.sk_m.as_ref().to_vec();
        out.extend_from_slice(self.sk_x.0.to_vec().as_ref());
        out.extend_from_slice(self.pk_x.0.to_vec().as_ref());
        out
    }
}

/// A KEM private key.
pub enum PrivateKey {
    X25519(x25519::PrivateKey),
    P256(p256::PrivateKey),
    MlKem512(MlKem512PrivateKey),
    MlKem768(MlKem768PrivateKey),
    X25519MlKem768Draft00(X25519MlKem768Draft00PrivateKey),
    XWingKemDraft02(XWingKemDraft02PrivateKey),
    MlKem1024(MlKem1024PrivateKey),
}

/// An ML-KEM768-x25519 public key.
pub struct X25519MlKem768Draft00PublicKey {
    pub mlkem: MlKem768PublicKey,
    pub x25519: x25519::PublicKey,
}

impl X25519MlKem768Draft00PublicKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            mlkem: MlKem768PublicKey::try_from(&bytes[32..])
                .ok()
                .and_then(mlkem768::validate_public_key)
                .ok_or(Error::InvalidPublicKey)?,
            x25519: bytes[0..32]
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.x25519.0.to_vec();
        out.extend_from_slice(self.mlkem.as_ref());
        out
    }
}

/// An X-Wing public key.
pub struct XWingKemDraft02PublicKey {
    pub pk_m: MlKem768PublicKey,
    pub pk_x: x25519::PublicKey,
}

impl XWingKemDraft02PublicKey {
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            pk_m: MlKem768PublicKey::try_from(&bytes[0..1184])
                .ok()
                .and_then(mlkem768::validate_public_key)
                .ok_or(Error::InvalidPublicKey)?,
            pk_x: bytes[1184..]
                .try_into()
                .map_err(|_| Error::InvalidPublicKey)?,
        })
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.pk_m.as_ref().to_vec();
        out.extend_from_slice(self.pk_x.0.to_vec().as_ref());
        out
    }
}

/// A KEM public key.
pub enum PublicKey {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    MlKem512(MlKem512PublicKey),
    MlKem768(MlKem768PublicKey),
    X25519MlKem768Draft00(X25519MlKem768Draft00PublicKey),
    XWingKemDraft02(XWingKemDraft02PublicKey),
    MlKem1024(MlKem1024PublicKey),
}

/// A KEM ciphertext
pub enum Ct {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    MlKem512(MlKem512Ciphertext),
    MlKem768(MlKem768Ciphertext),
    X25519MlKem768Draft00(MlKem768Ciphertext, x25519::PublicKey),
    XWingKemDraft02(MlKem768Ciphertext, x25519::PublicKey),
    MlKem1024(MlKem1024Ciphertext),
}

impl Ct {
    /// Decapsulate the shared secret in `ct` using the private key `sk`.
    pub fn decapsulate(&self, sk: &PrivateKey) -> Result<Ss, Error> {
        match self {
            Ct::X25519(ct) => {
                let sk = if let PrivateKey::X25519(k) = sk {
                    k
                } else {
                    return Err(Error::InvalidPrivateKey);
                };
                x25519::derive(ct, sk).map_err(|e| e.into()).map(Ss::X25519)
            }
            Ct::P256(ct) => {
                let sk = if let PrivateKey::P256(k) = sk {
                    k
                } else {
                    return Err(Error::InvalidPrivateKey);
                };
                p256_derive(ct, sk).map_err(|e| e.into()).map(Ss::P256)
            }
            Ct::MlKem512(ct) => {
                let sk = if let PrivateKey::MlKem512(k) = sk {
                    k
                } else {
                    return Err(Error::InvalidPrivateKey);
                };
                let ss = libcrux_ml_kem::mlkem512::decapsulate(sk, ct);

                Ok(Ss::MlKem768(ss))
            }
            Ct::MlKem768(ct) => {
                let sk = if let PrivateKey::MlKem768(k) = sk {
                    k
                } else {
                    return Err(Error::InvalidPrivateKey);
                };
                let ss = mlkem768::decapsulate(sk, ct);

                Ok(Ss::MlKem768(ss))
            }
            Ct::X25519MlKem768Draft00(kct, xct) => {
                let (ksk, xsk) =
                    if let PrivateKey::X25519MlKem768Draft00(X25519MlKem768Draft00PrivateKey {
                        mlkem: kk,
                        x25519: xk,
                    }) = sk
                    {
                        (kk, xk)
                    } else {
                        return Err(Error::InvalidPrivateKey);
                    };
                let kss = mlkem768::decapsulate(ksk, kct);
                let xss = x25519::derive(xct, xsk)?;

                Ok(Ss::X25519MlKem768Draft00(kss, xss))
            }
            Ct::XWingKemDraft02(ct_m, ct_x) => {
                let (sk_m, sk_x, pk_x) =
                    if let PrivateKey::XWingKemDraft02(XWingKemDraft02PrivateKey {
                        sk_m,
                        sk_x,
                        pk_x,
                    }) = sk
                    {
                        (sk_m, sk_x, pk_x)
                    } else {
                        return Err(Error::InvalidPrivateKey);
                    };
                let ss_m = mlkem768::decapsulate(sk_m, ct_m);
                let ss_x = x25519::derive(ct_x, sk_x)?;

                Ok(Ss::XWingKemDraft02(
                    ss_m,
                    ss_x,
                    x25519::PublicKey(ct_x.0.clone()),
                    x25519::PublicKey(pk_x.0.clone()),
                ))
            }
            Ct::MlKem1024(ct) => {
                let sk = if let PrivateKey::MlKem1024(k) = sk {
                    k
                } else {
                    return Err(Error::InvalidPrivateKey);
                };
                let ss = libcrux_ml_kem::mlkem1024::decapsulate(sk, ct);

                Ok(Ss::MlKem1024(ss))
            }
        }
    }
}

/// A KEM shared secret
pub enum Ss {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    MlKem512(MlKemSharedSecret),
    MlKem768(MlKemSharedSecret),
    X25519MlKem768Draft00(MlKemSharedSecret, x25519::PublicKey),
    XWingKemDraft02(
        MlKemSharedSecret, // ss_M
        x25519::PublicKey, // ss_X
        x25519::PublicKey, // ct_X
        x25519::PublicKey, // pk_X
    ),
    MlKem1024(MlKemSharedSecret),
}

impl PrivateKey {
    /// Encode a private key.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            PrivateKey::X25519(k) => k.0.to_vec(),
            PrivateKey::P256(k) => k.0.to_vec(),
            PrivateKey::MlKem512(k) => k.as_slice().to_vec(),
            PrivateKey::MlKem768(k) => k.as_slice().to_vec(),
            PrivateKey::X25519MlKem768Draft00(k) => k.encode(),
            PrivateKey::XWingKemDraft02(k) => k.encode(),
            PrivateKey::MlKem1024(k) => k.as_slice().to_vec(),
        }
    }

    /// Decode a private key.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(Self::X25519),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(Self::P256),
            Algorithm::MlKem512 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(Self::MlKem512),
            Algorithm::MlKem768 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(Self::MlKem768),
            Algorithm::X25519MlKem768Draft00 => {
                let key: [u8; MlKem768PrivateKey::len() + 32] =
                    bytes.try_into().map_err(|_| Error::InvalidPrivateKey)?;
                let (ksk, xsk) = key.split_at(MlKem768PrivateKey::len());
                Ok(Self::X25519MlKem768Draft00(
                    X25519MlKem768Draft00PrivateKey {
                        mlkem: ksk.try_into().map_err(|_| Error::InvalidPrivateKey)?,
                        x25519: xsk.try_into().map_err(|_| Error::InvalidPrivateKey)?,
                    },
                ))
            }
            Algorithm::XWingKemDraft02 => {
                let pk = XWingKemDraft02PrivateKey::decode(bytes)
                    .map_err(|_| Error::InvalidPrivateKey)?;
                Ok(Self::XWingKemDraft02(pk))
            }
            Algorithm::MlKem1024 => bytes
                .try_into()
                .map_err(|_| Error::InvalidPrivateKey)
                .map(Self::MlKem1024),
            _ => Err(Error::UnsupportedAlgorithm),
        }
    }
}

impl PublicKey {
    /// Encapsulate a shared secret to the provided `pk` and return the `(Key, Enc)` tuple.
    pub fn encapsulate(&self, rng: &mut (impl CryptoRng + Rng)) -> Result<(Ss, Ct), Error> {
        match self {
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

            PublicKey::MlKem512(pk) => {
                let seed = mlkem_rand(rng)?;
                let (ct, ss) = libcrux_ml_kem::mlkem512::encapsulate(pk, seed);
                Ok((Ss::MlKem512(ss), Ct::MlKem512(ct)))
            }

            PublicKey::MlKem768(pk) => {
                let seed = mlkem_rand(rng)?;
                let (ct, ss) = mlkem768::encapsulate(pk, seed);
                Ok((Ss::MlKem768(ss), Ct::MlKem768(ct)))
            }

            PublicKey::MlKem1024(pk) => {
                let seed = mlkem_rand(rng)?;
                let (ct, ss) = mlkem1024::encapsulate(pk, seed);
                Ok((Ss::MlKem1024(ss), Ct::MlKem1024(ct)))
            }

            PublicKey::X25519MlKem768Draft00(X25519MlKem768Draft00PublicKey {
                mlkem: kpk,
                x25519: xpk,
            }) => {
                let seed = mlkem_rand(rng)?;
                let (mlkem_ct, mlkem_ss) = mlkem768::encapsulate(kpk, seed);
                let (x_sk, x_pk) = ecdh::x25519_key_gen(rng)?;
                let x_ss = x25519::derive(xpk, &x_sk)?;

                Ok((
                    Ss::X25519MlKem768Draft00(mlkem_ss, x_ss),
                    Ct::X25519MlKem768Draft00(mlkem_ct, x_pk),
                ))
            }

            PublicKey::XWingKemDraft02(XWingKemDraft02PublicKey { pk_m, pk_x }) => {
                let seed = mlkem_rand(rng)?;
                let (ct_m, ss_m) = mlkem768::encapsulate(pk_m, seed);
                let (ek_x, ct_x) = ecdh::x25519_key_gen(rng)?;
                let ss_x = x25519::derive(pk_x, &ek_x)?;

                Ok((
                    Ss::XWingKemDraft02(
                        ss_m,
                        ss_x,
                        x25519::PublicKey(ct_x.0.clone()),
                        x25519::PublicKey(pk_x.0.clone()),
                    ),
                    Ct::XWingKemDraft02(ct_m, x25519::PublicKey(ct_x.0.clone())),
                ))
            }
        }
    }

    /// Encode public key.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            PublicKey::X25519(k) => k.0.to_vec(),
            PublicKey::P256(k) => k.0.to_vec(),
            PublicKey::MlKem512(k) => k.as_ref().to_vec(),
            PublicKey::MlKem768(k) => k.as_ref().to_vec(),
            PublicKey::X25519MlKem768Draft00(k) => k.encode(),
            PublicKey::XWingKemDraft02(k) => k.encode(),
            PublicKey::MlKem1024(k) => k.as_ref().to_vec(),
        }
    }

    /// Decode a public key.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map(Self::X25519)
                .map_err(|_| Error::InvalidPublicKey),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map(Self::P256)
                .map_err(|_| Error::InvalidPublicKey),
            Algorithm::MlKem512 => MlKem512PublicKey::try_from(bytes)
                .ok()
                .and_then(mlkem512::validate_public_key)
                .map(Self::MlKem512)
                .ok_or(Error::InvalidPublicKey),
            Algorithm::MlKem768 => MlKem768PublicKey::try_from(bytes)
                .ok()
                .and_then(mlkem768::validate_public_key)
                .map(Self::MlKem768)
                .ok_or(Error::InvalidPublicKey),
            Algorithm::X25519MlKem768Draft00 => {
                X25519MlKem768Draft00PublicKey::decode(bytes).map(Self::X25519MlKem768Draft00)
            }
            Algorithm::XWingKemDraft02 => {
                XWingKemDraft02PublicKey::decode(bytes).map(Self::XWingKemDraft02)
            }
            Algorithm::MlKem1024 => MlKem1024PublicKey::try_from(bytes)
                .ok()
                .and_then(mlkem1024::validate_public_key)
                .map(Self::MlKem1024)
                .ok_or(Error::InvalidPublicKey),
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
            Ss::MlKem512(k) => k.as_ref().to_vec(),
            Ss::MlKem768(k) => k.as_ref().to_vec(),
            Ss::X25519MlKem768Draft00(kk, xk) => {
                let mut out = xk.0.to_vec();
                out.extend_from_slice(kk.as_ref());
                out
            }
            Ss::XWingKemDraft02(ss_m, ss_x, ct_x, pk_x) => {
                // \./
                // /^\
                // 5c2e2f2f5e5c
                let mut input = vec![0x5c, 0x2e, 0x2f, 0x2f, 0x5e, 0x5c];
                input.extend_from_slice(ss_m.as_ref());
                input.extend_from_slice(ss_x.as_ref());
                input.extend_from_slice(ct_x.0.as_ref());
                input.extend_from_slice(pk_x.0.as_ref());
                sha3::sha256(&input).to_vec()
            }
            Ss::MlKem1024(k) => k.as_ref().to_vec(),
        }
    }
}

impl Ct {
    /// Encode a ciphertext.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Ct::X25519(k) => k.0.to_vec(),
            Ct::P256(k) => k.0.to_vec(),
            Ct::MlKem512(k) => k.as_ref().to_vec(),
            Ct::MlKem768(k) => k.as_ref().to_vec(),
            Ct::X25519MlKem768Draft00(kk, xk) => {
                let mut out = xk.0.to_vec();
                out.extend_from_slice(kk.as_ref());
                out
            }
            Ct::XWingKemDraft02(ct_m, ct_x) => {
                let mut out = ct_m.as_ref().to_vec();
                out.extend_from_slice(ct_x.as_ref());
                out
            }
            Ct::MlKem1024(k) => k.as_ref().to_vec(),
        }
    }

    /// Decode a ciphertext.
    pub fn decode(alg: Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::X25519 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(Self::X25519),
            Algorithm::Secp256r1 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(Self::P256),
            Algorithm::MlKem512 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(Self::MlKem512),
            Algorithm::MlKem768 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(Self::MlKem768),
            Algorithm::X25519MlKem768Draft00 => {
                let key: [u8; MlKem768Ciphertext::len() + 32] =
                    bytes.try_into().map_err(|_| Error::InvalidCiphertext)?;
                let (kct, xct) = key.split_at(MlKem768Ciphertext::len());
                Ok(Self::X25519MlKem768Draft00(
                    kct.try_into().map_err(|_| Error::InvalidCiphertext)?,
                    xct.try_into().map_err(|_| Error::InvalidCiphertext)?,
                ))
            }
            Algorithm::XWingKemDraft02 => {
                let key: [u8; MlKem768Ciphertext::len() + 32] =
                    bytes.try_into().map_err(|_| Error::InvalidCiphertext)?;
                let (ct_m, ct_x) = key.split_at(MlKem768Ciphertext::len());
                Ok(Self::XWingKemDraft02(
                    ct_m.try_into().map_err(|_| Error::InvalidCiphertext)?,
                    ct_x.try_into().map_err(|_| Error::InvalidCiphertext)?,
                ))
            }
            Algorithm::MlKem1024 => bytes
                .try_into()
                .map_err(|_| Error::InvalidCiphertext)
                .map(Self::MlKem1024),
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

fn gen_mlkem768(
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(MlKem768PrivateKey, MlKem768PublicKey), Error> {
    Ok(mlkem768::generate_key_pair(random_array(rng)?).into_parts())
}

fn random_array<const L: usize>(rng: &mut (impl CryptoRng + Rng)) -> Result<[u8; L], Error> {
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;
    Ok(seed)
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
        Algorithm::MlKem512 => {
            let (sk, pk) = mlkem512::generate_key_pair(random_array(rng)?).into_parts();
            Ok((PrivateKey::MlKem512(sk), PublicKey::MlKem512(pk)))
        }
        Algorithm::MlKem768 => {
            let (sk, pk) = mlkem768::generate_key_pair(random_array(rng)?).into_parts();
            Ok((PrivateKey::MlKem768(sk), PublicKey::MlKem768(pk)))
        }
        Algorithm::MlKem1024 => {
            let (sk, pk) = mlkem1024::generate_key_pair(random_array(rng)?).into_parts();
            Ok((PrivateKey::MlKem1024(sk), PublicKey::MlKem1024(pk)))
        }
        Algorithm::X25519MlKem768Draft00 => {
            let (mlkem_private, mlkem_public) = gen_mlkem768(rng)?;
            let (x25519_private, x25519_public) = ecdh::x25519_key_gen(rng)?;
            Ok((
                PrivateKey::X25519MlKem768Draft00(X25519MlKem768Draft00PrivateKey {
                    mlkem: mlkem_private,
                    x25519: x25519_private,
                }),
                PublicKey::X25519MlKem768Draft00(X25519MlKem768Draft00PublicKey {
                    mlkem: mlkem_public,
                    x25519: x25519_public,
                }),
            ))
        }
        Algorithm::XWingKemDraft02 => {
            let (sk_m, pk_m) = gen_mlkem768(rng)?;
            let (sk_x, pk_x) = ecdh::x25519_key_gen(rng)?;
            Ok((
                PrivateKey::XWingKemDraft02(XWingKemDraft02PrivateKey {
                    sk_m,
                    sk_x,
                    pk_x: x25519::PublicKey(pk_x.0.clone()),
                }),
                PublicKey::XWingKemDraft02(XWingKemDraft02PublicKey { pk_m, pk_x }),
            ))
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

fn mlkem_rand(
    rng: &mut (impl CryptoRng + Rng),
) -> Result<[u8; libcrux_ml_kem::SHARED_SECRET_SIZE], Error> {
    let mut seed = [0; libcrux_ml_kem::SHARED_SECRET_SIZE];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;
    Ok(seed)
}
