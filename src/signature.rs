//! # Signatures
//!
//! * EcDSA P256 with Sha256, Sha384, and Sha512
//! * EdDSA 25519
//! * RSA PSS

use crate::{
    ecdh,
    hacl::{self, ed25519},
};
use rand::{CryptoRng, Rng, RngCore};

use self::rsa_pss::RsaPssSignature;

/// Signature Errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    SigningError,
    InvalidSignature,
    KeyGenError,
    InvalidKey,
    InputTooLarge,
}

/// The digest algorithm used for the signature scheme (when required).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigestAlgorithm {
    Sha256,
    Sha384,
    Sha512,
}

/// The Signature Algorithm
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Algorithm {
    EcDsaP256(DigestAlgorithm),
    Ed25519,
    RsaPss(DigestAlgorithm),
}

/// The signature
#[derive(Debug)]
pub enum Signature {
    EcDsaP256(EcDsaP256Signature),
    Ed25519(Ed25519Signature),
    RsaPss(RsaPssSignature),
}

impl Signature {
    /// Convert the signature into a raw byte vector.
    ///
    /// * NIST P Curve signatures are returned as `r || s`.
    /// * RSA PSS signatures are returned as the raw bytes.
    pub fn into_vec(self) -> Vec<u8> {
        match self {
            Signature::EcDsaP256(s) => {
                let mut out = s.r.to_vec();
                out.extend_from_slice(&s.s);
                out
            }
            Signature::Ed25519(s) => s.signature.to_vec(),
            Signature::RsaPss(s) => s.value,
        }
    }
}

/// A [`Algorithm::EcDsaP256`] Signature
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EcDsaP256Signature {
    r: [u8; 32],
    s: [u8; 32],
    alg: Algorithm,
}

/// A [`Algorithm::Ed25519`] Signature
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ed25519Signature {
    signature: [u8; 64],
}

pub mod rsa_pss {
    use libcrux_hacl::{
        hacl_free, Hacl_RSAPSS_new_rsapss_load_pkey, Hacl_RSAPSS_new_rsapss_load_skey,
        Hacl_RSAPSS_rsapss_sign, Hacl_RSAPSS_rsapss_verify,
    };

    use super::{DigestAlgorithm, Error};

    /// A [`Algorithm::RsaPss`](super::Algorithm::RsaPss) Signature
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct RsaPssSignature {
        pub(super) value: Vec<u8>,
    }

    impl RsaPssSignature {
        /// Get the signature as the raw byte slice.
        pub fn as_bytes(&self) -> &[u8] {
            &self.value
        }
    }

    impl From<&[u8]> for RsaPssSignature {
        fn from(value: &[u8]) -> Self {
            Self {
                value: value.to_vec(),
            }
        }
    }

    impl<const L: usize> From<[u8; L]> for RsaPssSignature {
        fn from(value: [u8; L]) -> Self {
            Self {
                value: value.to_vec(),
            }
        }
    }

    impl From<Vec<u8>> for RsaPssSignature {
        fn from(value: Vec<u8>) -> Self {
            Self { value }
        }
    }

    /// A [`Algorithm::RsaPss`](super::Algorithm::RsaPss) public key.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct RsaPssPublicKey {
        n: Vec<u8>,
    }

    fn rsa_pss_digest(hash_algorithm: DigestAlgorithm) -> u8 {
        match hash_algorithm {
            DigestAlgorithm::Sha256 => libcrux_hacl::Spec_Hash_Definitions_SHA2_256 as u8,
            DigestAlgorithm::Sha384 => libcrux_hacl::Spec_Hash_Definitions_SHA2_384 as u8,
            DigestAlgorithm::Sha512 => libcrux_hacl::Spec_Hash_Definitions_SHA2_512 as u8,
        }
    }

    /// The key size is the bit/byte-size of the modulus N.
    /// Note that the values are bytes but the names are in bits.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[repr(usize)]
    pub enum RsaPssKeySize {
        /// N = 2048 bits | 256 bytes
        N2048 = 256,

        /// N = 3072 bits | 384 bytes
        N3072 = 384,

        /// N = 4096 bits | 512 bytes
        N4096 = 512,

        /// N = 6144 bits | 768 bytes
        N6144 = 768,

        /// N = 8192 bits | 1024 bytes
        N8192 = 1024,
    }

    // Size of e.
    const E_BITS: u32 = 17;

    // We only support this e.
    const E: [u8; 3] = [0x01, 0x00, 0x01];

    impl RsaPssPublicKey {
        pub fn new(key_size: RsaPssKeySize, n: &[u8]) -> Result<Self, Error> {
            if n.len() != key_size as usize {
                return Err(Error::InvalidKey);
            }
            Ok(Self { n: n.into() })
        }

        /// Verify the `signature` on the `msg` with the `public_key` using the
        /// `hash_algorithm` and `salt_len`.
        ///
        /// Returns an error if any of the inputs are invalid or the signature is
        /// invalid.
        #[must_use = "The result of the signature verification must be used."]
        pub fn verify(
            &self,
            hash_algorithm: DigestAlgorithm,
            signature: &RsaPssSignature,
            msg: &[u8],
            salt_len: usize,
        ) -> Result<(), Error> {
            let key_size_bits = (self.n.len() as u32) * 8;
            unsafe {
                let pkey = Hacl_RSAPSS_new_rsapss_load_pkey(
                    key_size_bits,
                    E_BITS,
                    self.n.as_ptr() as _,
                    E.as_ptr() as _,
                );
                if Hacl_RSAPSS_rsapss_verify(
                    rsa_pss_digest(hash_algorithm),
                    key_size_bits,
                    E_BITS,
                    pkey,
                    salt_len as u32,
                    signature.value.len() as u32,
                    signature.value.as_ptr() as _,
                    msg.len() as u32,
                    msg.as_ptr() as _,
                ) {
                    return Ok(());
                }
            }
            Err(Error::InvalidSignature)
        }
    }

    /// An RSA-PSS private key.
    /// The private key holds a [`RsaPssPublicKey`] with the public modulus.
    /// A [`Algorithm::RsaPss`](super::Algorithm::RsaPss) private key.
    pub struct RsaPssPrivateKey<'a> {
        pk: &'a RsaPssPublicKey,
        d: Vec<u8>,
    }

    impl<'a> RsaPssPrivateKey<'a> {
        ///Create a new [`RsaPssPrivateKey`] from a byte slice and a public key.
        ///
        /// Returns an error if the length of the byte slice is not equal to the
        /// key/modulus size.
        pub fn new(pk: &'a RsaPssPublicKey, d: &[u8]) -> Result<Self, Error> {
            if pk.n.len() != d.len() {
                return Err(Error::InvalidKey);
            }
            Ok(Self { pk, d: d.into() })
        }

        /// Sign the provided `msg` with the `private_key` using the `hash_algorithm`
        /// and `salt`.
        ///
        /// Returns an error if any of the inputs are invalid and the signature as byte
        /// array.
        pub fn sign(
            &self,
            hash_algorithm: DigestAlgorithm,
            salt: &[u8],
            msg: &[u8],
        ) -> Result<RsaPssSignature, Error> {
            if salt.len() > (u32::MAX as usize) || msg.len() > (u32::MAX as usize) {
                return Err(Error::InputTooLarge);
            }

            let key_len = self.d.len();
            let mut signature = vec![0; key_len];
            let key_size_bits = (key_len as u32) * 8;

            unsafe {
                let s_key = Hacl_RSAPSS_new_rsapss_load_skey(
                    key_size_bits,
                    E_BITS,
                    key_size_bits,
                    self.pk.n.as_ptr() as _,
                    E.as_ptr() as _,
                    self.d.as_ptr() as _,
                );

                if !Hacl_RSAPSS_rsapss_sign(
                    rsa_pss_digest(hash_algorithm),
                    key_size_bits,
                    E_BITS,
                    key_size_bits,
                    s_key,
                    salt.len() as u32,
                    salt.as_ptr() as _,
                    msg.len() as u32,
                    msg.as_ptr() as _,
                    signature.as_mut_ptr(),
                ) {
                    hacl_free(s_key as _);
                    return Err(Error::SigningError);
                }
                hacl_free(s_key as _);
            }
            Ok(RsaPssSignature { value: signature })
        }
    }
}

impl Ed25519Signature {
    /// Generate a signature from the raw 64 bytes.
    pub fn from_bytes(signature: [u8; 64]) -> Self {
        Self { signature }
    }

    /// Generate a signature from the raw bytes slice.
    ///
    /// Returns an error if the slice has legnth != 64.
    pub fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            signature: bytes.try_into().map_err(|_| Error::InvalidSignature)?,
        })
    }

    /// Get the signature as the raw 64 bytes.
    pub fn as_bytes(&self) -> &[u8; 64] {
        &self.signature
    }
}

impl EcDsaP256Signature {
    /// Generate a signature from the raw values r and s.
    pub fn from_raw(r: [u8; 32], s: [u8; 32], alg: Algorithm) -> Self {
        Self { r, s, alg }
    }

    /// Generate a signature from the raw values r || s.
    pub fn from_bytes(signature_bytes: [u8; 64], alg: Algorithm) -> Self {
        Self {
            r: signature_bytes[0..32].try_into().unwrap(),
            s: signature_bytes[32..].try_into().unwrap(),
            alg,
        }
    }

    /// Get the signature as the two raw 32 bytes `(r, s)`.
    pub fn as_bytes(&self) -> (&[u8; 32], &[u8; 32]) {
        (&self.r, &self.s)
    }
}

/// Prepare the nonce for EcDSA and validate the key
fn ecdsa_p256_sign_prep(
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(libcrux_ecdh::P256PrivateKey, [u8; 32]), Error> {
    let private_key =
        libcrux_ecdh::p256::validate_scalar_slice(private_key).map_err(|_| Error::SigningError)?;

    let mut nonce = [0u8; 32];
    loop {
        rng.try_fill_bytes(&mut nonce)
            .map_err(|_| Error::SigningError)?;
        // Make sure it's a valid nonce.
        if libcrux_ecdh::p256::validate_scalar_slice(&nonce).is_ok() {
            break;
        }
    }

    Ok((private_key, nonce))
}

/// Wrap EcDSA result into a signature
fn ecdsa_p256_sign_post(signature: [u8; 64], alg: Algorithm) -> Result<Signature, Error> {
    Ok(Signature::EcDsaP256(EcDsaP256Signature {
        r: signature[..32]
            .try_into()
            .map_err(|_| Error::SigningError)?,
        s: signature[32..]
            .try_into()
            .map_err(|_| Error::SigningError)?,
        alg,
    }))
}

fn into_signing_error(_e: impl Into<hacl::Error>) -> Error {
    Error::SigningError
}

/// Sign the `payload` with the given [`Algorithm`] and `private_key`.
///
/// Returns the [`Signature`] or an [`Error::SigningError`].
pub fn sign(
    alg: Algorithm,
    payload: &[u8],
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Signature, Error> {
    let signature = match alg {
        Algorithm::EcDsaP256(DigestAlgorithm::Sha256) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                crate::hacl::p256::ecdsa::sign_sha256(payload, private_key.as_ref(), &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::EcDsaP256(DigestAlgorithm::Sha384) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                crate::hacl::p256::ecdsa::sign_sha384(payload, private_key.as_ref(), &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::EcDsaP256(DigestAlgorithm::Sha512) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                crate::hacl::p256::ecdsa::sign_sha512(payload, private_key.as_ref(), &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::Ed25519 => {
            let signature = ed25519::sign(
                payload,
                private_key.try_into().map_err(|_| Error::SigningError)?,
            )
            .map_err(into_signing_error)?;
            Signature::Ed25519(Ed25519Signature { signature })
        }
        Algorithm::RsaPss(_) => {
            todo!()
        }
    };

    Ok(signature)
}

fn into_verify_error(_e: impl Into<hacl::Error>) -> Error {
    Error::InvalidSignature
}

/// Prepare the public key for EcDSA
fn ecdsa_p256_verify_prep(public_key: &[u8]) -> Result<[u8; 64], Error> {
    if public_key.is_empty() {
        return Err(Error::SigningError);
    }

    // Parse the public key.
    let pk = if let Ok(pk) = libcrux_ecdh::p256::uncompressed_to_coordinates(public_key) {
        pk
    } else {
        // Might be uncompressed
        if let Ok(pk) = libcrux_ecdh::p256::compressed_to_coordinates(public_key) {
            pk
        } else {
            // Might be a simple concatenation
            public_key.try_into().map_err(|_| Error::InvalidSignature)?
        }
    };

    libcrux_ecdh::p256::validate_point(libcrux_ecdh::P256PublicKey(pk))
        .map(|()| pk)
        .map_err(into_verify_error)
}

/// Verify the `payload` and `signature` with the `public_key`.
///
/// Return `()` or [`Error::InvalidSignature`].
pub fn verify(payload: &[u8], signature: &Signature, public_key: &[u8]) -> Result<(), Error> {
    match signature {
        Signature::EcDsaP256(signature) => match signature.alg {
            Algorithm::EcDsaP256(DigestAlgorithm::Sha256) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                crate::hacl::p256::ecdsa::verify_sha256(payload, &pk, &signature.r, &signature.s)
            }
            Algorithm::EcDsaP256(DigestAlgorithm::Sha384) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                crate::hacl::p256::ecdsa::verify_sha384(payload, &pk, &signature.r, &signature.s)
            }
            Algorithm::EcDsaP256(DigestAlgorithm::Sha512) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                crate::hacl::p256::ecdsa::verify_sha512(payload, &pk, &signature.r, &signature.s)
            }
            _ => Err(crate::hacl::p256::ecdsa::Error::InvalidInput),
        }
        .map_err(into_verify_error),
        Signature::Ed25519(signature) => {
            let public_key = public_key.try_into().map_err(|_| Error::InvalidSignature)?;
            ed25519::verify(payload, public_key, &signature.signature).map_err(into_verify_error)
        }
        Signature::RsaPss(_) => todo!(),
    }
}

/// Generate a fresh key pair.
///
/// The function returns the (secret key, public key) tuple, or an [`Error`].
pub fn key_gen(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        Algorithm::EcDsaP256(_) => {
            ecdh::key_gen(ecdh::Algorithm::P256, rng).map_err(|_| Error::KeyGenError)
        }
        Algorithm::Ed25519 => {
            const LIMIT: usize = 100;
            let mut sk = [0u8; 32];
            for _ in 0..LIMIT {
                rng.try_fill_bytes(&mut sk)
                    .map_err(|_| Error::KeyGenError)?;

                // We don't want a 0 key.
                if sk.iter().all(|&b| b == 0) {
                    sk = [0u8; 32];
                    continue;
                }

                // We clamp the key already to make sure it can't be misused.
                sk[0] &= 248u8;
                sk[31] &= 127u8;
                sk[31] |= 64u8;

                break;
            }
            let pk = ed25519::secret_to_public(&sk);

            Ok((sk.to_vec(), pk.to_vec()))
        }
        Algorithm::RsaPss(_) => todo!(),
    }
}
