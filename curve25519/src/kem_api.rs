//! This module implements a DH-Based KEM (DHKEM) based on RFC 9180.
//!
//! The DHKEM uses a fixed KDF (HKDF-SHA2_256) and generates shared
//! secrets of lenght `L` using the following domain separation values:
//! - `extract_label = "eae_prk"`
//! - `expand_label = "shared_secret"`
//! - `suite_id = "KEM" | I2OSP(kem_id,2)"`, where `kem_id = 0x0020` is
//!   the KEM ID associated with DHKEM(X25519,HKDF-SHA256) in RFC 9180.
//! - `ikm_label = "HPKE-v1" | suite_id | extract_label`
//! - `expand_label = I2OSP(L,2) | "HPKE-v1" | suite_id | expand_label`
//!
//! The module does not implement the AuthKEM functionality defined in RFC
//! 9180.
//!
//! Usage:
//! ```
//! use rand::RngCore;
//! use libcrux_curve25519::*;
//! use libcrux_curve25519::kem_api::*;
//!
//! let mut rng = rand::rng();
//!
//! // Responder key generation
//! let mut pk = [0u8; EK_LEN];
//! let mut sk = [0u8; DK_LEN];
//! let mut rand_keygen = [0u8; DK_LEN];
//!
//! rng.fill_bytes(&mut rand_keygen);
//!
//! X25519::keygen(&mut pk, &mut sk, &rand_keygen).unwrap();
//!
//! // Encapsulation
//! let mut rand_encaps = [0u8; DK_LEN];
//! rng.fill_bytes(&mut rand_encaps);
//!
//! let mut enc = [0u8; EK_LEN];
//! let mut shared_secret_initiator = [0u8; SHARED_SECRET_LEN];
//! X25519::encaps(&mut enc, &mut shared_secret_initiator, &pk, &rand_encaps).unwrap();
//!
//! // Decapsulation
//! let mut shared_secret_responder = [0u8; SHARED_SECRET_LEN];
//! X25519::decaps(&mut shared_secret_responder, &enc, &sk).unwrap();
//!
//! assert_eq!(shared_secret_initiator, shared_secret_responder);
//!
//! ```
use super::{DK_LEN, EK_LEN, X25519};
use libcrux_hkdf::HkdfMode;
use libcrux_secrets::{ClassifyRef as _, ClassifyRefMut as _};
pub use libcrux_traits::kem::arrayref::Kem;
use libcrux_traits::{
    ecdh::arrayref::EcdhArrayref,
    kem::arrayref::{DecapsError, EncapsError, KeyGenError},
};

/// An internal error that occurs during DHKEM operations.
enum DhKemError {
    Hkdf,
}

pub const SHARED_SECRET_LEN: usize = 32;

impl Kem<DK_LEN, EK_LEN, EK_LEN, SHARED_SECRET_LEN, DK_LEN, DK_LEN> for X25519 {
    fn keygen(
        ek: &mut [u8; DK_LEN],
        dk: &mut [u8; EK_LEN],
        rand: &[u8; DK_LEN],
    ) -> Result<(), KeyGenError> {
        X25519::generate_pair(ek, dk.classify_ref_mut(), rand.classify_ref())
            .map_err(|_| KeyGenError::InvalidRandomness)
    }

    fn encaps(
        ct: &mut [u8; EK_LEN],
        ss: &mut [u8; SHARED_SECRET_LEN],
        ek: &[u8; EK_LEN],
        rand: &[u8; DK_LEN],
    ) -> Result<(), EncapsError> {
        let mut ephemeral_secret = [0u8; DK_LEN];

        X25519::generate_pair(ct, ephemeral_secret.classify_ref_mut(), rand.classify_ref())
            .map_err(|_| EncapsError::InvalidRandomness)?;

        let mut derived_ecdh = [0u8; EK_LEN];
        X25519::derive_ecdh(
            derived_ecdh.classify_ref_mut(),
            ek,
            ephemeral_secret.classify_ref(),
        )
        .map_err(|_| EncapsError::InvalidEncapsKey)?;

        extract_and_expand(ct, ss, ek, derived_ecdh).map_err(|_| EncapsError::Unknown)
    }

    fn decaps(
        ss: &mut [u8; SHARED_SECRET_LEN],
        ct: &[u8; DK_LEN],
        dk: &[u8; EK_LEN],
    ) -> Result<(), DecapsError> {
        let mut derived_ecdh = [0u8; EK_LEN];
        X25519::derive_ecdh(derived_ecdh.classify_ref_mut(), ct, dk.classify_ref())
            .map_err(|_| DecapsError::InvalidCiphertext)?;

        let mut ek = [0u8; EK_LEN];
        X25519::secret_to_public(&mut ek, dk.classify_ref())
            .map_err(|_| DecapsError::InvalidDecapsKey)?;

        extract_and_expand(ct, ss, &ek, derived_ecdh).map_err(|_| DecapsError::Unknown)
    }
}

fn extract_and_expand<const SHARED_SECRET_LEN: usize>(
    ct: &[u8; 32],
    ss: &mut [u8; SHARED_SECRET_LEN],
    ek: &[u8; 32],
    derived_ecdh: [u8; 32],
) -> Result<(), DhKemError> {
    debug_assert!(SHARED_SECRET_LEN <= u16::MAX as usize);

    let mut kem_context = [0u8; 2 * EK_LEN];
    kem_context[..EK_LEN].copy_from_slice(ct.as_slice());
    kem_context[EK_LEN..].copy_from_slice(ek.as_slice());

    // `YY` marks bytes reserved for KEM ID
    let ikm_label = b"HPKE-v1YYeae_prk";
    let mut labeled_ikm = [0u8; EK_LEN + 16];
    labeled_ikm[..ikm_label.len()].copy_from_slice(ikm_label.as_slice());
    // Fill in KEM ID
    labeled_ikm[7..9].copy_from_slice(&[0x00, 0x20]);
    labeled_ikm[ikm_label.len()..].copy_from_slice(derived_ecdh.as_slice());

    let mut eae_prk = [0u8; 32];
    libcrux_hkdf::HkdfSha2_256::extract(&mut eae_prk, &[], &labeled_ikm)
        .map_err(|_| DhKemError::Hkdf)?;

    // `XX` marks bytes reserved for I2OSP(SHARED_SECRET_LEN, 2)
    // `YY` marks bytes reserved for KEM ID
    let info_label = b"YYHPKE-v1XXshared_secret";
    let mut labeled_info = [0u8; 2 * EK_LEN + 24];
    labeled_info[..info_label.len()].copy_from_slice(info_label.as_slice());
    // Fill in I2OSP(SHARED_SECRET_LEN, 2)
    labeled_info[0..2].copy_from_slice(&(SHARED_SECRET_LEN as u16).to_be_bytes());
    // Fill in KEM ID
    labeled_info[9..11].copy_from_slice(&[0x00, 0x20]);
    labeled_info[info_label.len()..].copy_from_slice(kem_context.as_slice());

    libcrux_hkdf::HkdfSha2_256::expand(ss, eae_prk.as_slice(), &labeled_info)
        .map_err(|_| DhKemError::Hkdf)
}

libcrux_traits::kem::slice::impl_trait!(X25519 => EK_LEN, DK_LEN, EK_LEN, SHARED_SECRET_LEN, DK_LEN, DK_LEN);
