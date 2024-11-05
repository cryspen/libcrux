//! HMAC
//!
//! This crate implements HMAC on SHA 1 and SHA 2 (except for SHA 224).

use libcrux_hkdf as hkdf;

use libcrux_hacl_rs::hmac::compute_sha1 as hmac_sha1;
use libcrux_hacl_rs::hmac::compute_sha2_256 as hmac_sha256;
use libcrux_hacl_rs::hmac::compute_sha2_384 as hmac_sha384;
use libcrux_hacl_rs::hmac::compute_sha2_512 as hmac_sha512;

/// The HMAC algorithm defining the used hash function.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Algorithm {
    Sha1,
    // Not implemented
    // Sha224
    Sha256,
    Sha384,
    Sha512,
}

impl From<hkdf::Algorithm> for Algorithm {
    fn from(value: hkdf::Algorithm) -> Self {
        match value {
            hkdf::Algorithm::Sha256 => Self::Sha256,
            hkdf::Algorithm::Sha384 => Self::Sha384,
            hkdf::Algorithm::Sha512 => Self::Sha512,
        }
    }
}

/// Get the tag size for a given algorithm.
pub const fn tag_size(alg: Algorithm) -> usize {
    match alg {
        Algorithm::Sha1 => 20,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
    }
}

/// Compute the HMAC value with the given `alg` and `key` on `data` with an
/// output tag length of `tag_length`.
/// Returns a vector of length `tag_length`.
pub fn hmac(alg: Algorithm, key: &[u8], data: &[u8], tag_length: Option<usize>) -> Vec<u8> {
    let native_tag_length = tag_size(alg);
    let tag_length = match tag_length {
        Some(v) => v,
        None => native_tag_length,
    };
    let mut dst = vec![0u8; native_tag_length];
    match alg {
        Algorithm::Sha1 => hmac_sha1(&mut dst, key, key.len() as u32, data, data.len() as u32),
        Algorithm::Sha256 => hmac_sha256(&mut dst, key, key.len() as u32, data, data.len() as u32),
        Algorithm::Sha384 => hmac_sha384(&mut dst, key, key.len() as u32, data, data.len() as u32),
        Algorithm::Sha512 => hmac_sha512(&mut dst, key, key.len() as u32, data, data.len() as u32),
    };
    dst.truncate(tag_length);
    dst
}
