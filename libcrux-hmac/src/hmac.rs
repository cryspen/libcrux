//! HMAC
//!
//! This crate implements HMAC on SHA 1 and SHA 2 (except for SHA 224).

use libcrux_hkdf as hkdf;

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
/// Panics if either `key` or `data` are longer than `u32::MAX`.
pub fn hmac(alg: Algorithm, key: &[u8], data: &[u8], tag_length: Option<usize>) -> Vec<u8> {
    let native_tag_length = tag_size(alg);
    let tag_length = match tag_length {
        Some(v) => v,
        None => native_tag_length,
    };
    let mut dst: Vec<_> = match alg {
        Algorithm::Sha1 => wrap_bufalloc(|buf| hmac_sha1(buf, key, data)).into(),
        Algorithm::Sha256 => wrap_bufalloc(|buf| hmac_sha256(buf, key, data)).into(),
        Algorithm::Sha384 => wrap_bufalloc(|buf| hmac_sha384(buf, key, data)).into(),
        Algorithm::Sha512 => wrap_bufalloc(|buf| hmac_sha512(buf, key, data)).into(),
    };
    dst.truncate(tag_length);
    dst
}

fn wrap_bufalloc<const N: usize, F: Fn(&mut [u8; N])>(f: F) -> [u8; N] {
    let mut buf = [0u8; N];
    f(&mut buf);
    buf
}

macro_rules! impl_hmac {
    ($name:ident,$fun:path,$tag_len:literal) => {
        /// Compute HMAC.
        ///
        /// Note that this function panics if `key` or `data` is larger than 2**32 bytes.
        pub fn $name(dst: &mut [u8; $tag_len], key: &[u8], data: &[u8]) {
            $fun(
                dst,
                key,
                key.len().try_into().unwrap(),
                data,
                data.len().try_into().unwrap(),
            )
        }
    };
}

impl_hmac!(hmac_sha1, libcrux_hacl_rs::hmac::compute_sha1, 20);
impl_hmac!(hmac_sha256, libcrux_hacl_rs::hmac::compute_sha2_256, 32);
impl_hmac!(hmac_sha384, libcrux_hacl_rs::hmac::compute_sha2_384, 32);
impl_hmac!(hmac_sha512, libcrux_hacl_rs::hmac::compute_sha2_512, 32);
