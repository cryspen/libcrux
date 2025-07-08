//! # SHA3
//!
//! A SHA3 implementation with optional simd optimisations.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

mod simd;

mod generic_keccak;
mod traits;

/// A SHA3 224 Digest
pub type Sha3_224Digest = [Secret<u8>; 28];

/// A SHA3 256 Digest
pub type Sha3_256Digest = [Secret<u8>; 32];

/// A SHA3 384 Digest
pub type Sha3_384Digest = [Secret<u8>; 48];

/// A SHA3 512 Digest
pub type Sha3_512Digest = [Secret<u8>; 64];

/// The Digest Algorithm.
#[cfg_attr(not(eurydice), derive(Copy, Clone, Debug, PartialEq))]
#[repr(u32)]
pub enum Algorithm {
    /// SHA3 224
    Sha224 = 1,

    /// SHA3 256
    Sha256 = 2,

    /// SHA3 384
    Sha384 = 3,

    /// SHA3 512
    Sha512 = 4,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha224,
            2 => Algorithm::Sha256,
            3 => Algorithm::Sha384,
            4 => Algorithm::Sha512,
            _ => panic!(),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha224 => 1,
            Algorithm::Sha256 => 2,
            Algorithm::Sha384 => 3,
            Algorithm::Sha512 => 4,
        }
    }
}

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha224 => 28,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
    }
}

/// SHA3
pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[Secret<u8>]) -> [Secret<u8>; LEN] {
    debug_assert!(payload.len() <= u32::MAX as usize);

    let mut out = [0u8; LEN].classify();
    match algorithm {
        Algorithm::Sha224 => portable::sha224(&mut out, payload),
        Algorithm::Sha256 => portable::sha256(&mut out, payload),
        Algorithm::Sha384 => portable::sha384(&mut out, payload),
        Algorithm::Sha512 => portable::sha512(&mut out, payload),
    }
    out
}

/// SHA3
pub use hash as sha3;
use libcrux_secrets::{Classify, Secret};

/// SHA3 224
#[inline(always)]
pub fn sha224(data: &[Secret<u8>]) -> Sha3_224Digest {
    let mut out = [0u8; 28].classify();
    sha224_ema(&mut out, data);
    out
}

/// SHA3 224
///
/// Preconditions:
/// - `digest.len() == 28`
#[inline(always)]
pub fn sha224_ema(digest: &mut [Secret<u8>], payload: &[Secret<u8>]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 28);

    portable::sha224(digest, payload)
}

/// SHA3 256
#[inline(always)]
pub fn sha256(data: &[Secret<u8>]) -> Sha3_256Digest {
    let mut out = [0u8; 32].classify();
    sha256_ema(&mut out, data);
    out
}

/// SHA3 256
#[inline(always)]
pub fn sha256_ema(digest: &mut [Secret<u8>], payload: &[Secret<u8>]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 32);

    portable::sha256(digest, payload)
}

/// SHA3 384
#[inline(always)]
pub fn sha384(data: &[Secret<u8>]) -> Sha3_384Digest {
    let mut out = [0u8; 48].classify();
    sha384_ema(&mut out, data);
    out
}

/// SHA3 384
#[inline(always)]
pub fn sha384_ema(digest: &mut [Secret<u8>], payload: &[Secret<u8>]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 48);

    portable::sha384(digest, payload)
}

/// SHA3 512
#[inline(always)]
pub fn sha512(data: &[Secret<u8>]) -> Sha3_512Digest {
    let mut out = [0u8; 64].classify();
    sha512_ema(&mut out, data);
    out
}

/// SHA3 512
#[inline(always)]
pub fn sha512_ema(digest: &mut [Secret<u8>], payload: &[Secret<u8>]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 64);

    portable::sha512(digest, payload)
}

/// SHAKE 128
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[Secret<u8>]) -> [Secret<u8>; BYTES] {
    let mut out = [0u8; BYTES].classify();
    portable::shake128(&mut out, data);
    out
}

/// SHAKE 128
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake128_ema(out: &mut [Secret<u8>], data: &[Secret<u8>]) {
    portable::shake128(out, data);
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake256<const BYTES: usize>(data: &[Secret<u8>]) -> [Secret<u8>; BYTES] {
    let mut out = [0u8; BYTES].classify();
    portable::shake256(&mut out, data);
    out
}

/// SHAKE 256
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake256_ema(out: &mut [Secret<u8>], data: &[Secret<u8>]) {
    portable::shake256(out, data);
}

//  === Instantiation === //

/// A portable SHA3 implementation without platform dependent optimisations.
pub mod portable;

/// A neon optimised implementation.
///
/// When this is compiled for non-neon architectures, the functions panic.
/// The caller must make sure to check for hardware feature before calling these
/// functions and compile them in.
///
/// Feature `simd128` enables the implementations in this module.
#[cfg(feature = "simd128")]
pub mod neon;

/// An AVX2 optimised implementation.
///
/// When this is compiled for non-neon architectures, the functions panic.
/// The caller must make sure to check for hardware feature before calling these
/// functions and compile them in.
///
/// Feature `simd256` enables the implementations in this module.
#[cfg(feature = "simd256")]
pub mod avx2;
