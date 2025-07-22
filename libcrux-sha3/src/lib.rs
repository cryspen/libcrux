//! # SHA3
//!
//! A SHA3 implementation with optional simd optimisations.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

mod simd;

mod generic_keccak;
mod traits;

const SHA3_224_LEN: usize = 28;
const SHA3_256_LEN: usize = 32;
const SHA3_384_LEN: usize = 48;
const SHA3_512_LEN: usize = 64;

/// A SHA3 224 Digest
pub type Sha3_224Digest = [u8; SHA3_224_LEN];

/// A SHA3 256 Digest
pub type Sha3_256Digest = [u8; SHA3_256_LEN];

/// A SHA3 384 Digest
pub type Sha3_384Digest = [u8; SHA3_384_LEN];

/// A SHA3 512 Digest
pub type Sha3_512Digest = [u8; SHA3_512_LEN];

macro_rules! impl_hash_traits {
    ($type:ident, $hasher:ident, $len:expr, $method:expr) => {

        /// TODO: doc comment
        pub struct $type;

        impl libcrux_traits::digest::arrayref::Hash<$len> for $type {
            #[inline(always)]
            fn hash(
                digest: &mut [u8; $len],
                payload: &[u8],
            ) -> Result<(), libcrux_traits::digest::arrayref::HashError> {
                // TODO: return error
                debug_assert!(payload.len() <= u32::MAX as usize);

                $method(digest, payload);

                Ok(())
            }
        }
        libcrux_traits::digest::slice::impl_hash_trait!($type => $len);
    };
}

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

impl_hash_traits!(Sha3_224, Sha3_224Hasher, SHA3_224_LEN, portable::sha224);
impl_hash_traits!(Sha3_256, Sha3_256Hasher, SHA3_256_LEN, portable::sha256);
impl_hash_traits!(Sha3_384, Sha3_384Hasher, SHA3_384_LEN, portable::sha384);
impl_hash_traits!(Sha3_512, Sha3_512Hasher, SHA3_512_LEN, portable::sha512);

/// SHAKE 128
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake128(&mut out, data);
    out
}

/// SHAKE 128
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake128_ema(out: &mut [u8], data: &[u8]) {
    portable::shake128(out, data);
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake256(&mut out, data);
    out
}

/// SHAKE 256
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake256_ema(out: &mut [u8], data: &[u8]) {
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
