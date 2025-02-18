//! # ECDSA
//!
//! A formally verified implementation of ECDSA on P-curves.
//!
//! For now only P-256 is supported.

#![no_std]
#![forbid(unsafe_code)]

pub mod p256;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    InvalidInput,
    InvalidScalar,
    InvalidPoint,
    NoCompressedPoint,
    NoUnCompressedPoint,
    SigningError,
    InvalidSignature,
    RandError,
    UnsupportedHash,
}

/// The hash algorithm used for signing or verifying.
pub type DigestAlgorithm = libcrux_sha2::Algorithm;

/// The number of iteration for rejection sampling.
pub(crate) const RAND_LIMIT: usize = 100;
