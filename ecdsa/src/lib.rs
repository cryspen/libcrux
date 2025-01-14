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
}
