//! # libcrux-sha2
//!
//! A pure Rust implementation of the SHA-2 family of cryptographic hash functions.
//!
//! This crate provides implementations for SHA-224, SHA-256, SHA-384, and SHA-512
//! hash algorithms. The implementation is based on verified HACL* code and provides
//! both a simple functional API and trait-based interfaces.
//!
//! ## Examples
//!
//! ```rust
//! use libcrux_sha2::{sha256, SHA256_LENGTH};
//!
//! let data = b"hello world";
//! let hash = sha256(data);
//! assert_eq!(hash.len(), SHA256_LENGTH);
//! ```

#![no_std]

/// The length of a SHA224 hash in bytes.
pub const SHA224_LENGTH: usize = 28;

/// The length of a SHA256 hash in bytes.
pub const SHA256_LENGTH: usize = 32;

/// The length of a SHA384 hash in bytes.
pub const SHA384_LENGTH: usize = 48;

/// The length of a SHA512 hash in bytes.
pub const SHA512_LENGTH: usize = 64;

/// The generated hacl code
#[cfg(not(feature = "expose-hacl"))]
mod hacl;

/// The generated hacl code
#[cfg(feature = "expose-hacl")]
#[allow(missing_docs)]
pub mod hacl;

/// The implementation of our types using that hacl code
mod impl_hacl;

mod impl_digest_trait;

pub use impl_hacl::*;

pub use libcrux_traits::Digest;

pub use impl_digest_trait::*;
