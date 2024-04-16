//! # Hardware abstraction
//!
//! This crate implements hardware abstraction for 128-bit and 256-bit SIMD on
//! x64 and aarch64.

#![no_std]

/// When we build for aarch64 and the simd128 config is enabled.
#[cfg(all(target_arch = "aarch64", feature = "simd128"))]
pub use aarch64;

pub mod scalar;
