//! # PQ-PSK
//!
//! This crate implements a protocol for establishing and mutually
//! registering a PQ-PSK between an initiator and a responder.

#![deny(missing_docs)]

pub(crate) mod aead;
pub mod handshake;
pub mod session;
pub mod traits;

#[cfg(feature = "legacy")]
pub mod legacy;

#[cfg(feature = "classic-mceliece")]
pub mod classic_mceliece;
