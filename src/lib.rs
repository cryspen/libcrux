//! # Modular PQ-PSK Protocol
//!
//! This crate implements a method to generate post-quantum pre-shared keys
//! bound to specific outer protocol contexts. The goal is to harden the outer
//! (potentially classical) protocol against harvest-now-decrypt-later quantum
//! adversaries.

#![deny(missing_docs)]

#[derive(Debug)]
/// PSQ Errors.
pub enum Error {
    /// An invalid public key was provided
    InvalidPublicKey,
    /// An invalid private key was provided
    InvalidPrivateKey,
    /// An error during PSK encapsulation
    PSQGenerationError,
    /// An error during PSK decapsulation
    PSQDerivationError,
    /// An error during binder computation
    BinderError,
    /// An error in the underlying cryptographic algorithms
    CryptoError,
    /// Error relating to operating system environment
    OsError
}

const PSK_LENGTH: usize = 32;
type Psk = [u8; PSK_LENGTH];

pub mod ecdh_binder;
pub mod psq;
