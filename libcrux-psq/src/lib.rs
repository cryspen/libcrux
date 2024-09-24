//! # PQ-PSK
//!
//! This crate implements a protocol for establishing and mutually
//! registering a PQ-PSK between an initiator and a responder.

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
    /// An error during credential processing
    CredError,
    /// An error during binder computation
    RegistrationError,
    /// An error in the underlying cryptographic algorithms
    CryptoError,
    /// Error relating to operating system environment
    OsError,
}

impl From<libcrux_kem::Error> for Error {
    fn from(_value: libcrux_kem::Error) -> Self {
        Self::CryptoError
    }
}

const PSK_LENGTH: usize = 32;
type Psk = [u8; PSK_LENGTH];

pub mod cred;
pub mod psk_registration;
pub mod psq;
