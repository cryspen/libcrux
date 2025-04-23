//! # PQ-PSK
//!
//! This crate implements a protocol for establishing and mutually
//! registering a PQ-PSK between an initiator and a responder.

#![deny(missing_docs)]

use std::array::TryFromSliceError;

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
    /// An error while decoding bytes
    Decoding,
}

#[cfg(debug_assertions)]
fn print_error(m: &str, e: &impl std::fmt::Debug) {
    use std::backtrace;

    eprintln!("{m} {e:?}");
    let bt = backtrace::Backtrace::capture();
    eprintln!("{bt}");
}

impl From<libcrux_kem::Error> for Error {
    fn from(_e: libcrux_kem::Error) -> Self {
        #[cfg(debug_assertions)]
        print_error("KEM error", &_e);
        Self::CryptoError
    }
}

impl From<libcrux_chacha20poly1305::AeadError> for Error {
    fn from(_e: libcrux_chacha20poly1305::AeadError) -> Self {
        #[cfg(debug_assertions)]
        print_error("Chacha20Poly1305 error", &_e);
        Self::CryptoError
    }
}

impl From<libcrux_hkdf::Error> for Error {
    fn from(_e: libcrux_hkdf::Error) -> Self {
        #[cfg(debug_assertions)]
        print_error("HKDF error", &_e);
        Self::CryptoError
    }
}

impl From<TryFromSliceError> for Error {
    fn from(_e: TryFromSliceError) -> Self {
        #[cfg(debug_assertions)]
        print_error("TryFromSliceError", &_e);
        Self::CryptoError
    }
}

const PSK_LENGTH: usize = 32;
type Psk = [u8; PSK_LENGTH];

pub mod cred;
pub mod psk_registration;

#[cfg(feature = "classic-mceliece")]
pub mod classic_mceliece;
pub mod impls;
pub mod traits;
