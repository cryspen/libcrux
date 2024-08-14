//! # Modular PQ-PSK Protocol
//!
//! This crate implements a method to generate post-quantum pre-shared keys
//! bound to specific outer protocol contexts. The goal is to harden the outer
//! (potentially classical) protocol against harvest-now-decrypt-later quantum
//! adversaries.
//!
//! Example usage of a PSK bound to an ECDH protocol context:
//! ```
//! use std::time::Duration;
//!
//! use libcrux_psq::{
//!     ecdh_binder::{receive_ecdh_bound_psq, send_ecdh_bound_psq},
//!     psq::{generate_key_pair, Algorithm},
//! };
//! use rand::thread_rng;
//!
//! fn main() {
//!     let mut rng = thread_rng();
//!     let (receiver_pqsk, receiver_pqpk) = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
//!     let (receiver_dh_sk, receiver_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
//!     let (initiator_dh_sk, _initiator_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
//!
//!     // Generate a PSK and PSK message bound to a specific ECDH key pair.
//!     let (psk_initiator, ecdh_psk_message) = send_ecdh_bound_psq(
//!         &receiver_pqpk,
//!         &receiver_dh_pk,
//!         &initiator_dh_sk,
//!         Duration::from_secs(3600),
//!         b"example context",
//!         &mut rng,
//!     )
//!     .unwrap();
//!
//!     // Derive a PSK from the PSK message.
//!     let psk_receiver = receive_ecdh_bound_psq(
//!         &receiver_pqsk,
//!         &receiver_pqpk,
//!         &receiver_dh_sk,
//!         &ecdh_psk_message,
//!         b"example context",
//!     )
//!     .unwrap();
//!
//!     assert_eq!(psk_initiator, psk_receiver);
//! }
//! ```
//!

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
    OsError,
}

impl From<libcrux_kem::Error> for Error {
    fn from(_value: libcrux_kem::Error) -> Self {
        Self::CryptoError
    }
}

const PSK_LENGTH: usize = 32;
type Psk = [u8; PSK_LENGTH];

pub mod ecdh_binder;
pub mod psq;
