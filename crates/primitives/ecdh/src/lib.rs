//! # Elliptic Curve Diffie-Hellman (ECDH) key exchange
//!
//! This crate provides a uniform API for elliptic curve Diffie-Hellman
//! key exchange over the following curves:
//!
//! - NIST P-256
//! - Curve25519
//!
//! *TODO*: Explain error types, different APIs.
//!
//! Usage example:
//! ```rust
//! use libcrux_ecdh_new::curve25519::{X25519Pair, RAND_LEN};
//!
//! use rand::RngCore;
//! let mut rng = rand::rng();
//!
//! let mut randomness_a = [0u8; RAND_LEN];
//! let mut randomness_b = [0u8; RAND_LEN];
//!
//! rng.fill_bytes(&mut randomness_a);
//! let x25519_pair_a = X25519Pair::generate(&randomness_a).unwrap();
//!
//! rng.fill_bytes(&mut randomness_b);
//! let x25519_pair_b = X25519Pair::generate(&randomness_b).unwrap();
//!
//! let derived_a = x25519_pair_a.derive_ecdh(x25519_pair_b.public()).unwrap();
//! let derived_b = x25519_pair_b.derive_ecdh(x25519_pair_a.public()).unwrap();
//!
//! assert_eq!(derived_a, derived_b);
//! ```

#[cfg(feature = "p256")]
pub mod p256 {
    //! This module provides an API for ECDH over NIST-P256.
    //!
    //! ```rust
    //! use libcrux_ecdh_new::p256::{P256Pair, RAND_LEN};
    //! use rand::RngCore;
    //!
    //! let mut rng = rand::rng();
    //!
    //! let mut randomness_a = [0u8; RAND_LEN];
    //! let mut randomness_b = [0u8; RAND_LEN];
    //!
    //! rng.fill_bytes(&mut randomness_a);
    //! let p256_pair_a = P256Pair::generate(&randomness_a).unwrap();
    //!
    //! rng.fill_bytes(&mut randomness_b);
    //! let p256_pair_b = P256Pair::generate(&randomness_b).unwrap();
    //!
    //! let derived_a = p256_pair_a.derive_ecdh(p256_pair_b.public()).unwrap();
    //! let derived_b = p256_pair_b.derive_ecdh(p256_pair_a.public()).unwrap();
    //!
    //! assert_eq!(derived_a, derived_b);
    //! ```
    pub use libcrux_p256::ecdh_api::*;

    /// Access low level ECDH APIs via this struct.
    pub use libcrux_p256::P256;
}

#[cfg(feature = "curve25519")]
pub mod curve25519 {
    //! This module provides an API for ECDH over Curve25519.
    //!
    //! ```rust
    //! use libcrux_ecdh_new::curve25519::{X25519Pair, RAND_LEN};
    //!
    //! use rand::RngCore;
    //! let mut rng = rand::rng();
    //!
    //! let mut randomness_a = [0u8; RAND_LEN];
    //! let mut randomness_b = [0u8; RAND_LEN];
    //!
    //! rng.fill_bytes(&mut randomness_a);
    //! let x25519_pair_a = X25519Pair::generate(&randomness_a).unwrap();
    //!
    //! rng.fill_bytes(&mut randomness_b);
    //! let x25519_pair_b = X25519Pair::generate(&randomness_b).unwrap();
    //!
    //! let derived_a = x25519_pair_a.derive_ecdh(x25519_pair_b.public()).unwrap();
    //! let derived_b = x25519_pair_b.derive_ecdh(x25519_pair_a.public()).unwrap();
    //!
    //! assert_eq!(derived_a, derived_b);
    //! ```
    pub use libcrux_curve25519::ecdh_api::*;

    /// Access low level ECDH APIs via this struct.
    pub use libcrux_curve25519::X25519;
}
