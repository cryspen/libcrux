#![no_std]

#[cfg(feature = "hacl")]
pub use libcrux_hacl_rs::curve25519_51 as hacl;

#[cfg(feature = "hacl")]
mod impl_hacl;

#[cfg(feature = "hacl")]
pub use impl_hacl::{ecdh, secret_to_public};

/// The length of Curve25519 secret keys.
pub const SK_LEN: usize = 32;

/// The length of Curve25519 public keys.
pub const PK_LEN: usize = 32;

/// The length of Curve25519 shared keys.
pub const SHK_LEN: usize = 32;

/// Indicates that an error occurred
pub struct Error;

/// This trait is implemented by the backing implementations.
/// Only used for implementation agility.
pub trait Curve25519 {
    /// Computes a public key from a secret key.
    fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]);

    /// Computes the scalar multiplication between the provided public and secret keys. Returns an
    /// error if the result is 0.
    fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error>;
}
