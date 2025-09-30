#![no_std]

pub use libcrux_hacl_rs::curve25519_51 as hacl;

mod impl_hacl;

pub mod ecdh_api;

#[cfg(feature = "kem-api")]
pub mod kem_api;

pub use impl_hacl::ecdh;

/// The length of Curve25519 secret keys.
pub const DK_LEN: usize = 32;

/// The length of Curve25519 public keys.
pub const EK_LEN: usize = 32;

/// The length of Curve25519 shared keys.
pub const SS_LEN: usize = 32;

/// Indicates that an error occurred
pub struct Error;

/// This trait is implemented by the backing implementations.
/// Only used for ensuring implementations follow the same interface, not really consumed.
#[allow(dead_code)]
trait Curve25519 {
    /// Computes a public key from a secret key.
    fn secret_to_public(pk: &mut [u8; EK_LEN], sk: &[u8; DK_LEN]);

    /// Computes the scalar multiplication between the provided public and secret keys. Returns an
    /// error if the result is 0.
    fn ecdh(out: &mut [u8; SS_LEN], pk: &[u8; EK_LEN], sk: &[u8; DK_LEN]) -> Result<(), Error>;
}

pub struct X25519;

/// Clamp a scalar.
fn clamp(scalar: &mut [u8; DK_LEN]) {
    // We clamp the key already to make sure it can't be misused.
    scalar[0] &= 248u8;
    scalar[31] &= 127u8;
    scalar[31] |= 64u8;
}
