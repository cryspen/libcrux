#![no_std]

pub use libcrux_hacl_rs::curve25519_51 as hacl;

mod impl_hacl;

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
/// Only used for ensuring implementations follow the same interface, not really consumed.
#[allow(dead_code)]
trait Curve25519 {
    /// Computes a public key from a secret key.
    fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]);

    /// Computes the scalar multiplication between the provided public and secret keys. Returns an
    /// error if the result is 0.
    fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error>;
}

pub struct Kem;

impl libcrux_traits::kem::arrayref::Kem<SK_LEN, PK_LEN, PK_LEN, SHK_LEN, SK_LEN, SK_LEN> for Kem {
    fn keygen(
        ek: &mut [u8; SK_LEN],
        dk: &mut [u8; PK_LEN],
        rand: &[u8; SK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::KeyGenError> {
        dk.copy_from_slice(rand);
        clamp(dk);
        secret_to_public(ek, dk);
        Ok(())
    }

    fn encaps(
        ct: &mut [u8; PK_LEN],
        ss: &mut [u8; SHK_LEN],
        ek: &[u8; PK_LEN],
        rand: &[u8; SK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::EncapsError> {
        let mut eph_dk = *rand;
        clamp(&mut eph_dk);
        secret_to_public(ct, &eph_dk);

        ecdh(ss, ek, &eph_dk).map_err(|_| libcrux_traits::kem::arrayref::EncapsError::Unknown)
    }

    fn decaps(
        ss: &mut [u8; SHK_LEN],
        ct: &[u8; SK_LEN],
        dk: &[u8; PK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::DecapsError> {
        ecdh(ss, ct, dk).map_err(|_| libcrux_traits::kem::arrayref::DecapsError::Unknown)
    }
}

libcrux_traits::kem::slice::impl_trait!(Kem => PK_LEN, SK_LEN, PK_LEN, PK_LEN, SK_LEN, SK_LEN);

/// Clamp a scalar.
fn clamp(scalar: &mut [u8; SK_LEN]) {
    // We clamp the key already to make sure it can't be misused.
    scalar[0] &= 248u8;
    scalar[31] &= 127u8;
    scalar[31] |= 64u8;
}
