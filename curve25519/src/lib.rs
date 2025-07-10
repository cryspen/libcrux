#![no_std]

pub use libcrux_hacl_rs::curve25519_51 as hacl;

mod impl_hacl;

pub use impl_hacl::{ecdh, secret_to_public};

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

#[inline(always)]
const fn or(a: u8, b: &u8) -> u8 {
    a | *b
}

impl libcrux_traits::kem::arrayref::Kem<DK_LEN, EK_LEN, EK_LEN, SS_LEN, DK_LEN, DK_LEN> for X25519 {
    fn keygen(
        ek: &mut [u8; DK_LEN],
        dk: &mut [u8; EK_LEN],
        rand: &[u8; DK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::KeyGenError> {
        if rand.iter().fold(0, or) == 0 {
            return Err(libcrux_traits::kem::arrayref::KeyGenError::InvalidRandomness);
        }

        dk.copy_from_slice(rand);
        clamp(dk);
        secret_to_public(ek, dk);
        Ok(())
    }

    fn encaps(
        ct: &mut [u8; EK_LEN],
        ss: &mut [u8; SS_LEN],
        ek: &[u8; EK_LEN],
        rand: &[u8; DK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::EncapsError> {
        if rand.iter().fold(0, or) == 0 {
            return Err(libcrux_traits::kem::arrayref::EncapsError::InvalidRandomness);
        }

        let mut eph_dk = *rand;
        clamp(&mut eph_dk);
        secret_to_public(ct, &eph_dk);

        ecdh(ss, ek, &eph_dk).map_err(|_| libcrux_traits::kem::arrayref::EncapsError::Unknown)
    }

    fn decaps(
        ss: &mut [u8; SS_LEN],
        ct: &[u8; DK_LEN],
        dk: &[u8; EK_LEN],
    ) -> Result<(), libcrux_traits::kem::arrayref::DecapsError> {
        ecdh(ss, ct, dk).map_err(|_| libcrux_traits::kem::arrayref::DecapsError::Unknown)
    }
}

libcrux_traits::kem::slice::impl_trait!(X25519 => EK_LEN, DK_LEN, EK_LEN, EK_LEN, DK_LEN, DK_LEN);

/// Clamp a scalar.
fn clamp(scalar: &mut [u8; DK_LEN]) {
    // We clamp the key already to make sure it can't be misused.
    scalar[0] &= 248u8;
    scalar[31] &= 127u8;
    scalar[31] |= 64u8;
}
