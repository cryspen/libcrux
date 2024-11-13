#[cfg(feature = "hacl")]
pub use libcrux_hacl_rs::curve25519_51 as hacl;

#[cfg(feature = "hacl")]
mod impl_hacl;

#[cfg(feature = "portable_hacl")]
pub use impl_hacl::HaclCurve25519 as Impl;

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
trait Curve25519 {
    /// Computes a public key from a secret key.
    fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]);

    /// Computes the scalar multiplication between the provided public and secret keys. Returns an
    /// error if the result is 0.
    fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error>;
}

/// Computes and writes the public key from the secret key `sk` and writes it into `pk`.
pub fn secret_to_public(pk: &mut [u8; PK_LEN], sk: &[u8; SK_LEN]) {
    Impl::secret_to_public(pk, sk)
}

/// Performs the ECDH computation and writes the key shared betweem `pk` and `sk` into `shk`.
pub fn ecdh(out: &mut [u8; SHK_LEN], pk: &[u8; PK_LEN], sk: &[u8; SK_LEN]) -> Result<(), Error> {
    Impl::ecdh(out, pk, sk)
}
