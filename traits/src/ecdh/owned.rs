//! This module contains the trait and related errors for an ECDH
//! implementation that takes array references as arguments and
//! returns owned arrays.

use super::arrayref;
use super::arrayref::ECDHError;

use libcrux_secrets::{Classify, U8};

/// An Elliptic Curve Diffie-Hellman (ECDH) key exchange.
pub trait ECDHOwned<const RAND_LEN: usize, const SECRET_LEN: usize, const PUBLIC_LEN: usize> {
    /// Generate a Diffie-Hellman secret value.
    /// It is the responsibility of the caller to ensure  that the `rand` argument is actually
    /// random.
    fn generate_secret(rand: &[U8; RAND_LEN]) -> Result<[U8; SECRET_LEN], ECDHError>;

    /// Derive a Diffie-Hellman public value from a secret value.
    fn secret_to_public(secret: &[U8; SECRET_LEN]) -> Result<[u8; PUBLIC_LEN], ECDHError>;

    /// Derive a Diffie-Hellman shared secret from a public and a
    /// secret value.
    fn derive_ecdh(
        public: &[u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<[U8; PUBLIC_LEN], ECDHError>;

    /// Check the validity of a Diffie-Hellman secret value.
    fn validate_secret(secret: &[U8; SECRET_LEN]) -> Result<(), ECDHError>;
}

impl<
        const RAND_LEN: usize,
        const SECRET_LEN: usize,
        const PUBLIC_LEN: usize,
        T: arrayref::ECDHArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN>,
    > ECDHOwned<RAND_LEN, SECRET_LEN, PUBLIC_LEN> for T
{
    fn generate_secret(rand: &[U8; RAND_LEN]) -> Result<[U8; SECRET_LEN], ECDHError> {
        let mut secret = [0u8; SECRET_LEN].classify();
        <Self as arrayref::ECDHArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN>>::generate_secret(
            &mut secret,
            rand,
        )?;
        Ok(secret)
    }

    fn secret_to_public(secret: &[U8; SECRET_LEN]) -> Result<[u8; PUBLIC_LEN], ECDHError> {
        let mut public = [0u8; PUBLIC_LEN];
        <Self as arrayref::ECDHArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN>>::secret_to_public(
            &mut public,
            secret,
        )?;
        Ok(public)
    }

    fn derive_ecdh(
        public: &[u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<[U8; PUBLIC_LEN], ECDHError> {
        let mut derived = [0u8; PUBLIC_LEN].classify();
        <Self as arrayref::ECDHArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN>>::derive_ecdh(
            &mut derived,
            public,
            secret,
        )?;
        Ok(derived)
    }

    fn validate_secret(secret: &[U8; SECRET_LEN]) -> Result<(), ECDHError> {
        <Self as arrayref::ECDHArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN>>::validate_secret(secret)
    }
}
