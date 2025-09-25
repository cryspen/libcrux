// TODO: Docs

use super::arrayref;
use libcrux_secrets::U8;

pub trait ECDHSlice {
    fn generate_secret(secret: &mut [U8], rand: &[U8]) -> Result<(), ECDHError>;
    fn secret_to_public(public: &mut [u8], secret: &[U8]) -> Result<(), ECDHError>;
    fn derive_ecdh(derived: &mut [U8], public: &[u8], secret: &[U8]) -> Result<(), ECDHError>;
    fn validate_secret(secret: &[U8]) -> Result<(), ECDHError>;
}

#[derive(Debug)]
pub enum InvalidLengthError {
    Rand,
    Secret,
    Public,
}

#[derive(Debug)]
pub enum ECDHError {
    GenerateSecret,
    SecretToPublic,
    Derive,
    ValidateSecret,
    InvalidLength(InvalidLengthError),
}

/// Implements [`ECDHSlice`] for any [`arrayref::ECDHArrayref`]
#[macro_export]
macro_rules! impl_ecdh_slice_trait {
    ($type:ty => $rand_len:expr, $sk_len:expr, $pk_len:expr) => {
        impl $crate::ecdh::slice::ECDHSlice for $type {
            fn generate_secret(secret: &mut [U8], rand: &[U8]) -> Result<(), $crate::ecdh::slice::ECDHError> {
                let secret: &mut [U8; $sk_len] = secret
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Secret))?;

                let rand: &[U8; $rand_len] = rand
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Rand))?;

                <$type as $crate::ecdh::arrayref::ECDHArrayref<$rand_len, $sk_len, $pk_len>>::generate_secret(secret, rand)
                .map_err($crate::ecdh::slice::ECDHError::from)
            }

            fn secret_to_public(public: &mut [u8], secret: &[U8]) -> Result<(), $crate::ecdh::slice::ECDHError> {
                let secret: &[U8; $sk_len] = secret
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Secret))?;

                let public: &mut [u8; $pk_len] = public
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Public))?;

                <$type as $crate::ecdh::arrayref::ECDHArrayref<$rand_len, $sk_len, $pk_len>>::secret_to_public(public, secret)
                .map_err($crate::ecdh::slice::ECDHError::from)
            }

            fn derive_ecdh(derived: &mut [U8], public: &[u8], secret: &[U8]) -> Result<(), $crate::ecdh::slice::ECDHError> {
                let derived: &mut [U8; $pk_len] = derived
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Public))?;

                let secret: &[U8; $sk_len] = secret
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Secret))?;

                let public: &[u8; $pk_len] = public
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Public))?;

                <$type as $crate::ecdh::arrayref::ECDHArrayref<$rand_len, $sk_len, $pk_len>>::derive_ecdh(derived, public, secret)
                .map_err($crate::ecdh::slice::ECDHError::from)
            }

            fn validate_secret(secret: &[U8]) -> Result<(), $crate::ecdh::slice::ECDHError> {
                let secret: &[U8; $sk_len] = secret
                .try_into()
                .map_err(|_|
                    $crate::ecdh::slice::ECDHError::InvalidLength($crate::ecdh::slice::InvalidLengthError::Secret))?;

                <$type as $crate::ecdh::arrayref::ECDHArrayref<$rand_len, $sk_len, $pk_len>>::validate_secret(secret)
                .map_err($crate::ecdh::slice::ECDHError::from)
            }
        }
    };
}

pub use impl_ecdh_slice_trait;

impl From<arrayref::ECDHError> for ECDHError {
    fn from(value: arrayref::ECDHError) -> Self {
        match value {
            arrayref::ECDHError::GenerateSecret => ECDHError::GenerateSecret,
            arrayref::ECDHError::SecretToPublic => ECDHError::SecretToPublic,
            arrayref::ECDHError::Derive => ECDHError::Derive,
            arrayref::ECDHError::ValidateSecret => ECDHError::ValidateSecret,
        }
    }
}

impl core::fmt::Display for ECDHError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            ECDHError::GenerateSecret => "error generating ECDH secret value",
            ECDHError::SecretToPublic => {
                "error transforming secret ECDH value to public ECDH value"
            }
            ECDHError::Derive => "error deriving ECDH shared secret",
            ECDHError::ValidateSecret => "invalid ECDH secret value",
            ECDHError::InvalidLength(invalid_length_error) => match invalid_length_error {
                InvalidLengthError::Rand => "the provided randomness buffer has the wrong length",
                InvalidLengthError::Secret => {
                    "the provided secret value buffer has the wrong length"
                }
                InvalidLengthError::Public => {
                    "the provided public value buffer has the wrong length"
                }
            },
        };

        f.write_str(text)
    }
}
