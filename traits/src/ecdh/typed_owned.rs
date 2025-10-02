//! This module provides a strongly typed ECDH API in terms of pairs
//! of corresponding ECDH secret and public values.

use crate::ecdh::owned::{self, GenerateSecretError, SecretToPublicError};

/// The types associated with an ECDH implementation.
pub trait EcdhTypes {
    type Secret;
    type Public;
    type Randomness;
    type Derived;
}

/// An pair of corresponding ECDH secret and public values, generic
/// over the underlying elliptic curve.
pub struct Pair<Algorithm: EcdhTypes> {
    secret: Algorithm::Secret,
    public: Algorithm::Public,
}

impl<Algorithm: Ecdh> Pair<Algorithm> {
    /// Generate a new pair of ECDH secret and public values.
    pub fn generate(rand: &Algorithm::Randomness) -> Result<Self, owned::GenerateSecretError> {
        let (public, secret) = Algorithm::generate_pair(&rand)?;
        Ok(Pair { secret, public })
    }

    /// Returns the secret component of the pair.
    pub fn secret(&self) -> &Algorithm::Secret {
        &self.secret
    }

    /// Returns the public component of the pair.
    pub fn public(&self) -> &Algorithm::Public {
        &self.public
    }

    /// Derive an ECDH shared secret value from the pairs secret value
    /// and a given ECDH public value.
    pub fn derive_ecdh(
        &self,
        public: &Algorithm::Public,
    ) -> Result<Algorithm::Derived, owned::DeriveError> {
        Algorithm::derive_ecdh(public, self.secret())
    }
}

/// Trait implementing ECDH operations over a given elliptic curve.
///
/// Mostly for `libcrux`-internal use.
pub trait Ecdh: EcdhTypes + Sized {
    /// Generate a Diffie-Hellman secret value.
    /// It is the responsibility of the caller to ensure  that the `rand` argument is actually
    /// random.
    fn generate_secret(rand: &Self::Randomness) -> Result<Self::Secret, GenerateSecretError>;

    /// Derive a Diffie-Hellman public value from a secret value.
    fn secret_to_public(secret: &Self::Secret) -> Result<Self::Public, SecretToPublicError>;

    /// Generate a Diffie-Hellman secret value and derive the
    /// corresponding public value in one step.
    fn generate_pair(
        rand: &Self::Randomness,
    ) -> Result<(Self::Public, Self::Secret), GenerateSecretError> {
        let secret = Self::generate_secret(rand)?;
        let public = Self::secret_to_public(&secret).map_err(|_| GenerateSecretError::Unknown)?;
        Ok((public, secret))
    }

    /// Derive a Diffie-Hellman shared secret from a public and a
    /// secret value.
    ///
    /// This value is NOT (!) safe for use as a key and needs to be processed in a round of key
    /// derivation, to ensure both that the output is uniformly random and that unkown key share
    /// attacks can not happen.
    fn derive_ecdh(
        public: &Self::Public,
        secret: &Self::Secret,
    ) -> Result<Self::Derived, owned::DeriveError>;

    /// Check the validity of a Diffie-Hellman secret value.
    fn validate_secret(secret: &Self::Secret) -> Result<(), owned::ValidateSecretError>;
}

#[macro_export]
/// This macro implements the traits `ecdh::typed_owned::EcdhTypes` and `ecdh::typed_owned::Ecdh` from an
/// implementation of the `ecdh::owned::EcdhOwned` trait.
///
/// - `$ty` should provide an underlying implementation of `ecdh::owned::EcdhOwned`
/// - `$randomness_len` should be the length in bytes of randomness for ECDH secret
///   generation in the underlying implementation
/// - `$secret_len` should be the length in bytes of ECDH secret values in
///   the underlying implementation
/// - `$public_len` should be the length in bytes of ECDH public values in
///   the underlying implementation (this is also the length of ECDH
///   shared secrets)
macro_rules! impl_ecdh_typed_owned {
    ($ty:ty => $randomness_len:expr, $secret_len:expr, $public_len:expr) => {
        impl $crate::ecdh::typed_owned::EcdhTypes for $ty {
            type Secret = [$crate::libcrux_secrets::U8; $secret_len];
            type Public = [u8; $public_len];
            type Randomness = [$crate::libcrux_secrets::U8; $randomness_len];
            type Derived = [$crate::libcrux_secrets::U8; $public_len];
        }

        impl $crate::ecdh::typed_owned::Ecdh for $ty {
            fn generate_secret(
                rand: &Self::Randomness,
            ) -> Result<Self::Secret, $crate::ecdh::owned::GenerateSecretError> {
                <$ty as $crate::ecdh::owned::EcdhOwned<$randomness_len,
                                                               $secret_len,
                                                               $public_len
                                                               >>::generate_secret(rand)
            }

            fn secret_to_public(
                secret: &Self::Secret,
            ) -> Result<Self::Public, $crate::ecdh::owned::SecretToPublicError> {
                <$ty as $crate::ecdh::owned::EcdhOwned<$randomness_len,
                                                               $secret_len,
                                                               $public_len
                                                               >>::secret_to_public(secret)
            }

            fn derive_ecdh(
                public: &Self::Public,
                secret: &Self::Secret,
            ) -> Result<Self::Derived, $crate::ecdh::owned::DeriveError> {
                <$ty as $crate::ecdh::owned::EcdhOwned<$randomness_len,
                                                               $secret_len,
                                                               $public_len
                                                               >>::derive_ecdh(public, secret)
            }

            fn validate_secret(
                secret: &Self::Secret,
            ) -> Result<(), $crate::ecdh::owned::ValidateSecretError> {
                <$ty as $crate::ecdh::owned::EcdhOwned<$randomness_len,
                                                               $secret_len,
                                                               $public_len
                                                               >>::validate_secret(secret)
            }
        }
    };
}

pub use impl_ecdh_typed_owned;
