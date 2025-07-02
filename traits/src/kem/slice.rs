use super::arrayref;

pub trait Kem {
    /// Generate a pair of encapsulation and decapsulation keys.
    fn keygen(ek: &mut [u8], dk: &mut [u8], rand: &[u8]) -> Result<(), KeyGenError>;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encaps(ct: &mut [u8], ss: &mut [u8], ek: &[u8], rand: &[u8]) -> Result<(), EncapsError>;

    /// Decapsulate a shared secret.
    fn decaps(ss: &mut [u8], ct: &[u8], dk: &[u8]) -> Result<(), DecapsError>;
}

/// Error generating key with provided randomness
#[derive(thiserror::Error, Debug)]
pub enum KeyGenError {
    #[doc = "Error generating key with provided randomness"]
    #[error("error generating key with provided randomness")]
    InvalidRandomness,
    #[doc = "The provided randomness has the wrong length"]
    #[error("the provided randomness has the wrong length")]
    InvalidRandomnessLength,
    #[doc = "The provided encapsulation key has the wrong length"]
    #[error("the provided encapsulation key has the wrong length")]
    InvalidEncapsKeyLength,
    #[doc = "The provided decapulation key has the wrong length"]
    #[error("the provided decapulation key has the wrong length")]
    InvalidDecapsKeyLength,
    #[doc = "An unknown error occurred"]
    #[error("an unknown error occurred")]
    Unknown,
}

/// Error indicating that encapsulating failed
#[derive(thiserror::Error, Debug)]
pub enum EncapsError {
    #[doc = "Encapsulation key is invalid"]
    #[error("encapsulation key is invalid")]
    InvalidEncapsKey,
    #[doc = "Error encapsulating key with provided randomness"]
    #[error("error encapsulating key with provided randomness")]
    InvalidRandomness,
    #[doc = "The provided randomness has the wrong length"]
    #[error("the provided randomness has the wrong length")]
    InvalidRandomnessLength,
    #[doc = "The provided encapsulation key has the wrong length"]
    #[error("the provided encapsulation key has the wrong length")]
    InvalidEncapsKeyLength,
    #[doc = "The provided ciphertext has the wrong length"]
    #[error("the provided ciphertext has the wrong length")]
    InvalidCipertextLength,
    #[doc = "The provided shared secret has the wrong length"]
    #[error("the provided shared secret has the wrong length")]
    InvalidSharedSecretLength,
    #[doc = "An unknown error occurred"]
    #[error("an unknown error occurred")]
    Unknown,
}

/// Error indicating that decapsulating failed
#[derive(thiserror::Error, Debug)]
pub enum DecapsError {
    #[doc = "Ciphertext key is invalid"]
    #[error("ciphertext key is invalid")]
    InvalidCipertext,
    #[doc = "Decapsulation key is invalid"]
    #[error("decapsulation key is invalid")]
    InvalidDecapsKey,
    #[doc = "The provided decapulation key has the wrong length"]
    #[error("the provided decapulation key has the wrong length")]
    InvalidDecapsKeyLength,
    #[doc = "The provided ciphertext has the wrong length"]
    #[error("the provided ciphertext has the wrong length")]
    InvalidCipertextLength,
    #[doc = "The provided shared secret has the wrong length"]
    #[error("the provided shared secret has the wrong length")]
    InvalidSharedSecretLength,
    #[doc = "An unknown error occurred"]
    #[error("an unknown error occurred")]
    Unknown,
}

impl From<super::arrayref::KeyGenError> for KeyGenError {
    fn from(value: super::arrayref::KeyGenError) -> Self {
        match value {
            super::arrayref::KeyGenError::InvalidRandomness => KeyGenError::InvalidRandomness,
            super::arrayref::KeyGenError::Unknown => KeyGenError::Unknown,
        }
    }
}

impl From<super::arrayref::EncapsError> for EncapsError {
    fn from(value: super::arrayref::EncapsError) -> Self {
        match value {
            arrayref::EncapsError::InvalidEncapsKey => EncapsError::InvalidEncapsKey,
            arrayref::EncapsError::InvalidRandomness => EncapsError::InvalidRandomness,
            arrayref::EncapsError::Unknown => EncapsError::Unknown,
        }
    }
}

impl From<super::arrayref::DecapsError> for DecapsError {
    fn from(value: super::arrayref::DecapsError) -> Self {
        match value {
            arrayref::DecapsError::InvalidCipertext => DecapsError::InvalidCipertext,
            arrayref::DecapsError::InvalidDecapsKey => DecapsError::InvalidDecapsKey,
            arrayref::DecapsError::Unknown => DecapsError::Unknown,
        }
    }
}

#[macro_export]
macro_rules! impl_trait {
    ($name:ty => $ek:expr, $dk:expr, $ct:expr, $ss:expr, $rand_kg:expr, $rand_encaps:expr) => {
        impl $crate::kem::slice::Kem for $name {
            fn keygen(ek: &mut [u8], dk: &mut [u8], rand: &[u8]) -> Result<(), $crate::kem::slice::KeyGenError> {
                let ek : &mut [u8; $ek] = ek
                    .try_into()
                    .map_err(|_| $crate::kem::slice::KeyGenError::InvalidEncapsKeyLength)?;
                let dk : &mut [u8; $dk] = dk
                    .try_into()
                    .map_err(|_| $crate::kem::slice::KeyGenError::InvalidDecapsKeyLength)?;
                let rand : &[u8; $rand_kg] = rand
                    .try_into()
                    .map_err(|_| $crate::kem::slice::KeyGenError::InvalidRandomnessLength)?;

                <$name as $crate::kem::arrayref::Kem<$ek, $dk, $ct, $ss, $rand_kg, $rand_encaps>>::keygen(ek, dk, rand).map_err($crate::kem::slice::KeyGenError::from)
            }

            fn encaps(ct: &mut [u8], ss: &mut [u8], ek: &[u8], rand: &[u8]) -> Result<(), $crate::kem::slice::EncapsError>{
                let ct : &mut [u8; $ct] = ct
                    .try_into()
                    .map_err(|_| $crate::kem::slice::EncapsError::InvalidCipertextLength)?;
                let ss : &mut [u8; $ss] = ss
                    .try_into()
                    .map_err(|_| $crate::kem::slice::EncapsError::InvalidSharedSecretLength)?;
                let ek : & [u8; $ek] = ek
                    .try_into()
                    .map_err(|_| $crate::kem::slice::EncapsError::InvalidEncapsKeyLength)?;
                let rand : &[u8; $rand_encaps] = rand
                    .try_into()
                    .map_err(|_| $crate::kem::slice::EncapsError::InvalidRandomnessLength)?;


                <$name as $crate::kem::arrayref::Kem<$ek, $dk, $ct, $ss, $rand_kg, $rand_encaps>>::encaps(ct, ss, ek,rand).map_err($crate::kem::slice::EncapsError::from)
            }

            fn decaps(ss: &mut [u8], ct: &[u8], dk: &[u8]) -> Result<(), $crate::kem::slice::DecapsError> {
                let ss : &mut [u8; $ss] = ss
                    .try_into()
                    .map_err(|_| $crate::kem::slice::DecapsError::InvalidSharedSecretLength)?;
                let ct : &[u8; $ct] = ct
                    .try_into()
                    .map_err(|_| $crate::kem::slice::DecapsError::InvalidCipertextLength)?;
                let dk : &[u8; $dk] = dk
                    .try_into()
                    .map_err(|_| $crate::kem::slice::DecapsError::InvalidDecapsKeyLength)?;


                <$name as $crate::kem::arrayref::Kem<$ek, $dk, $ct, $ss, $rand_kg, $rand_encaps>>::decaps(ss, ct, dk).map_err($crate::kem::slice::DecapsError::from)

            }

        }
    };
}

pub use impl_trait;
