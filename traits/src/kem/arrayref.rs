pub trait Kem<
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
>
{
    /// Generate a pair of encapsulation and decapsulation keys.
    fn keygen(
        ek: &mut [u8; EK_LEN],
        dk: &mut [u8; DK_LEN],
        rand: &[u8; RAND_KEYGEN_LEN],
    ) -> Result<(), KeyGenError>;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encaps(
        ct: &mut [u8; CT_LEN],
        ss: &mut [u8; SS_LEN],
        ek: &[u8; EK_LEN],
        rand: &[u8; RAND_ENCAPS_LEN],
    ) -> Result<(), EncapsError>;

    /// Decapsulate a shared secret.
    fn decaps(
        ss: &mut [u8; SS_LEN],
        ct: &[u8; CT_LEN],
        dk: &[u8; DK_LEN],
    ) -> Result<(), DecapsError>;
}

/// Error generating key with provided randomness
#[derive(thiserror::Error, Debug)]
pub enum KeyGenError {
    #[doc = "Error generating key with provided randomness"]
    #[error("error generating key with provided randomness")]
    InvalidRandomness,
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
    #[doc = "An unknown error occurred"]
    #[error("an unknown error occurred")]
    Unknown,
}
