#![no_std]

#[cfg(not(feature = "expose-hacl"))]
mod hacl {
    pub(crate) mod rsapss;

    use libcrux_hacl_rs::streaming_types;
    use libcrux_sha2::hacl as hash_sha2;
}

/// The hacl-rs code for RSA signatures
#[cfg(feature = "expose-hacl")]
pub mod hacl {
    /// The RSA-PSS signature code.
    pub mod rsapss;

    use libcrux_hacl_rs::streaming_types;
    use libcrux_sha2::hacl as hash_sha2;
}

/// The hash algorithm used for signing or verifying.
#[derive(Clone, Copy, Debug)]
pub enum DigestAlgorithm {
    Sha2_256,
    Sha2_384,
    Sha2_512,
}

impl DigestAlgorithm {
    // using u8 so it can be safely coerced into any uint type
    fn hash_len(&self) -> u8 {
        match self {
            DigestAlgorithm::Sha2_256 => 32,
            DigestAlgorithm::Sha2_384 => 48,
            DigestAlgorithm::Sha2_512 => 64,
        }
    }
}

/// Represents errors that occurred during signing or verifying.
#[derive(Debug)]
pub enum Error {
    /// Indicates that the salt is too large.
    SaltTooLarge,

    /// Indicates that the message is too large.
    MessageTooLarge,

    /// Indicates that the verification of a signature failed.
    VerificationFailed,

    /// Indicates that signing a message failed.
    SigningFailed,
}

mod impl_hacl;

pub use impl_hacl::*;
