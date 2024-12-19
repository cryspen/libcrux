#![no_std]

#[cfg(not(feature = "expose-hacl"))]
mod hacl {
    pub(crate) mod rsapss;

    use libcrux_hacl_rs::streaming_types;
    use libcrux_sha2::hacl as hash_sha2;
}

#[cfg(feature = "expose-hacl")]
pub mod hacl {
    pub mod rsapss;

    use libcrux_hacl_rs::streaming_types;
    use libcrux_sha2::hacl as hash_sha2;
}

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

#[derive(Debug)]
pub enum Error {
    SaltTooLarge,
    MessageTooLarge,
    VerificationFailed,
    SigningFailed,
}

mod impl_hacl;

pub use impl_hacl::*;
