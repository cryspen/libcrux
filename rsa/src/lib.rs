#[cfg(feature = "hacl")]
mod hacl {
    pub(crate) mod rsapss;

    use libcrux_hacl_rs::streaming_types;
    use libcrux_sha2::hacl as hash_sha2;
}

pub enum DigestAlgorithm {
    Sha2_256,
    Sha2_384,
    Sha2_512,
}

#[derive(Debug)]
pub enum Error {
    SaltTooLarge,
    MessageTooLarge,
    SigningFailed,
    VerificationFailed,
}

#[cfg(feature = "hacl")]
mod impl_hacl;
