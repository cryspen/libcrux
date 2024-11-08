//! Common types

// XXX:
// - use named structs?
// - add conversion helpers?

macro_rules! impl_struct {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name<const SIZE: usize>(pub [u8; SIZE]);

        impl<const SIZE: usize> $name<SIZE> {
            /// A reference to the raw byte slice.
            pub fn as_slice(&self) -> &[u8] {
                &self.0
            }

            /// The number of bytes
            pub const fn len() -> usize {
                SIZE
            }
        }
    };
}

impl_struct!(MLDSASigningKey, "An ML-DSA signature key.");
impl_struct!(MLDSAVerificationKey, "An ML-DSA verification key.");
impl_struct!(MLDSASignature, "An ML-DSA signature.");

/// An ML-DSA key pair.
pub struct MLDSAKeyPair<const VERIFICATION_KEY_SIZE: usize, const SIGNING_KEY_SIZE: usize> {
    pub signing_key: MLDSASigningKey<SIGNING_KEY_SIZE>,
    pub verification_key: MLDSAVerificationKey<VERIFICATION_KEY_SIZE>,
}

use crate::{constants::*, polynomial::PolynomialRingElement, simd::traits::Operations};

pub(crate) struct Signature<
    SIMDUnit: Operations,
    const COMMITMENT_HASH_SIZE: usize,
    const COLUMNS_IN_A: usize,
    const ROWS_IN_A: usize,
> {
    pub commitment_hash: [u8; COMMITMENT_HASH_SIZE],
    pub signer_response: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    pub hint: [[i32; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A],
}

#[derive(Debug)]
pub enum VerificationError {
    MalformedHintError,
    SignerResponseExceedsBoundError,
    CommitmentHashesDontMatchError,
    ContextTooLongError,
}

#[derive(Debug)]
pub enum SigningError {
    RejectionSamplingError,
    ContextTooLongError,
}
