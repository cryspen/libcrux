//! Common types

macro_rules! impl_struct {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name<const SIZE: usize> {
            pub(crate) value: [u8; SIZE],
        }

        impl<const SIZE: usize> $name<SIZE> {
            /// Build
            pub fn new(value: [u8; SIZE]) -> Self {
                Self { value }
            }

            /// A reference to the raw byte slice.
            pub fn as_slice(&self) -> &[u8] {
                &self.value
            }

            /// A mutable reference to the raw byte slice.
            pub fn as_mut_slice(&mut self) -> &mut [u8] {
                &mut self.value
            }

            /// A reference to the raw byte array.
            pub fn as_raw(&self) -> &[u8; SIZE] {
                &self.value
            }

            /// A mutable reference to the raw byte array.
            pub fn as_raw_mut(&mut self) -> &mut [u8; SIZE] {
                &mut self.value
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
