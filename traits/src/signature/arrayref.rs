pub trait Sign<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    // TODO: should this be called `private_key` or `sk`?
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        sign_aux: SignAux,
    ) -> Result<(), SignError>;
}

pub trait Verify<VerifyAux, const PUBLIC_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        verify_aux: VerifyAux,
    ) -> Result<(), VerifyError>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for SignError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            SignError::InvalidPayloadLength => "the length of the provided payload is invalid",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The provided signature is invalid.
    InvalidSignature,
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            VerifyError::InvalidSignature => "the provided signature is invalid",
            VerifyError::InvalidPayloadLength => "the length of the provided payload is invalid",
            VerifyError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

// No auxiliary information
pub trait SignNoAux<const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError>;
}

impl<
        'a,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Sign<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > SignNoAux<PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError> {
        <Self as Sign<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            signature,
            &(),
        )
    }
}

// No auxiliary information
pub trait VerifyNoAux<const PUBLIC_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;
}

impl<
        'a,
        const PUBLIC_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Verify<&'a (), PUBLIC_KEY_LEN, SIGNATURE_LEN>,
    > VerifyNoAux<PUBLIC_KEY_LEN, SIGNATURE_LEN> for T
{
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        <Self as Verify<&'a (), PUBLIC_KEY_LEN, SIGNATURE_LEN>>::verify(
            payload,
            public_key,
            signature,
            &(),
        )
    }
}
