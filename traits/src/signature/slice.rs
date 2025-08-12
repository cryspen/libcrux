pub trait Sign<SignAux> {
    fn sign(
        payload: &[u8],
        private_key: &[u8],
        signature: &mut [u8],
        aux: SignAux,
    ) -> Result<(), SignError>;
}
pub trait Verify<VerifyAux> {
    fn verify(
        payload: &[u8],
        public_key: &[u8],
        signature: &[u8],
        aux: VerifyAux,
    ) -> Result<(), VerifyError>;
}

pub trait SignNoAux {
    fn sign(payload: &[u8], private_key: &[u8], signature: &mut [u8]) -> Result<(), SignError>;
}

impl<T: Sign<()>> SignNoAux for T {
    fn sign(payload: &[u8], private_key: &[u8], signature: &mut [u8]) -> Result<(), SignError> {
        <Self as Sign<()>>::sign(payload, private_key, signature, ())
    }
}

pub trait VerifyNoAux {
    fn verify(payload: &[u8], public_key: &[u8], signature: &[u8]) -> Result<(), VerifyError>;
}
impl<'a, T: Verify<()>> VerifyNoAux for T {
    fn verify(payload: &[u8], public_key: &[u8], signature: &[u8]) -> Result<(), VerifyError> {
        <Self as Verify<()>>::verify(payload, public_key, signature, ())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The length of the provided private key is invalid.
    InvalidPrivateKeyLength,
    /// The length of the provided signature buffer is invalid.
    InvalidSignatureBufferLength,
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for SignError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            SignError::InvalidPrivateKeyLength => {
                "the length of the provided private key is invalid"
            }
            SignError::InvalidSignatureBufferLength => {
                "the length of the provided signature buffer is invalid"
            }
            SignError::InvalidPayloadLength => "the length of the provided payload is invalid",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// The length of the provided public key is invalid.
    InvalidPublicKeyLength,
    /// The length of the provided signature buffer is invalid.
    InvalidSignatureBufferLength,
    /// The provided signature is invalid.
    InvalidSignature,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            VerifyError::InvalidSignature => "the provided signature is invalid",
            VerifyError::InvalidPublicKeyLength => {
                "the length of the provided public key is invalid"
            }
            VerifyError::InvalidSignatureBufferLength => {
                "the length of the provided signature buffer is invalid"
            }
            VerifyError::InvalidPayloadLength => "the length of the provided payload is invalid",
            VerifyError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error_in_core")]
mod error_in_core {

    impl core::error::Error for super::SignError {}
    impl core::error::Error for super::VerifyError {}
}

impl From<super::arrayref::SignError> for SignError {
    fn from(e: super::arrayref::SignError) -> Self {
        match e {
            super::arrayref::SignError::InvalidPayloadLength => Self::InvalidPayloadLength,
            super::arrayref::SignError::LibraryError => Self::LibraryError,
        }
    }
}
impl From<super::arrayref::VerifyError> for VerifyError {
    fn from(e: super::arrayref::VerifyError) -> Self {
        match e {
            super::arrayref::VerifyError::InvalidSignature => Self::InvalidSignature,
            super::arrayref::VerifyError::InvalidPayloadLength => Self::InvalidPayloadLength,
            super::arrayref::VerifyError::LibraryError => Self::LibraryError,
        }
    }
}

/// Implements [`Sign`] for any [`arrayref::Sign`](crate::signature::arrayref::Sign)
#[macro_export]
macro_rules! impl_signature_slice_trait {
    ($type:ty => $sk_len:expr, $sig_len:expr, $sign_aux:ty, $sign_aux_param:tt) => {
        impl $crate::signature::slice::Sign<$sign_aux> for $type {
            fn sign(
                payload: &[u8],
                private_key: &[u8],
                signature: &mut [u8],
                $sign_aux_param: $sign_aux,
            ) -> Result<(), $crate::signature::slice::SignError> {
                let private_key: &[u8; $sk_len] = private_key
                    .try_into()
                    .map_err(|_| $crate::signature::slice::SignError::InvalidPrivateKeyLength)?;

                let signature: &mut [u8; $sig_len] = signature.try_into().map_err(|_| {
                    $crate::signature::slice::SignError::InvalidSignatureBufferLength
                })?;

                <$type as $crate::signature::arrayref::Sign<$sign_aux, $sk_len, $sig_len>>::sign(
                    payload,
                    private_key,
                    signature,
                    $sign_aux_param,
                )
                .map_err($crate::signature::slice::SignError::from)
            }
        }
    };
}
/// Implements [`Verify`] for any [`arrayref::Verify`](crate::signature::arrayref::Verify)
#[macro_export]
macro_rules! impl_verify_slice_trait {
    ($type:ty => $pk_len:expr, $sig_len:expr, $verify_aux:ty, $verify_aux_param:tt) => {
        impl $crate::signature::slice::Verify<$verify_aux> for $type {
            fn verify(
                payload: &[u8],
                public_key: &[u8],
                signature: &[u8],
                $verify_aux_param: $verify_aux,
            ) -> Result<(), $crate::signature::slice::VerifyError> {
                let public_key: &[u8; $pk_len] = public_key
                    .try_into()
                    .map_err(|_| $crate::signature::slice::VerifyError::InvalidPublicKeyLength)?;

                let signature: &[u8; $sig_len] = signature.try_into().map_err(|_| {
                    $crate::signature::slice::VerifyError::InvalidSignatureBufferLength
                })?;

                <$type as $crate::signature::arrayref::Verify<
                                    $verify_aux,
                                    $pk_len,
                                    $sig_len,
                                >>::verify(payload, public_key, signature, $verify_aux_param)
                                .map_err($crate::signature::slice::VerifyError::from)
            }
        }
    };
}
pub use impl_signature_slice_trait;
pub use impl_verify_slice_trait;
