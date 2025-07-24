pub trait Signature<Config> {
    fn sign(
        payload: &[u8],
        private_key: &[u8],
        signature: &mut [u8],
        config: Config,
    ) -> Result<(), SignError>;
    fn verify(payload: &[u8], public_key: &[u8], signature: &[u8]) -> Result<(), VerifyError>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    InvalidPrivateKeyLength,
    InvalidSignatureBufferLength,
    InvalidPayloadLength,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    InvalidPayloadLength,
    InvalidPublicKeyLength,
    InvalidSignatureBufferLength,
    InvalidSignature,
}

impl From<super::arrayref::SignError> for SignError {
    fn from(e: super::arrayref::SignError) -> Self {
        match e {
            super::arrayref::SignError::InvalidPayloadLength => Self::InvalidPayloadLength,
        }
    }
}
impl From<super::arrayref::VerifyError> for VerifyError {
    fn from(e: super::arrayref::VerifyError) -> Self {
        match e {
            super::arrayref::VerifyError::InvalidSignature => Self::InvalidSignature,
            super::arrayref::VerifyError::InvalidPayloadLength => Self::InvalidPayloadLength,
        }
    }
}

#[macro_export]
macro_rules! impl_signature_slice_trait {
    ($type:ty => $pk_len:expr, $sk_len:expr, $sig_len:expr, $config:ty, $config_param:ident) => {
        impl $crate::signature::slice::Signature<$config> for $type {
            fn sign(
                payload: &[u8],
                private_key: &[u8],
                signature: &mut [u8],
                $config_param: $config,
            ) -> Result<(), $crate::signature::slice::SignError> {
                let private_key: &[u8; $sk_len] = private_key
                    .try_into()
                    .map_err(|_| $crate::signature::slice::SignError::InvalidPrivateKeyLength)?;

                let signature: &mut [u8; $sig_len] = signature.try_into().map_err(|_| {
                    $crate::signature::slice::SignError::InvalidSignatureBufferLength
                })?;

                <$type as $crate::signature::arrayref::Signature<
                    $config,
                    $pk_len,
                    $sk_len,
                    $sig_len,
                >>::sign(payload, private_key, signature, $config_param)
                .map_err($crate::signature::slice::SignError::from)
            }
            fn verify(
                payload: &[u8],
                public_key: &[u8],
                signature: &[u8],
            ) -> Result<(), $crate::signature::slice::VerifyError> {
                let public_key: &[u8; $pk_len] = public_key
                    .try_into()
                    .map_err(|_| $crate::signature::slice::VerifyError::InvalidPublicKeyLength)?;

                let signature: &[u8; $sig_len] = signature.try_into().map_err(|_| {
                    $crate::signature::slice::VerifyError::InvalidSignatureBufferLength
                })?;

                <$type as $crate::signature::arrayref::Signature<
                    $config,
                    $pk_len,
                    $sk_len,
                    $sig_len,
                >>::verify(payload, public_key, signature)
                .map_err($crate::signature::slice::VerifyError::from)
            }
        }
    };
}
pub use impl_signature_slice_trait;
