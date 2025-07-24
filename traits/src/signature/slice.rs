pub trait Signature<SignAux, VerifyAux> {
    fn sign(
        payload: &[u8],
        private_key: &[u8],
        signature: &mut [u8],
        aux: SignAux,
    ) -> Result<(), SignError>;
    fn verify(
        payload: &[u8],
        public_key: &[u8],
        signature: &[u8],
        aux: VerifyAux,
    ) -> Result<(), VerifyError>;
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
    ($type:ty => $pk_len:expr, $sk_len:expr, $sig_len:expr, $sign_aux:ty, $sign_aux_param:tt, $verify_aux:ty, $verify_aux_param:tt) => {
        impl $crate::signature::slice::Signature<$sign_aux, $verify_aux> for $type {
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

                <$type as $crate::signature::arrayref::Signature<
                    $sign_aux,
                    $verify_aux,
                    $pk_len,
                    $sk_len,
                    $sig_len,
                >>::sign(payload, private_key, signature, $sign_aux_param)
                .map_err($crate::signature::slice::SignError::from)
            }
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

                <$type as $crate::signature::arrayref::Signature<
                    $sign_aux,
                    $verify_aux,
                    $pk_len,
                    $sk_len,
                    $sig_len,
                >>::verify(payload, public_key, signature, $verify_aux_param)
                .map_err($crate::signature::slice::VerifyError::from)
            }
        }
    };
}
pub use impl_signature_slice_trait;
