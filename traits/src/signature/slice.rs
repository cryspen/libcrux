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

impl<'a, T: Sign<&'a ()>> SignNoAux for T {
    fn sign(payload: &[u8], private_key: &[u8], signature: &mut [u8]) -> Result<(), SignError> {
        <Self as Sign<&()>>::sign(payload, private_key, signature, &())
    }
}

pub trait VerifyNoAux {
    fn verify(payload: &[u8], public_key: &[u8], signature: &[u8]) -> Result<(), VerifyError>;
}
impl<'a, T: Verify<&'a ()>> VerifyNoAux for T {
    fn verify(payload: &[u8], public_key: &[u8], signature: &[u8]) -> Result<(), VerifyError> {
        <Self as Verify<&()>>::verify(payload, public_key, signature, &())
    }
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
