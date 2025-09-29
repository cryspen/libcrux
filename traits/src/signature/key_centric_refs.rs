pub use super::slice::{KeyGenError, SignError, VerifyError};
use libcrux_secrets::U8;

pub struct SigningKeyRef<'a, Algorithm> {
    key: &'a [U8],
    _marker: core::marker::PhantomData<Algorithm>,
}

pub enum FromBytesError {
    InvalidLength,
}

impl<'a, const L: usize, Algorithm: super::key_centric_owned::Sign<SigningKey = [U8; L]>>
    SigningKeyRef<'a, Algorithm>
{
    pub fn from_bytes(key: &'a [U8]) -> Result<Self, FromBytesError> {
        if key.len() != L {
            return Err(FromBytesError::InvalidLength);
        }

        Ok(Self {
            key,
            _marker: Default::default(),
        })
    }
    pub fn sign(
        &self,
        payload: &[u8],
        aux: Algorithm::SignAux<'_>,
    ) -> Result<Algorithm::Signature, SignError> {
        let key: &[U8; L] = self
            .key
            .try_into()
            .map_err(|_| SignError::InvalidSigningKeyLength)?;

        Algorithm::sign(payload, key, aux).map_err(SignError::from)
    }
}

pub struct VerificationKeyRef<'a, Algorithm> {
    key: &'a [U8],
    _marker: core::marker::PhantomData<Algorithm>,
}

impl<'a, const L: usize, Algorithm: super::key_centric_owned::Sign<VerificationKey = [U8; L]>>
    VerificationKeyRef<'a, Algorithm>
{
    pub fn from_bytes(key: &'a [U8]) -> Result<Self, FromBytesError> {
        if key.len() != L {
            return Err(FromBytesError::InvalidLength);
        }

        Ok(Self {
            key,
            _marker: Default::default(),
        })
    }
    pub fn verify(
        &self,
        payload: &[u8],
        signature: &Algorithm::Signature,
        aux: Algorithm::VerifyAux<'_>,
    ) -> Result<(), VerifyError> {
        let key: &[U8; L] = self
            .key
            .try_into()
            .map_err(|_| VerifyError::InvalidVerificationKeyLength)?;

        Algorithm::verify(payload, key, signature, aux).map_err(VerifyError::from)
    }
}
