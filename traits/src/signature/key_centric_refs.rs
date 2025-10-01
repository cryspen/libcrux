pub use super::slice::{KeyGenError, SignError, VerifyError};
use libcrux_secrets::U8;

pub struct SigningKeyRef<'a, Algorithm> {
    key: &'a [U8],
    _marker: core::marker::PhantomData<Algorithm>,
}

#[derive(Debug)]
pub enum FromBytesError {
    InvalidLength,
}

impl<
        'a,
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [U8; VERIFICATION_KEY_LEN],
                Signature = [U8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > SigningKeyRef<'a, Algorithm>
{
    pub fn from_bytes(key: &'a [U8]) -> Result<Self, FromBytesError> {
        if key.len() != SIGNING_KEY_LEN {
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
        aux: <Algorithm as super::owned::Sign<
            SIGNING_KEY_LEN,
            VERIFICATION_KEY_LEN,
            SIGNATURE_LEN,
            RAND_KEYGEN_LEN,
        >>::SignAux<'_>,
    ) -> Result<Algorithm::Signature, SignError> {
        let key: &[U8; SIGNING_KEY_LEN] = self
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

impl<
        'a,
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [U8; VERIFICATION_KEY_LEN],
                Signature = [U8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > VerificationKeyRef<'a, Algorithm>
{
    pub fn from_bytes(key: &'a [U8]) -> Result<Self, FromBytesError> {
        if key.len() != VERIFICATION_KEY_LEN {
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
    ) -> Result<(), VerifyError> {
        let key: &[U8; VERIFICATION_KEY_LEN] = self
            .key
            .try_into()
            .map_err(|_| VerifyError::InvalidVerificationKeyLength)?;

        Algorithm::verify(payload, key, signature).map_err(VerifyError::from)
    }
}
