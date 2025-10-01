use libcrux_secrets::U8;

pub trait SignConsts {
    const VERIFICATION_KEY_LEN: usize;
    const SIGNING_KEY_LEN: usize;
    const SIGNATURE_LEN: usize;
    const RAND_KEYGEN_LEN: usize;
}
pub trait SignTypes {
    type SigningKey;
    type VerificationKey;
    type Signature;
    type KeyGenRandomness;
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
}

pub struct SigningKey<Algorithm: SignTypes> {
    key: Algorithm::SigningKey,
}

pub struct VerificationKey<Algorithm: SignTypes> {
    key: Algorithm::VerificationKey,
}

pub struct KeyPair<Algorithm: SignTypes> {
    pub signing_key: SigningKey<Algorithm>,
    pub verification_key: VerificationKey<Algorithm>,
}

impl<
        'a,
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > SigningKey<Algorithm>
{
    pub fn sign(
        &self,
        payload: &[u8],
        aux: <Algorithm as super::key_centric_owned::SignTypes>::SignAux<'_>,
    ) -> Result<Algorithm::Signature, SignError> {
        Algorithm::sign(payload, &self.key, aux)
    }
}

impl<
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > VerificationKey<Algorithm>
{
    pub fn verify(
        &self,
        payload: &[u8],
        signature: &Algorithm::Signature,
    ) -> Result<(), VerifyError> {
        Algorithm::verify(payload, &self.key, signature)
    }
}

impl<
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > KeyPair<Algorithm>
{
    pub fn from_keys(
        signing_key: Algorithm::SigningKey,
        verification_key: Algorithm::VerificationKey,
    ) -> Self {
        Self {
            signing_key: SigningKey { key: signing_key },
            verification_key: VerificationKey {
                key: verification_key,
            },
        }
    }
}

pub use super::owned::{KeyGenError, SignError, VerifyError};

/// Implement `key_centric_owned` traits based on internal `owned` traits
#[macro_export]
macro_rules! impl_sign_types {
    ($ty:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr, $sign_aux:ty) => {
        impl $crate::signature::key_centric_owned::SignTypes for $ty {
            type SigningKey = [$crate::libcrux_secrets::U8; $signing_key_len];
            type VerificationKey = [u8; $verification_key_len];
            type Signature = [u8; $signature_len];
            type KeyGenRandomness = [$crate::libcrux_secrets::U8; $rand_keygen_len];
            type SignAux<'a> = $sign_aux;
        }
    };
}
pub use impl_sign_types;

impl<const L: usize, Algorithm: SignTypes<SigningKey = [U8; L]>> From<[U8; L]>
    for SigningKey<Algorithm>
{
    fn from(bytes: [U8; L]) -> Self {
        Self { key: bytes }
    }
}

impl<const L: usize, Algorithm: SignTypes<VerificationKey = [u8; L]>> From<[u8; L]>
    for VerificationKey<Algorithm>
{
    fn from(bytes: [u8; L]) -> Self {
        Self { key: bytes }
    }
}
