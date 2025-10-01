use libcrux_secrets::U8;

pub trait SignTypes {
    type SigningKey;
    type VerificationKey;
    type Signature;
    type KeyGenRandomness;
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// Auxiliary information needed for verification.
    type VerifyAux<'a>;
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
                VerificationKey = [U8; VERIFICATION_KEY_LEN],
                Signature = [U8; SIGNATURE_LEN],
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
        aux: <Algorithm as super::owned::Sign<
            SIGNING_KEY_LEN,
            VERIFICATION_KEY_LEN,
            SIGNATURE_LEN,
            RAND_KEYGEN_LEN,
        >>::SignAux<'_>,
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
                VerificationKey = [U8; VERIFICATION_KEY_LEN],
                Signature = [U8; SIGNATURE_LEN],
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
        aux: <Algorithm as super::owned::Sign<
            SIGNING_KEY_LEN,
            VERIFICATION_KEY_LEN,
            SIGNATURE_LEN,
            RAND_KEYGEN_LEN,
        >>::VerifyAux<'_>,
    ) -> Result<(), VerifyError> {
        Algorithm::verify(payload, &self.key, signature, aux)
    }
}

impl<
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
macro_rules! impl_key_centric_owned {
    ($ty:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr) => {
        impl $crate::signature::key_centric_owned::SignTypes for $ty {
            type SigningKey = [$crate::libcrux_secrets::U8; $signing_key_len];
            type VerificationKey = [$crate::libcrux_secrets::U8; $verification_key_len];
            type Signature = [$crate::libcrux_secrets::U8; $signature_len];
            type KeyGenRandomness = [$crate::libcrux_secrets::U8; $rand_keygen_len];
            type SignAux<'a> = <$ty as $crate::signature::owned::Sign<
                $signing_key_len,
                $verification_key_len,
                $signature_len,
                $rand_keygen_len,
            >>::SignAux<'a>;
            type VerifyAux<'a> = <$ty as $crate::signature::owned::Sign<
                $signing_key_len,
                $verification_key_len,
                $signature_len,
                $rand_keygen_len,
            >>::VerifyAux<'a>;
        }
    };
}
pub use impl_key_centric_owned;

impl<const L: usize, Algorithm: SignTypes<SigningKey = [U8; L]>> From<[U8; L]>
    for SigningKey<Algorithm>
{
    fn from(bytes: [U8; L]) -> Self {
        Self { key: bytes }
    }
}

impl<const L: usize, Algorithm: SignTypes<VerificationKey = [U8; L]>> From<[U8; L]>
    for VerificationKey<Algorithm>
{
    fn from(bytes: [U8; L]) -> Self {
        Self { key: bytes }
    }
}
