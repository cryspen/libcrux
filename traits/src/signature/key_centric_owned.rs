use libcrux_secrets::U8;

pub trait SignTypes {
    type SigningKey;
    type VerificationKey;
    type Signature;
    type Randomness;
}

pub trait Sign: SignTypes {
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// The signing key.
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &Self::SigningKey,
        aux: Self::SignAux<'_>,
    ) -> Result<Self::Signature, SignError>;
    /// Auxiliary information needed for verification.
    type VerifyAux<'a>;

    /// Verify a signature using a provided verification key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn verify(
        payload: &[u8],
        verification_key: &Self::VerificationKey,
        signature: &Self::Signature,
        aux: Self::VerifyAux<'_>,
    ) -> Result<(), VerifyError>;
    /// Generate a pair of signing and verification keys.
    ///
    /// It is the responsibility of the caller to ensure  that the `rand` argument is actually
    /// random.
    fn keygen(
        rand: Self::Randomness,
    ) -> Result<(Self::SigningKey, Self::VerificationKey), KeyGenError>;
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

impl<Algorithm: Sign> KeyPair<Algorithm> {
    pub fn generate_key_pair(randomness: Algorithm::Randomness) -> Result<Self, KeyGenError> {
        Algorithm::keygen(randomness).map(|(signing_key, verification_key)| KeyPair {
            signing_key: SigningKey { key: signing_key },
            verification_key: VerificationKey {
                key: verification_key,
            },
        })
    }
}
impl<'a, Algorithm: Sign<SignAux<'a> = ()>> SigningKey<Algorithm> {
    pub fn sign(&self, payload: &[u8]) -> Result<Algorithm::Signature, SignError> {
        Algorithm::sign(payload, &self.key, ())
    }
}

impl<Algorithm: Sign> VerificationKey<Algorithm> {
    pub fn verify(
        &self,
        payload: &[u8],
        signature: &Algorithm::Signature,
        aux: Algorithm::VerifyAux<'_>,
    ) -> Result<(), VerifyError> {
        Algorithm::verify(payload, &self.key, signature, aux)
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
            type Randomness = [$crate::libcrux_secrets::U8; $rand_keygen_len];
        }

        impl $crate::signature::key_centric_owned::Sign for $ty {
            type SignAux<'a> = <$ty as $crate::signature::owned::Sign<
                $signing_key_len,
                $verification_key_len,
                $signature_len,
                $rand_keygen_len,
            >>::SignAux<'a>;
            fn sign(
                payload: &[u8],
                signing_key: &Self::SigningKey,
                aux: Self::SignAux<'_>,
            ) -> Result<Self::Signature, $crate::signature::owned::SignError> {
                <$ty as $crate::signature::owned::Sign<
                    $signing_key_len,
                    $verification_key_len,
                    $signature_len,
                    $rand_keygen_len,
                >>::sign(payload, signing_key, aux)
            }
            type VerifyAux<'a> = <$ty as $crate::signature::owned::Sign<
                $signing_key_len,
                $verification_key_len,
                $signature_len,
                $rand_keygen_len,
            >>::VerifyAux<'a>;

            fn verify(
                payload: &[u8],
                verification_key: &Self::VerificationKey,
                signature: &Self::Signature,
                aux: Self::VerifyAux<'_>,
            ) -> Result<(), $crate::signature::owned::VerifyError> {
                <$ty as $crate::signature::owned::Sign<
                    $signing_key_len,
                    $verification_key_len,
                    $signature_len,
                    $rand_keygen_len,
                >>::verify(payload, verification_key, signature, aux)
            }
            fn keygen(
                rand: Self::Randomness,
            ) -> Result<
                (Self::SigningKey, Self::VerificationKey),
                $crate::signature::owned::KeyGenError,
            > {
                <$ty as $crate::signature::owned::Sign<
                    $signing_key_len,
                    $verification_key_len,
                    $signature_len,
                    $rand_keygen_len,
                >>::keygen(rand)
            }
        }
    };
}

pub use impl_key_centric_owned;

impl<const L: usize, Algorithm: Sign<SigningKey = [U8; L]>> From<[U8; L]>
    for SigningKey<Algorithm>
{
    fn from(bytes: [U8; L]) -> Self {
        Self { key: bytes }
    }
}

impl<const L: usize, Algorithm: Sign<VerificationKey = [U8; L]>> From<[U8; L]>
    for VerificationKey<Algorithm>
{
    fn from(bytes: [U8; L]) -> Self {
        Self { key: bytes }
    }
}
