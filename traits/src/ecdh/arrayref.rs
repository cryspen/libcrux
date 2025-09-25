//TODO: Docs
use libcrux_secrets::U8;

pub trait ECDHArrayref<const RAND_LEN: usize, const SECRET_LEN: usize, const PUBLIC_LEN: usize> {
    fn generate_secret(
        secret: &mut [U8; SECRET_LEN],
        rand: &[U8; RAND_LEN],
    ) -> Result<(), ECDHError>;
    fn secret_to_public(
        public: &mut [u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), ECDHError>;
    fn derive_ecdh(
        derived: &mut [U8; PUBLIC_LEN],
        public: &[u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), ECDHError>;
    fn validate_secret(secret: &[U8; SECRET_LEN]) -> Result<(), ECDHError>;
}

#[derive(Debug)]
pub enum ECDHError {
    GenerateSecret,
    SecretToPublic,
    Derive,
    ValidateSecret,
}

impl core::fmt::Display for ECDHError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            ECDHError::GenerateSecret => "error generating ECDH secret value",
            ECDHError::SecretToPublic => {
                "error transforming secret ECDH value to public ECDH value"
            }
            ECDHError::Derive => "error deriving ECDH shared secret",
            ECDHError::ValidateSecret => "invalid ECDH secret value",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error-in-core")]
/// Here we implement the Error trait. This has only been added to core relatively recently, so we
/// are hiding that behind a feature.
mod error_in_core {
    impl core::error::Error for super::ECDHError {}
}
