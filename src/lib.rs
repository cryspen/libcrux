#[derive(Debug)]
/// PSQ Errors.
pub enum Error {
    /// An invalid public key was provided
    InvalidPublicKey,
    /// An invalid private key was provided
    InvalidPrivateKey,
    /// An error during PSK encapsulation
    GenerationError,
    /// An error during PSK decapsulation
    DerivationError,
}

const PSK_LENGTH: usize = 32;
type Psk = [u8; PSK_LENGTH];

pub mod ecdh_binder;
pub mod psq;
