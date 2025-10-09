use libcrux_kem::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_kem::MlKemSharedSecret;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{Ciphertext, PublicKey, SecretKey, SharedSecret};

#[derive(TlsSize, TlsDeserialize, TlsSerialize)]
#[repr(u8)]
pub enum DynamicCiphertext {
    MlKem(MlKem768Ciphertext) = 1,
    #[cfg(feature = "classic-mceliece")]
    CMC(Ciphertext) = 2,
    #[cfg(not(feature = "classic-mceliece"))]
    CMC = 3,
}

#[derive(TlsSize, TlsSerialize)]
#[repr(u8)]
pub enum DynamicEncapsulationKeyRef<'a> {
    MlKem(&'a MlKem768PublicKey) = 1,
    #[cfg(feature = "classic-mceliece")]
    CMC(&'a PublicKey) = 2,
    #[cfg(not(feature = "classic-mceliece"))]
    CMC = 3,
}

impl<'a> From<&'a MlKem768PublicKey> for DynamicEncapsulationKeyRef<'a> {
    fn from(value: &'a MlKem768PublicKey) -> Self {
        Self::MlKem(value)
    }
}

#[cfg(feature = "classic-mceliece")]
impl<'a> From<&'a PublicKey> for DynamicEncapsulationKeyRef<'a> {
    fn from(value: &'a PublicKey) -> Self {
        Self::CMC(value)
    }
}

#[derive(TlsSize, TlsSerializeBytes)]
#[repr(u8)]
pub enum DynamicSharedSecret<'a> {
    None,
    MlKem(MlKemSharedSecret),
    #[cfg(feature = "classic-mceliece")]
    CMC(SharedSecret<'a>),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC(std::marker::PhantomData<&'a [u8]>),
}

pub enum DynamicDecapsulationKey {
    None,
    MlKem(MlKem768PrivateKey),
    #[cfg(feature = "classic-mceliece")]
    CMC(SecretKey),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}
