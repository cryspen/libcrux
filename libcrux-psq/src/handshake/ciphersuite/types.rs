use libcrux_ed25519::VerificationKey;
use libcrux_kem::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_dsa::ml_dsa_65::{MLDSA65Signature, MLDSA65VerificationKey};
use libcrux_ml_kem::MlKemSharedSecret;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{Ciphertext, PublicKey, SecretKey, SharedSecret};
use crate::handshake::{ciphersuite::initiator::Auth, dhkem::DHPublicKey};

#[derive(TlsSize, TlsDeserialize, TlsSerialize)]
#[repr(u8)]
pub enum Authenticator {
    Dh(DHPublicKey),
    Sig(SigVerificationKey),
}

impl From<Auth<'_>> for Authenticator {
    fn from(value: Auth<'_>) -> Self {
        match value {
            Auth::DH(dhkey_pair) => Authenticator::Dh(dhkey_pair.pk.clone()),
            Auth::Sig(sig_auth) => Authenticator::Sig(sig_auth.into()),
        }
    }
}

#[derive(TlsSize, TlsDeserialize, TlsSerialize, Clone)]
#[repr(u8)]
pub enum SigVerificationKey {
    Ed25519(VerificationKey),
    MlDsa65(MLDSA65VerificationKey),
}

#[derive(TlsSize, TlsDeserialize, TlsSerialize)]
#[repr(u8)]
pub enum Signature {
    Ed25519([u8; 64]),
    MlDsa65(MLDSA65Signature),
}

#[derive(TlsSize, TlsDeserialize, TlsSerialize)]
#[repr(u8)]
pub enum PQCiphertext {
    MlKem(Box<MlKem768Ciphertext>) = 1,
    #[cfg(feature = "classic-mceliece")]
    CMC(Box<Ciphertext>) = 2,
    #[cfg(not(feature = "classic-mceliece"))]
    CMC = 3,
}

#[derive(TlsSize, TlsSerialize)]
#[repr(u8)]
pub enum PQEncapsulationKey<'a> {
    MlKem(&'a MlKem768PublicKey) = 1,
    #[cfg(feature = "classic-mceliece")]
    CMC(&'a PublicKey) = 2,
    #[cfg(not(feature = "classic-mceliece"))]
    CMC = 3,
}

impl<'a> From<&'a MlKem768PublicKey> for PQEncapsulationKey<'a> {
    fn from(value: &'a MlKem768PublicKey) -> Self {
        Self::MlKem(value)
    }
}

#[cfg(feature = "classic-mceliece")]
impl<'a> From<&'a PublicKey> for PQEncapsulationKey<'a> {
    fn from(value: &'a PublicKey) -> Self {
        Self::CMC(value)
    }
}

#[derive(TlsSize, TlsSerializeBytes)]
#[repr(u8)]
pub enum PQSharedSecret {
    None,
    MlKem(MlKemSharedSecret),
    #[cfg(feature = "classic-mceliece")]
    CMC(SharedSecret<'static>),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}

pub enum PQDecapsulationKey {
    None,
    MlKem(Box<MlKem768PrivateKey>),
    #[cfg(feature = "classic-mceliece")]
    CMC(Box<SecretKey>),
    #[cfg(not(feature = "classic-mceliece"))]
    CMC,
}
