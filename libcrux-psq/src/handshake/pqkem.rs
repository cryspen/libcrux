use libcrux_ml_kem::{
    mlkem768::{
        decapsulate, rand::encapsulate, MlKem768Ciphertext, MlKem768KeyPair, MlKem768PrivateKey,
        MlKem768PublicKey,
    },
    MlKemSharedSecret,
};
use rand::CryptoRng;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

#[derive(TlsSerialize, TlsSize, Copy, Clone)]
#[repr(u8)]
/// A PQ-KEM public key
pub enum PQPublicKey<'a> {
    MlKem768(&'a MlKem768PublicKey),
}

impl<'a> From<&'a MlKem768PublicKey> for PQPublicKey<'a> {
    fn from(value: &'a MlKem768PublicKey) -> Self {
        Self::MlKem768(value)
    }
}

/// A PQ-KEM private key
pub enum PQPrivateKey<'a> {
    MlKem768(&'a MlKem768PrivateKey),
}

impl<'a> From<&'a MlKem768PrivateKey> for PQPrivateKey<'a> {
    fn from(value: &'a MlKem768PrivateKey) -> Self {
        Self::MlKem768(value)
    }
}

/// Wrapper type for PQ-KEM key pairs
#[derive(Copy, Clone)]
pub enum PQKeyPair<'a> {
    MlKem768 {
        pk: &'a MlKem768PublicKey,
        sk: &'a MlKem768PrivateKey,
    },
}

impl<'a> From<&'a MlKem768KeyPair> for PQKeyPair<'a> {
    fn from(value: &'a MlKem768KeyPair) -> Self {
        Self::MlKem768 {
            pk: value.public_key(),
            sk: value.private_key(),
        }
    }
}

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
#[repr(u8)]
/// A PQ-KEM key encapsulation
pub enum PQCiphertext {
    MlKem768(MlKem768Ciphertext),
}

impl From<MlKem768Ciphertext> for PQCiphertext {
    fn from(value: MlKem768Ciphertext) -> Self {
        Self::MlKem768(value)
    }
}

#[derive(TlsSerializeBytes, TlsSize)]
/// A PQ-KEM shared secret
#[repr(u8)]
pub enum PQSharedSecret {
    MlKem768(MlKemSharedSecret),
}

impl From<MlKemSharedSecret> for PQSharedSecret {
    fn from(value: MlKemSharedSecret) -> Self {
        Self::MlKem768(value)
    }
}

impl<'a> PQPublicKey<'a> {
    /// Encapsulate a PQ-shared secret towards the given PQ-KEM public key
    pub(crate) fn encapsulate(&self, rng: &mut impl CryptoRng) -> (PQCiphertext, PQSharedSecret) {
        match &self {
            PQPublicKey::MlKem768(ml_kem_public_key) => {
                let (ciphertext, shared_secret) = encapsulate(ml_kem_public_key, rng);
                (ciphertext.into(), shared_secret.into())
            }
        }
    }
}

impl<'a> PQPrivateKey<'a> {
    /// Decapsulate a PQ-shared secret from an encapsulation
    pub(crate) fn decapsulate(self, enc: &PQCiphertext) -> PQSharedSecret {
        match (self, enc) {
            (
                PQPrivateKey::MlKem768(ml_kem_private_key),
                PQCiphertext::MlKem768(ml_kem_ciphertext),
            ) => decapsulate(ml_kem_private_key, ml_kem_ciphertext).into(),
        }
    }
}

impl<'a> PQKeyPair<'a> {
    pub(crate) fn private_key(self) -> PQPrivateKey<'a> {
        match self {
            PQKeyPair::MlKem768 { sk, .. } => sk.into(),
        }
    }

    pub fn public_key(self) -> PQPublicKey<'a> {
        match self {
            PQKeyPair::MlKem768 { pk, .. } => pk.into(),
        }
    }
}
