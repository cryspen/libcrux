use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use libcrux_ml_kem::{
    mlkem768::{
        decapsulate, rand::encapsulate, MlKem768Ciphertext, MlKem768KeyPair, MlKem768PrivateKey,
        MlKem768PublicKey,
    },
    MlKemSharedSecret,
};
use rand::CryptoRng;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

use crate::classic_mceliece::{
    Ciphertext, KeyPair, McElieceRng, PublicKey, SecretKey, SharedSecret,
};

#[derive(TlsSerialize, TlsSize)]
#[repr(u8)]
/// A PQ-KEM public key
pub enum PQPublicKey<'a> {
    MlKem768(&'a MlKem768PublicKey),
    ClassicMcEliece(PublicKey<'a>),
}

impl<'a> From<&'a MlKem768PublicKey> for PQPublicKey<'a> {
    fn from(value: &'a MlKem768PublicKey) -> Self {
        Self::MlKem768(value)
    }
}

impl<'a> From<PublicKey<'a>> for PQPublicKey<'a> {
    fn from(value: PublicKey<'a>) -> Self {
        Self::ClassicMcEliece(value)
    }
}

/// A PQ-KEM private key
pub enum PQPrivateKey<'a> {
    MlKem768(&'a MlKem768PrivateKey),
    ClassicMcEliece(SecretKey<'a>),
}

impl<'a> From<&'a MlKem768PrivateKey> for PQPrivateKey<'a> {
    fn from(value: &'a MlKem768PrivateKey) -> Self {
        Self::MlKem768(value)
    }
}

impl<'a> From<SecretKey<'a>> for PQPrivateKey<'a> {
    fn from(value: SecretKey<'a>) -> Self {
        Self::ClassicMcEliece(value)
    }
}

/// Wrapper type for PQ-KEM key pairs
pub enum PQKeyPair<'a> {
    MlKem768 {
        pk: &'a MlKem768PublicKey,
        sk: &'a MlKem768PrivateKey,
    },
    ClassicMcEliece {
        pk: PublicKey<'a>,
        sk: SecretKey<'a>,
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

impl<'a> From<KeyPair<'a>> for PQKeyPair<'a> {
    fn from(value: KeyPair<'a>) -> Self {
        Self::ClassicMcEliece {
            pk: value.pk,
            sk: value.sk,
        }
    }
}

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
#[repr(u8)]
/// A PQ-KEM key encapsulation
pub enum PQCiphertext {
    MlKem768(MlKem768Ciphertext),
    ClassicMcEliece(Ciphertext),
}

impl From<MlKem768Ciphertext> for PQCiphertext {
    fn from(value: MlKem768Ciphertext) -> Self {
        Self::MlKem768(value)
    }
}

impl From<Ciphertext> for PQCiphertext {
    fn from(value: Ciphertext) -> Self {
        Self::ClassicMcEliece(value)
    }
}

#[derive(TlsSerializeBytes, TlsSize)]
/// A PQ-KEM shared secret
#[repr(u8)]
pub enum PQSharedSecret<'a> {
    MlKem768(MlKemSharedSecret),
    ClassicMcEliece(SharedSecret<'a>),
}

impl From<MlKemSharedSecret> for PQSharedSecret<'_> {
    fn from(value: MlKemSharedSecret) -> Self {
        Self::MlKem768(value)
    }
}

impl<'a> From<SharedSecret<'a>> for PQSharedSecret<'a> {
    fn from(value: SharedSecret<'a>) -> Self {
        Self::ClassicMcEliece(value)
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
            PQPublicKey::ClassicMcEliece(public_key) => {
                let mut rng = McElieceRng::new(rng);
                let (enc, ss) = encapsulate_boxed(&public_key.0, &mut rng);
                (Ciphertext(enc).into(), SharedSecret(ss).into())
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
            (
                PQPrivateKey::ClassicMcEliece(secret_key),
                PQCiphertext::ClassicMcEliece(ciphertext),
            ) => SharedSecret(decapsulate_boxed(&ciphertext.0, &secret_key.0)).into(),
            (PQPrivateKey::MlKem768(_), PQCiphertext::ClassicMcEliece(_))
            | (PQPrivateKey::ClassicMcEliece(_), PQCiphertext::MlKem768(_)) => panic!(), // Incompatible KEM / ciphertext
        }
    }
}

impl<'a> PQKeyPair<'a> {
    pub(crate) fn private_key(self) -> PQPrivateKey<'a> {
        match self {
            PQKeyPair::MlKem768 { sk, .. } => sk.into(),
            PQKeyPair::ClassicMcEliece { sk, .. } => sk.into(),
        }
    }

    pub fn public_key(self) -> PQPublicKey<'a> {
        match self {
            PQKeyPair::MlKem768 { pk, .. } => pk.into(),
            PQKeyPair::ClassicMcEliece { pk, .. } => pk.into(),
        }
    }
}
