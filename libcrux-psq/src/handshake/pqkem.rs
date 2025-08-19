use libcrux_ml_kem::{
    mlkem768::{
        decapsulate,
        rand::{encapsulate, generate_key_pair},
        MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey,
    },
    MlKemSharedSecret,
};
use rand::CryptoRng;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

#[derive(TlsSerialize, TlsSize)]
/// A PQ-KEM public key
pub struct PQPublicKey(MlKem768PublicKey);

/// A PQ-KEM private key
pub struct PQPrivateKey(MlKem768PrivateKey);

/// Wrapper type for PQ-KEM key pairs
pub struct PQKeyPair {
    pub pk: PQPublicKey,
    pub(crate) sk: PQPrivateKey,
}

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
/// A PQ-KEM key encapsulation
pub struct PQCiphertext(MlKem768Ciphertext);

#[derive(TlsSerializeBytes, TlsSize)]
/// A PQ-KEM shared secret
pub struct PQSharedSecret(MlKemSharedSecret);

impl PQPublicKey {
    /// Encapsulate a PQ-shared secret towards the given PQ-KEM public key
    pub(crate) fn encapsulate(&self, rng: &mut impl CryptoRng) -> (PQCiphertext, PQSharedSecret) {
        let (ciphertext, shared_secret) = encapsulate(&self.0, rng);
        (PQCiphertext(ciphertext), PQSharedSecret(shared_secret))
    }
}

impl PQPrivateKey {
    /// Decapsulate a PQ-shared secret from an encapsulation
    pub(crate) fn decapsulate(&self, enc: &PQCiphertext) -> PQSharedSecret {
        PQSharedSecret(decapsulate(&self.0, &enc.0))
    }
}

impl PQKeyPair {
    /// Generate a new PQ-KEM key pair
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let (sk, pk) = generate_key_pair(rng).into_parts();
        PQKeyPair {
            pk: PQPublicKey(pk),
            sk: PQPrivateKey(sk),
        }
    }
}
