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

#[derive(Clone, TlsSerialize, TlsSize)]
pub struct PQPublicKey(MlKem768PublicKey);
pub struct PQPrivateKey(MlKem768PrivateKey);
pub struct PQKeyPair {
    pub pk: PQPublicKey,
    pub(crate) sk: PQPrivateKey,
}
#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
pub struct PQCiphertext(MlKem768Ciphertext);
#[derive(TlsSerializeBytes, TlsSize)]
pub struct PQSharedSecret(MlKemSharedSecret);

impl PQPublicKey {
    pub(crate) fn encapsulate(&self, rng: &mut impl CryptoRng) -> (PQCiphertext, PQSharedSecret) {
        let (ciphertext, shared_secret) = encapsulate(&self.0, rng);
        (PQCiphertext(ciphertext), PQSharedSecret(shared_secret))
    }
}

impl PQPrivateKey {
    pub(crate) fn decapsulate(&self, enc: &PQCiphertext) -> PQSharedSecret {
        PQSharedSecret(decapsulate(&self.0, &enc.0))
    }
}

impl PQKeyPair {
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let (sk, pk) = generate_key_pair(rng).into_parts();
        PQKeyPair {
            pk: PQPublicKey(pk),
            sk: PQPrivateKey(sk),
        }
    }
}
