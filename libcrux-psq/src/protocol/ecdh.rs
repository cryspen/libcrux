use libcrux_ecdh::{secret_to_public, Algorithm};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

#[derive(TlsSerializeBytes, TlsSize)]
pub(crate) struct SharedSecret(Vec<u8>);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

#[derive(Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
pub(crate) struct PublicKey(Vec<u8>);

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}
#[derive(Clone)]
pub(crate) struct PrivateKey(Vec<u8>);

impl AsRef<[u8]> for PrivateKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl SharedSecret {
    pub(crate) fn derive(sk: &PrivateKey, pk: &PublicKey) -> SharedSecret {
        SharedSecret(libcrux_ecdh::derive(Algorithm::X25519, &pk.0, &sk.0).unwrap())
    }
}

impl PrivateKey {
    pub(crate) fn new(rng: &mut impl CryptoRng) -> Self {
        Self(
            libcrux_ecdh::generate_secret(libcrux_ecdh::Algorithm::X25519, rng)
                .expect("Insufficient Randomness"),
        )
    }
}

impl From<&PrivateKey> for PublicKey {
    fn from(value: &PrivateKey) -> Self {
        PublicKey(secret_to_public(libcrux_ecdh::Algorithm::X25519, &value.0).unwrap())
    }
}
