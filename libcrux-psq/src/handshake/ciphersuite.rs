use libcrux_kem::{MlKem768Ciphertext, MlKem768PublicKey};
use libcrux_ml_kem::MlKemSharedSecret;
use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, SerializeBytes, Size};

use crate::handshake::{
    dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
    HandshakeError,
};

pub trait CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize + Size;
    type EncapsulationKey: Serialize + Size;
    type SharedSecret: SerializeBytes + Size;

    fn name(&self) -> CiphersuiteName;

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey;
    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey;
}

pub trait InitiatorCiphersuite: CiphersuiteBase {
    fn peer_pq_encapsulation_key(&self) -> Option<&<Self as CiphersuiteBase>::EncapsulationKey>;

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<
        (
            Option<<Self as CiphersuiteBase>::Ciphertext>,
            Option<<Self as CiphersuiteBase>::SharedSecret>,
        ),
        HandshakeError,
    >;
}

pub trait ResponderCiphersuite: CiphersuiteBase {
    type DecapsulationKey;
    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKey>;
    fn own_pq_decapsulation_key(&self) -> Option<&Self::DecapsulationKey>;
    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError>;
}

pub enum CiphersuiteName {
    X25519ChachaPolyHkdfSha256,
    X25519Mlkem768ChachaPolyHkdfSha256,
    X25519ClassicMcElieceChachaPolyHkdfSha256,
}

pub struct InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub(crate) peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
}

pub struct InitiatorX25519ChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
}

impl CiphersuiteBase for InitiatorX25519ChachaPolyHkdfSha256<'_> {
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;

    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519ChachaPolyHkdfSha256
    }

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        self.peer_longterm_ecdh_pk
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

impl CiphersuiteBase for InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'_> {
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;
    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256
    }

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        self.peer_longterm_ecdh_pk
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

impl InitiatorCiphersuite for InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'_> {
    fn peer_pq_encapsulation_key(&self) -> Option<&Self::EncapsulationKey> {
        Some(self.peer_longterm_mlkem_pk)
    }

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<(Option<Self::Ciphertext>, Option<Self::SharedSecret>), HandshakeError> {
        todo!()
    }
}

#[cfg(feature = "classic-mceliece")]
pub struct InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub(crate) peer_longterm_cmc_pk: crate::classic_mceliece::PublicKey,
}
