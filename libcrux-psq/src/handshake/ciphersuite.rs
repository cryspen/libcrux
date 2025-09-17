use libcrux_kem::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_kem::MlKemSharedSecret;
use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, SerializeBytes, Size};

#[cfg(feature = "classic-mceliece")]
use crate::classic_mceliece::{Ciphertext, PublicKey, SecretKey, SharedSecret};
use crate::handshake::{
    dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
    HandshakeError,
};

pub trait CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize + Size;
    type EncapsulationKey;
    type EncapsulationKeyRef: Serialize + Size;
    type SharedSecret: SerializeBytes + Size;

    fn name(&self) -> CiphersuiteName;

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey;
}

pub trait InitiatorCiphersuite: CiphersuiteBase {
    fn peer_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef>;

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey;

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
    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef>;
    fn own_pq_decapsulation_key(&self) -> Option<&Self::DecapsulationKey>;
    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError>;
}

pub struct ResponderX25519MlKem768ChaChaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a MlKem768PublicKey,
    pub longterm_pq_decapsulation_key: &'a MlKem768PrivateKey,
}

impl<'a> CiphersuiteBase for ResponderX25519MlKem768ChaChaPolyHkdfSha256<'a> {
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type EncapsulationKeyRef = &'a MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;

    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

impl ResponderCiphersuite for ResponderX25519MlKem768ChaChaPolyHkdfSha256<'_> {
    type DecapsulationKey = MlKem768PrivateKey;

    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        Some(self.longterm_pq_encapsulation_key)
    }

    fn own_pq_decapsulation_key(&self) -> Option<&Self::DecapsulationKey> {
        Some(self.longterm_pq_decapsulation_key)
    }

    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError> {
        if ciphertext.is_none() {
            return Err(HandshakeError::UnsupportedCiphersuite);
        }
        let shared_secret = libcrux_ml_kem::mlkem768::decapsulate(
            self.longterm_pq_decapsulation_key,
            ciphertext.expect("ciphertext should not be none for this ciphersuite"),
        );
        Ok(Some(shared_secret))
    }
}

pub enum CiphersuiteName {
    X25519ChachaPolyHkdfSha256,
    X25519Mlkem768ChachaPolyHkdfSha256,
    X25519ClassicMcElieceChachaPolyHkdfSha256,
}

pub struct InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
}

pub struct InitiatorX25519ChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
}

impl<'a> CiphersuiteBase for InitiatorX25519ChachaPolyHkdfSha256<'a> {
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type EncapsulationKeyRef = &'a MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;

    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519ChachaPolyHkdfSha256
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

impl<'a> CiphersuiteBase for InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a> {
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type EncapsulationKeyRef = &'a MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;
    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

impl InitiatorCiphersuite for InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'_> {
    fn peer_pq_encapsulation_key(&self) -> Option<Self::EncapsulationKeyRef> {
        Some(self.peer_longterm_mlkem_pk)
    }

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        self.peer_longterm_ecdh_pk
    }

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<(Option<Self::Ciphertext>, Option<Self::SharedSecret>), HandshakeError> {
        let mut rand = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
        rng.fill_bytes(&mut rand);
        let (ct, ss) = libcrux_ml_kem::mlkem768::encapsulate(self.peer_longterm_mlkem_pk, rand);
        Ok((Some(ct), Some(ss)))
    }
}

#[cfg(feature = "classic-mceliece")]
pub struct InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub peer_longterm_cmc_pk: &'a PublicKey,
}

#[cfg(feature = "classic-mceliece")]
impl<'a> CiphersuiteBase for InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a> {
    type Ciphertext = Ciphertext;
    type EncapsulationKey = PublicKey;
    type EncapsulationKeyRef = &'a PublicKey;
    type SharedSecret = SharedSecret<'a>;
    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

#[cfg(feature = "classic-mceliece")]
impl InitiatorCiphersuite for InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'_> {
    fn peer_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        Some(&self.peer_longterm_cmc_pk)
    }

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        self.peer_longterm_ecdh_pk
    }

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<
        (
            Option<<Self as CiphersuiteBase>::Ciphertext>,
            Option<<Self as CiphersuiteBase>::SharedSecret>,
        ),
        HandshakeError,
    > {
        use crate::classic_mceliece::ClassicMcEliece;
        use libcrux_traits::kem::KEM;
        let (ss, ct) = <ClassicMcEliece as KEM>::encapsulate(&self.peer_longterm_cmc_pk, rng)
            .map_err(|_| HandshakeError::CryptoError)?;
        Ok((Some(ct), Some(ss)))
    }
}

#[cfg(feature = "classic-mceliece")]
pub struct ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256<'a> {
    pub longterm_ecdh_keys: &'a DHKeyPair,
    pub longterm_pq_encapsulation_key: &'a PublicKey,
    pub longterm_pq_decapsulation_key: &'a SecretKey,
}
#[cfg(feature = "classic-mceliece")]
impl<'a> CiphersuiteBase for ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256<'a> {
    type Ciphertext = Ciphertext;
    type EncapsulationKey = PublicKey;
    type EncapsulationKeyRef = &'a PublicKey;
    type SharedSecret = SharedSecret<'a>;

    fn name(&self) -> CiphersuiteName {
        CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256
    }

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey {
        &self.longterm_ecdh_keys.sk
    }

    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey {
        &self.longterm_ecdh_keys.pk
    }
}

#[cfg(feature = "classic-mceliece")]
impl ResponderCiphersuite for ResponderX25519ClassicMcElieceChaChaPolyHkdfSha256<'_> {
    type DecapsulationKey = SecretKey;

    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef> {
        Some(self.longterm_pq_encapsulation_key)
    }

    fn own_pq_decapsulation_key(&self) -> Option<&Self::DecapsulationKey> {
        Some(self.longterm_pq_decapsulation_key)
    }

    fn pq_decapsulate(
        &self,
        ciphertext: Option<&<Self as CiphersuiteBase>::Ciphertext>,
    ) -> Result<Option<<Self as CiphersuiteBase>::SharedSecret>, HandshakeError> {
        use crate::classic_mceliece::ClassicMcEliece;
        use libcrux_traits::kem::KEM;

        if ciphertext.is_none() {
            return Err(HandshakeError::UnsupportedCiphersuite);
        }

        let shared_secret = <ClassicMcEliece as KEM>::decapsulate(
            &self.longterm_pq_decapsulation_key.0,
            ciphertext.expect("ciphertext should not be None for this ciphersuite"),
        )
        .map_err(|_| HandshakeError::CryptoError)?;

        Ok(Some(shared_secret))
    }
}
