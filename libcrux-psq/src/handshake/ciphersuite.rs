use libcrux_kem::{MlKem768Ciphertext, MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_kem::MlKemSharedSecret;
use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, SerializeBytes};

use crate::{
    aead::AEAD,
    handshake::{
        dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey},
        HandshakeError,
    },
};

// pub struct CiphersuiteBuilder<'a> {
//     aead: Option<AEAD>,
//     longterm_ecdh_keys: Option<&'a DHKeyPair>,
//     longterm_pq_keys: Option<PQKeyPair<'a>>,
//     peer_longterm_ecdh_pk: Option<&'a DHPublicKey>,
//     peer_longterm_mlkem_pk: Option<&'a libcrux_kem::PublicKey>,
//     #[cfg(feature = "classic-mceliece")]
//     peer_longterm_cmc_pk: Option<crate::classic_mceliece::PublicKey>,
// }

// impl<'a> CiphersuiteBuilder<'a> {
//     pub fn new() -> Self {
//         Self {
//             aead: Default::default(),
//             longterm_ecdh_keys: Default::default(),
//             longterm_pq_keys: Default::default(),
//             peer_longterm_ecdh_pk: Default::default(),
//             peer_longterm_mlkem_pk: Default::default(),
//             #[cfg(feature = "classic-mceliece")]
//             peer_longterm_cmc_pk: Default::default(),
//         }
//     }

//     pub fn aead(mut self, aead: AEAD) -> Self {
//         self.aead = Some(aead);
//         self
//     }

//     /// Set the long-term ECDH key pair.
//     pub fn longterm_ecdh_keys(mut self, longterm_ecdh_keys: &'a DHKeyPair) -> Self {
//         self.longterm_ecdh_keys = Some(longterm_ecdh_keys);
//         self
//     }

//     /// Set the long-term PQ key pair.
//     pub fn longterm_pq_keys(mut self, longterm_pq_keys: impl Into<PQKeyPair<'a>>) -> Self {
//         self.longterm_pq_keys = Some(longterm_pq_keys.into());
//         self
//     }

//     /// Set the peer's long-term ECDH public key.
//     pub fn peer_longterm_ecdh_pk(mut self, peer_longterm_ecdh_pk: &'a DHPublicKey) -> Self {
//         self.peer_longterm_ecdh_pk = Some(peer_longterm_ecdh_pk);
//         self
//     }

//     /// Set the peer's long-term PQ public key.
//     pub fn peer_longterm_mlkem_pk(
//         mut self,
//         peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
//     ) -> Self {
//         self.peer_longterm_mlkem_pk = Some(peer_longterm_mlkem_pk.into());
//         self
//     }

//     /// Set the peer's long-term PQ public key.
//     #[cfg(feature = "classic-mceliece")]
//     pub fn peer_longterm_cmc_pk(
//         mut self,
//         peer_longterm_cmc_pk: crate::classic_mceliece::PublicKey,
//     ) -> Self {
//         self.peer_longterm_mlkem_pk = Some(peer_longterm_cmc_pk);
//         self
//     }

//     /// Create an initiator ciphersuite.
//     pub fn build_registration_initiator_ciphersuite(
//         self,
//         name: CiphersuiteName,
//     ) -> Result<RegistrationInitiatorCiphersuite<'a>, HandshakeError> {
//         if self.aead.is_none()
//             || self.peer_longterm_ecdh_pk.is_none()
//             || self.longterm_ecdh_keys.is_none()
//         {
//             return Err(HandshakeError::BuilderState);
//         }

//         match name {
//             CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256 => {
//                 if self.peer_longterm_mlkem_pk.is_none() {
//                     return Err(HandshakeError::BuilderState);
//                 }

//                 Ok(RegistrationInitiatorCiphersuite {
//                     name,
//                     aead: self.aead.expect("self.aead should be Some(..)"),
//                     longterm_ecdh_keys: self
//                         .longterm_ecdh_keys
//                         .expect("self.longterm_ecdh_keys should be Some(..)"),
//                     peer_longterm_ecdh_pk: self
//                         .peer_longterm_ecdh_pk
//                         .expect("self.peer_longterm_ecdh_pk should be Some(..)"),
//                     peer_longterm_pq_pk: self.peer_longterm_mlkem_pk,
//                 })
//             }
//             #[cfg(feature = "classic-mceliece")]
//             CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
//                 if self.peer_longterm_cmc_pk.is_none() {
//                     return Err(HandshakeError::BuilderState);
//                 }

//                 Ok(RegistrationInitiatorCiphersuite {
//                     name,
//                     aead: self.aead.expect("self.aead should be Some(..)"),
//                     longterm_ecdh_keys: self
//                         .longterm_ecdh_keys
//                         .expect("self.longterm_ecdh_keys should be Some(..)"),
//                     peer_longterm_ecdh_pk: self
//                         .peer_longterm_ecdh_pk
//                         .expect("self.peer_longterm_ecdh_pk should be Some(..)"),
//                     peer_longterm_pq_pk: self.peer_longterm_cmc_pk,
//                 })
//             }
//         }
//     }

//     pub fn build_query_initiator_ciphersuite(
//         self,
//     ) -> Result<QueryInitiatorCiphersuite<'a>, HandshakeError> {
//         if self.aead.is_none() || self.peer_longterm_ecdh_pk.is_none() {
//             return Err(HandshakeError::BuilderState);
//         }

//         Ok(QueryInitiatorCiphersuite {
//             aead: self.aead.expect("self.aead should be Some(..)"),
//             peer_longterm_ecdh_pk: self
//                 .peer_longterm_ecdh_pk
//                 .expect("self.peer_longterm_ecdh_pk should be Some(..)"),
//         })
//     }

//     /// Create a responder ciphersuite.
//     pub fn build_responder_ciphersuite(
//         self,
//         name: CiphersuiteName,
//     ) -> Result<ResponderCiphersuite<'a>, HandshakeError> {
//         if self.aead.is_none() || self.longterm_ecdh_keys.is_none() {
//             return Err(HandshakeError::BuilderState);
//         }

//         Ok(ResponderCiphersuite {
//             name,
//             aead: self.aead.expect("self.aead should be Some(..)"),
//             longterm_ecdh_keys: self
//                 .longterm_ecdh_keys
//                 .expect("self.longterm.ecdh_keys should be Some(..)"),
//             longterm_pq_keys: self.longterm_pq_keys,
//         })
//     }
// }

pub enum CiphersuiteName {
    X25519Mlkem768ChachaPolyHkdfSha256,
    X25519ClassicMcElieceChachaPolyHkdfSha256,
}

pub struct InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub(crate) peer_longterm_mlkem_pk: &'a libcrux_ml_kem::mlkem768::MlKem768PublicKey,
}
impl CiphersuiteBase for InitiatorX25519Mlkem768ChachaPolyHkdfSha256<'_> {
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
    type Ciphertext = MlKem768Ciphertext;
    type EncapsulationKey = MlKem768PublicKey;
    type SharedSecret = MlKemSharedSecret;

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

pub struct InitiatorX25519ChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
}

#[cfg(feature = "classic-mceliece")]
pub struct InitiatorX25519ClassicMcElieceChachaPolyHkdfSha256<'a> {
    pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
    pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
    pub(crate) peer_longterm_cmc_pk: crate::classic_mceliece::PublicKey,
}

pub trait CiphersuiteBase {
    fn name(&self) -> CiphersuiteName;

    fn peer_ecdh_encapsulation_key(&self) -> &DHPublicKey;
    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    fn own_ecdh_encapsulation_key(&self) -> &DHPrivateKey;
}

pub trait InitiatorCiphersuite: CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize;
    type EncapsulationKey: Serialize;
    type SharedSecret: SerializeBytes;

    fn peer_pq_encapsulation_key(&self) -> Option<&Self::EncapsulationKey>;

    fn pq_encapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<(Option<Self::Ciphertext>, Option<Self::SharedSecret>), HandshakeError>;
}

pub trait ResponderCiphersuite: CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize;
    type EncapsulationKey: Serialize;
    type DecapsulationKey;
    type SharedSecret: SerializeBytes;
    fn own_pq_encapsulation_key(&self) -> Option<&Self::EncapsulationKey>;
    fn own_pq_decapsulation_key(&self) -> Option<&Self::DecapsulationKey>;
    fn pq_decapsulate(
        &self,
        rng: &mut impl CryptoRng,
    ) -> Result<Option<Self::SharedSecret>, HandshakeError>;
}

// pub struct RegistrationInitiatorCiphersuite<'a, T: libcrux_traits::kem::KEM> {
//     pub(crate) name: CiphersuiteName,
//     pub(crate) aead: AEAD,
//     pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
//     pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
//     pub(crate) peer_longterm_pq_pk: Option<&'a T::EncapsulationKey>,
// }

// pub struct ResponderCiphersuite<'a> {
//     pub(crate) name: CiphersuiteName,
//     pub(crate) aead: AEAD,
//     pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
//     pub(crate) longterm_pq_keys: Option<PQKeyPair<'a>>,
// }

// pub struct RegistrationInitiatorCiphersuite<'a, T: libcrux_traits::kem::KEM> {
//     pub(crate) name: CiphersuiteName,
//     pub(crate) aead: AEAD,
//     pub(crate) longterm_ecdh_keys: &'a DHKeyPair,
//     pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
//     pub(crate) peer_longterm_pq_pk: Option<&'a T::EncapsulationKey>,
// }

// pub struct QueryInitiatorCiphersuite<'a> {
//     pub(crate) aead: AEAD,
//     pub(crate) peer_longterm_ecdh_pk: &'a DHPublicKey,
// }
