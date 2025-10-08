//! # Ciphersuite Traits
//!
//! This module defines common behaviour for all initiator and responder ciphersuites.

use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, SerializeBytes, Size};

use crate::handshake::{
    ciphersuite::CiphersuiteName,
    dhkem::{DHPrivateKey, DHPublicKey},
    HandshakeError,
};

/// Functionality and associated types that are shared in common
/// between initiator and responde ciphersuites.
pub trait CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize + Size;
    type EncapsulationKeyRef: Serialize + Size;
    type SharedSecret: SerializeBytes + Size;

    fn name(&self) -> CiphersuiteName;

    fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey;
}

/// Functionality provided by initiator ciphersuites.
pub trait InitiatorCiphersuiteTrait: CiphersuiteBase {
    fn is_pq(&self) -> bool;
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

/// Functionality provided by responder ciphersuites.
pub trait ResponderCiphersuiteTrait: CiphersuiteBase {
    type DecapsulationKey;
    fn own_pq_encapsulation_key(&self) -> Option<<Self as CiphersuiteBase>::EncapsulationKeyRef>;

    fn pq_decapsulate(
        &self,
        ciphertext: &<Self as CiphersuiteBase>::Ciphertext,
    ) -> Result<<Self as CiphersuiteBase>::SharedSecret, HandshakeError>;
}
