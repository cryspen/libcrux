//! # Ciphersuite Traits
//!
//! This module defines common behaviour for all initiator and responder ciphersuites.

use tls_codec::{Deserialize, Serialize, SerializeBytes, Size};

use crate::handshake::{
    ciphersuite::CiphersuiteName,
    dhkem::{DHPrivateKey, DHPublicKey},
    types::ClientAuthenticator,
};

/// Functionality and associated types that are shared in common
/// between initiator and responde ciphersuites.
pub(crate) trait CiphersuiteBase {
    type Ciphertext: Serialize + Deserialize + Size;
    type EncapsulationKeyRef: Serialize + Size;
    type SharedSecret: SerializeBytes + Size;

    fn name(&self) -> CiphersuiteName;
    fn client_authenticator(&self) -> ClientAuthenticator;

    // fn own_ecdh_decapsulation_key(&self) -> &DHPrivateKey;
    // fn own_ecdh_encapsulation_key(&self) -> &DHPublicKey;

    fn tx0(&self, ctx: &[u8], peer_pk: &DHPublicKey) -> Result<Transcript, HandshakeError>;
    fn tx1(&self) -> Result<Transcript, HandshakeError>;
    fn tx2(&self) -> Result<Transcript, HandshakeError>;
    fn k0(&self, tx0: Transcript, peer_pk: &DHPublicKey) -> Result<AEADKey, HandshakeError>;
    fn k1(&self) -> Result<AEADKey, HandshakeError>;
    fn k2(&self) -> Result<AEADKey, HandshakeError>;
}
