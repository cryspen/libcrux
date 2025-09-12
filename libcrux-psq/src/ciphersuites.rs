//! Ciphersuites for PSQ.

// XXX: We could also put the keys into each ciphersuite.

use std::convert::Infallible;

use libcrux_kem::{MlKem768PrivateKey, MlKem768PublicKey};
use libcrux_ml_kem::mlkem768::MlKem768KeyPair;

use crate::handshake::{
    dhkem::DHKeyPair,
    pqkem::{PQKeyPair, PQPublicKey},
};

/// Ciphersuites for the PSQ query protocol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryCiphersuite {
    /// KEM: x25519, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256
    X25519ChachaPolyHkdfSha256,

    /// KEM: x25519, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256, ML-DSA 65
    X25519ChachaPolyHkdfSha256Mldsa65,
}

/// Ciphersuites for the PSQ registration protocol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistrationCiphersuite {
    /// KEM: x25519 ML-KEM 768, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256
    X25519Mlkem768ChachaPolyHkdfSha256,

    /// KEM: x25519 McEliece 460896, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256
    X25519McElieceChachaPolyHkdfSha256,

    /// KEM: x25519 ML-KEM 768, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256, ML-DSA 65
    X25519Mlkem768ChachaPolyHkdfSha256Mldsa65,

    /// KEM: x25519 McEliece 460896, AEAD: ChaChaPoly1305, KDF: HKDF-Sha256, ML-DSA 65
    X25519McElieceChachaPolyHkdfSha256Mldsa65,
}

/// Ciphersuites for the PSQ protocol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ciphersuite {
    /// Query mode
    QueryCiphersuite(QueryCiphersuite),

    /// Registration mode
    RegistrationCiphersuite(RegistrationCiphersuite),
}

/// The ciphersuites for the PSQ protocol
pub trait CiphersuiteTrait {
    /// The PQ Key pair type.
    type PQKeypair;

    /// The PQ encaps key type.
    type PQEncapsKey;

    /// The PQ decaps key type.
    type PQDecapsKey;

    /// The name (identifier) of this ciphersuite.
    fn name() -> &'static str;

    /// Returns `true` if this is a query ciphersuite.
    /// XXX: are these really needed?
    fn query() -> bool;

    /// Returns `true` if this is a registration ciphersuite.
    fn registration() -> bool;

    /// Convert the pq encaps key to a [`PQPublicKey`].
    ///
    /// XXX: drop if we don't need to convert anymore
    fn pq_encaps_key<'a>(pk: &'a Self::PQEncapsKey) -> PQPublicKey<'a>;

    /// Convert the pq key pair to a [`PQKeyPair`].
    ///
    /// XXX: drop if we don't need to convert anymore
    fn pq_keypair<'a>(kp: &'a Self::PQKeypair) -> PQKeyPair<'a>;
}

/// X25519ChachaPolyHkdfSha256
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X25519ChachaPolyHkdfSha256;
impl CiphersuiteTrait for X25519ChachaPolyHkdfSha256 {
    type PQKeypair = Infallible;
    type PQEncapsKey = Infallible;
    type PQDecapsKey = Infallible;

    fn name() -> &'static str {
        "X25519ChachaPolyHkdfSha256"
    }

    fn query() -> bool {
        true
    }

    fn registration() -> bool {
        false
    }

    fn pq_encaps_key<'a>(_: &'a Self::PQEncapsKey) -> PQPublicKey<'a> {
        unreachable!()
    }

    fn pq_keypair<'a>(_: &'a Self::PQKeypair) -> PQKeyPair<'a> {
        unreachable!()
    }
}

/// X25519Mlkem768ChachaPolyHkdfSha256
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X25519Mlkem768ChachaPolyHkdfSha256;
impl CiphersuiteTrait for X25519Mlkem768ChachaPolyHkdfSha256 {
    type PQKeypair = MlKem768KeyPair;
    type PQEncapsKey = MlKem768PublicKey;
    type PQDecapsKey = MlKem768PrivateKey;

    fn name() -> &'static str {
        "MlKem768KeyPair"
    }

    fn query() -> bool {
        true
    }

    fn registration() -> bool {
        true
    }

    fn pq_encaps_key<'a>(pk: &'a Self::PQEncapsKey) -> PQPublicKey<'a> {
        PQPublicKey::MlKem768(pk)
    }

    fn pq_keypair<'a>(kp: &'a Self::PQKeypair) -> PQKeyPair<'a> {
        PQKeyPair::MlKem768 {
            pk: kp.public_key(),
            sk: kp.private_key(),
        }
    }
}

/// X25519McElieceChachaPolyHkdfSha256
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X25519McElieceChachaPolyHkdfSha256;
impl CiphersuiteTrait for X25519McElieceChachaPolyHkdfSha256 {
    type PQKeypair = crate::classic_mceliece::KeyPair;
    type PQEncapsKey = crate::classic_mceliece::PublicKey;
    type PQDecapsKey = crate::classic_mceliece::SecretKey;

    fn name() -> &'static str {
        "X25519McElieceChachaPolyHkdfSha256"
    }

    fn query() -> bool {
        true
    }

    fn registration() -> bool {
        true
    }

    fn pq_encaps_key<'a>(pk: &'a Self::PQEncapsKey) -> PQPublicKey<'a> {
        PQPublicKey::ClassicMcEliece(pk)
    }

    fn pq_keypair<'a>(kp: &'a Self::PQKeypair) -> PQKeyPair<'a> {
        PQKeyPair::ClassicMcEliece {
            pk: &kp.pk,
            sk: &kp.sk,
        }
    }
}
