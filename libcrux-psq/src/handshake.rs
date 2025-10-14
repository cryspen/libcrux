//! # The PSQ Handshake
//!
//! The PSQ handshake consists of one message from the initiator to the
//! responder, and one response from the responder. It supports two modes:
//! - Query mode: A stateless, classically secure protocol which allows
//!   the initiator to send one query payload to the responder, which in
//!   turn sends one query response payload to the initiator.
//! - Registration mode: An (optionally) HNDL-secure protocol, which allows the
//!   initiator to register its long-term classical public key with the
//!   responder in a long-term session. The initiator's long-term public
//!   key is transmitted encrypted under the responders long-term public
//!   key, and thus not revealed to an eavesdropping attacker.

#![allow(missing_docs)]

#[derive(Debug, PartialEq)]
pub enum HandshakeError {
    Serialize(tls_codec::Error),
    Deserialize(tls_codec::Error),
    CryptoError,
    InitiatorState,
    ResponderState,
    TransportState,
    OutputBufferShort,
    PayloadTooLong,
    ChannelError,
    UnsupportedCiphersuite,
    Storage,
    OtherError,
    IdentifierMismatch,
    InvalidMessage,
}

impl From<AEADError> for HandshakeError {
    fn from(value: AEADError) -> Self {
        match value {
            AEADError::CryptoError => HandshakeError::CryptoError,
            AEADError::Serialize(error) => HandshakeError::Serialize(error),
            AEADError::Deserialize(error) => HandshakeError::Deserialize(error),
        }
    }
}

use tls_codec::{TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize, VLByteSlice, VLBytes};
use transcript::Transcript;

use crate::{
    aead::{AEADError, AEADKey},
    handshake::{
        ciphersuite::{types::PQSharedSecret, CiphersuiteName},
        dhkem::{DHPrivateKey, DHPublicKey, DHSharedSecret},
    },
};

pub(crate) mod dhkem;
pub(crate) mod initiator;
// pub mod pqkem;
pub(crate) mod responder;
pub(crate) mod transcript;

pub(crate) mod builder;
pub(crate) mod ciphersuite;

#[derive(Debug)]
pub(crate) struct ToTransportState {
    pub(crate) tx2: Transcript,
    pub(crate) k2: AEADKey,
    pub(crate) initiator_ecdh_pk: Option<DHPublicKey>,
    pub(crate) pq: bool,
}

#[derive(TlsDeserialize, TlsSize)]
/// A PSQ handshake message.
pub(crate) struct HandshakeMessage {
    /// A Diffie-Hellman KEM public key
    pk: DHPublicKey,
    /// The AEAD-encrypted message payload
    ciphertext: VLBytes,
    /// AEAD tag authenticating the ciphertext and any AAD
    tag: [u8; 16],
    /// Associated data, covered by the AEAD message authentication tag
    aad: VLBytes,
    /// The handshake ciphersuite for this message
    ciphersuite: CiphersuiteName,
    /// An optional post-quantum key encapsulation
    pq_encapsulation: VLBytes,
}

#[derive(TlsSerialize, TlsSize)]
/// A PSQ handshake message. (Serialization helper)
pub(crate) struct HandshakeMessageOut<'a> {
    pk: &'a DHPublicKey,
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16], // XXX: implement Serialize for &[T; N]
    aad: VLByteSlice<'a>,
    ciphersuite: CiphersuiteName,
    pq_encapsulation: VLByteSlice<'a>,
}

pub(crate) fn write_output(payload: &[u8], out: &mut [u8]) -> Result<usize, HandshakeError> {
    let payload_len = payload.len();
    if out.len() < payload_len {
        return Err(HandshakeError::OutputBufferShort);
    }
    out[..payload_len].copy_from_slice(payload);
    Ok(payload_len)
}

// K0 = KDF(g^xs, tx0)
pub(super) fn derive_k0(
    peer_pk: &DHPublicKey,
    own_pk: &DHPublicKey,
    own_sk: &DHPrivateKey,
    ctx: &[u8],
    is_responder: bool,
) -> Result<(Transcript, AEADKey), HandshakeError> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K0Ikm<'a> {
        g_xs: &'a DHSharedSecret,
    }

    let tx0 = if is_responder {
        transcript::tx0(ctx, own_pk, peer_pk)?
    } else {
        transcript::tx0(ctx, peer_pk, own_pk)?
    };
    let ikm = K0Ikm {
        g_xs: &DHSharedSecret::derive(own_sk, peer_pk)?,
    };

    Ok((tx0, AEADKey::new(&ikm, &tx0)?))
}

// K1 = KDF(K0 | g^cs | SS, tx1)
pub(super) fn derive_k1(
    k0: &AEADKey,
    own_longterm_key: &DHPrivateKey,
    peer_longterm_pk: &DHPublicKey,
    pq_shared_secret: Option<PQSharedSecret>,
    tx1: &Transcript,
) -> Result<AEADKey, HandshakeError> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K1Ikm<'a> {
        k0: &'a AEADKey,
        ecdh_shared_secret: &'a DHSharedSecret,
        pq_shared_secret: Option<PQSharedSecret>,
    }

    let ecdh_shared_secret = DHSharedSecret::derive(own_longterm_key, peer_longterm_pk)?;

    // XXX: This makes clippy unhappy, but is a lifetime error for feature `classic-mceliece` if we return directlyr
    Ok(AEADKey::new(
        &K1Ikm {
            k0,
            ecdh_shared_secret: &ecdh_shared_secret,
            pq_shared_secret,
        },
        &tx1,
    )?)
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2IkmQuery<'a> {
    k0: &'a AEADKey,
    g_xs: &'a DHSharedSecret,
    g_xy: &'a DHSharedSecret,
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2IkmRegistration<'a, 'b> {
    k1: &'a AEADKey,
    g_cy: &'b DHSharedSecret,
    g_xy: &'b DHSharedSecret,
}

pub mod builders {
    #[derive(Debug, PartialEq)]
    pub enum BuilderError {
        CiphersuiteBuilderState,
        PrincipalBuilderState,
        UnsupportedCiphersuite,
    }

    #[doc(inline)]
    pub use crate::handshake::builder::PrincipalBuilder;
    #[doc(inline)]
    pub use crate::handshake::ciphersuite::builder::CiphersuiteBuilder;
}

pub mod types {
    #[doc(inline)]
    pub use crate::handshake::ciphersuite::types::*;
    #[doc(inline)]
    pub use crate::handshake::dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey};
}

pub mod ciphersuites {
    #[doc(inline)]
    pub use crate::handshake::ciphersuite::{
        initiator::InitiatorCiphersuite, responder::ResponderCiphersuite, CiphersuiteName,
    };
}

#[doc(inline)]
pub use initiator::query::QueryInitiator;

#[doc(inline)]
pub use initiator::registration::RegistrationInitiator;

#[doc(inline)]
pub use responder::Responder;
