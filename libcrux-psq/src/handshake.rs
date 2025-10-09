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
//!
//!
//!     .read_message(&msg_channel, &mut payload_buf_responder)
//!     .unwrap();
//!
//! // We read the same amount of data.
//! assert_eq!(len_r_deserialized, len_i);
//! assert_eq!(len_r_payload, registration_payload_initiator.len());
//! assert_eq!(
//!     &payload_buf_responder[0..len_r_payload],
//!     registration_payload_initiator
//! );
//!
//! // Respond
//! let registration_payload_responder = b"Registration_respond";
//! let len_r = responder
//!     .write_message(registration_payload_responder, &mut msg_channel)
//!     .unwrap();
//!
//! // Finalize on registration initiator
//! let (len_i_deserialized, len_i_payload) = initiator
//!     .read_message(&msg_channel, &mut payload_buf_initiator)
//!     .unwrap();
//!
//! // We read the same amount of data.
//! assert_eq!(len_r, len_i_deserialized);
//! assert_eq!(registration_payload_responder.len(), len_i_payload);
//! assert_eq!(
//!     &payload_buf_initiator[0..len_i_payload],
//!     registration_payload_responder
//! );
//!
//! // Ready for transport mode
//! assert!(initiator.is_handshake_finished());
//! assert!(responder.is_handshake_finished());
//!
//! let i_transport = initiator.into_session().unwrap();
//! let mut r_transport = responder.into_session().unwrap();
//!
//! // test serialization, deserialization
//! i_transport.serialize(&mut msg_channel).unwrap();
//! let mut i_transport = Session::deserialize(
//!     &msg_channel,
//!     &initiator_ecdh_keys.pk,
//!     &responder_ecdh_keys.pk,
//!     Some(responder_pq_keys.public_key().into()),
//! )
//! .unwrap();
//!
//! let mut channel_i = i_transport.transport_channel().unwrap();
//! let mut channel_r = r_transport.transport_channel().unwrap();
//!
//! assert_eq!(channel_i.identifier(), channel_r.identifier());
//!
//! let app_data_i = b"Derived session hey".as_slice();
//! let app_data_r = b"Derived session ho".as_slice();
//!
//! let len_i = channel_i
//!     .write_message(app_data_i, &mut msg_channel)
//!     .unwrap();
//!
//! let (len_r_deserialized, len_r_payload) = channel_r
//!     .read_message(&msg_channel, &mut payload_buf_responder)
//!     .unwrap();
//!
//! // We read the same amount of data.
//! assert_eq!(len_r_deserialized, len_i);
//! assert_eq!(len_r_payload, app_data_i.len());
//! assert_eq!(&payload_buf_responder[0..len_r_payload], app_data_i);
//!
//! let len_r = channel_r
//!     .write_message(app_data_r, &mut msg_channel)
//!     .unwrap();
//!
//! let (len_i_deserialized, len_i_payload) = channel_i
//!     .read_message(&msg_channel, &mut payload_buf_initiator)
//!     .unwrap();
//!
//! assert_eq!(len_r, len_i_deserialized);
//! assert_eq!(app_data_r.len(), len_i_payload);
//! assert_eq!(&payload_buf_initiator[0..len_i_payload], app_data_r);
//! ```
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
        pq_shared_secret: Option<PQSharedSecret<'a>>,
    }

    let ecdh_shared_secret = DHSharedSecret::derive(own_longterm_key, peer_longterm_pk)?;

    let k1 = AEADKey::new(
        &K1Ikm {
            k0,
            ecdh_shared_secret: &ecdh_shared_secret,
            pq_shared_secret,
        },
        &tx1,
    )
    .map_err(|e| e.into());
    k1
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
