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
//! See below for an example of the registration handshake:
//! ```rust
//! use libcrux_psq::{
//!     aead::*,
//!     session::Session,
//!     traits::*,
//!     handshake::{
//!         pqkem::PQKeyPair,
//!         dhkem::DHKeyPair,
//!         builder::BuilderContext,
//!         ciphersuite::*,
//!     }
//! };
//!
//! let mut rng = rand::rng();
//! let ctx = b"Test Context";
//! let aad_initiator_outer = b"Test Data I Outer";
//! let aad_initiator_inner = b"Test Data I Inner";
//! let aad_responder = b"Test Data R";
//!
//! let mut msg_channel = vec![0u8; 4096];
//! let mut payload_buf_responder = vec![0u8; 4096];
//! let mut payload_buf_initiator = vec![0u8; 4096];
//!
//! // External setup
//! let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);
//!
//! let responder_ecdh_keys = DHKeyPair::new(&mut rng);
//! let initiator_ecdh_keys = DHKeyPair::new(&mut rng);
//!
//!
//! // Setup initiator
//! let initiator_ciphersuite = CiphersuiteBuilder::new()
//!     .aead(AEAD::ChaChaPoly1305)
//!     .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk)
//!     .longterm_ecdh_keys(&initiator_ecdh_keys)
//!     .peer_longterm_pq_pk(responder_pq_keys.public_key())
//!     .build_registration_initiator_ciphersuite()
//!     .unwrap();
//!
//! let mut initiator = BuilderContext::new(rand::rng())
//!     .outer_aad(aad_initiator_outer)
//!     .inner_aad(aad_initiator_inner)
//!     .context(ctx)
//!     .build_registration_initiator(initiator_ciphersuite)
//!     .unwrap();
//!
//! // Setup responder
//! let responder_ciphersuite = CiphersuiteBuilder::new()
//!     .aead(AEAD::ChaChaPoly1305)
//!     .longterm_ecdh_keys(&responder_ecdh_keys)
//!     .longterm_pq_keys(&responder_pq_keys)
//!     .build_responder_ciphersuite()
//!     .unwrap();
//!
//! let mut responder = BuilderContext::new(rand::rng())
//!     .context(ctx)
//!     .outer_aad(aad_responder)
//!     .recent_keys_upper_bound(30)
//!     .build_responder(responder_ciphersuite)
//!     .unwrap();
//!
//! // Send first message
//! let registration_payload_initiator = b"Registration_init";
//! let len_i = initiator
//!     .write_message(registration_payload_initiator, &mut msg_channel)
//!     .unwrap();
//!
//! // Read first message
//! let (len_r_deserialized, len_r_payload) = responder
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

#[derive(Debug)]
pub enum HandshakeError {
    BuilderState,
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

use dhkem::{DHPrivateKey, DHPublicKey, DHSharedSecret};
// use pqkem::{PQCiphertext, PQSharedSecret};
use tls_codec::{
    Deserialize, Serialize, SerializeBytes, TlsDeserialize, TlsSerialize, TlsSerializeBytes,
    TlsSize, VLByteSlice, VLBytes,
};
use transcript::Transcript;

use crate::aead::{AEADError, AEADKey};

pub mod dhkem;
pub mod initiator;
// pub mod pqkem;
pub mod responder;
pub(crate) mod transcript;

pub mod builder;
pub mod ciphersuite;

#[derive(Debug)]
pub(crate) struct ToTransportState {
    pub(crate) tx2: Transcript,
    pub(crate) k2: AEADKey,
    pub(crate) initiator_ecdh_pk: Option<DHPublicKey>,
}

#[derive(TlsDeserialize, TlsSize)]
/// A PSQ handshake message.
pub struct HandshakeMessage<T: Deserialize> {
    /// A Diffie-Hellman KEM public key
    pk: DHPublicKey,
    /// The AEAD-encrypted message payload
    ciphertext: VLBytes,
    /// AEAD tag authenticating the ciphertext and any AAD
    tag: [u8; 16],
    /// Associated data, covered by the AEAD message authentication tag
    aad: VLBytes,
    /// An optional post-quantum key encapsulation
    pq_encapsulation: Option<T>,
}

#[derive(TlsSerialize, TlsSize)]
/// A PSQ handshake message. (Serialization helper)
pub struct HandshakeMessageOut<'a, T: Serialize> {
    pk: &'a DHPublicKey,
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16], // XXX: implement Serialize for &[T; N]
    aad: VLByteSlice<'a>,
    pq_encapsulation: Option<&'a T>,
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
pub(super) fn derive_k1<T: SerializeBytes>(
    k0: &AEADKey,
    own_longterm_key: &DHPrivateKey,
    peer_longterm_pk: &DHPublicKey,
    pq_shared_secret: Option<T>,
    tx1: &Transcript,
) -> Result<AEADKey, HandshakeError> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K1Ikm<'a, 'b, T: SerializeBytes> {
        k0: &'a AEADKey,
        ecdh_shared_secret: &'b DHSharedSecret,
        pq_shared_secret: Option<T>,
    }

    let ecdh_shared_secret = DHSharedSecret::derive(own_longterm_key, peer_longterm_pk)?;

    AEADKey::new(
        &K1Ikm {
            k0,
            ecdh_shared_secret: &ecdh_shared_secret,
            pq_shared_secret,
        },
        &tx1,
    )
    .map_err(|e| e.into())
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
