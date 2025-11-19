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
//! use libcrux_psq::protocol::api::{Session, Protocol, Builder, IntoSession};
//! use libcrux_psq::protocol::dhkem::DHKeyPair;
//! use libcrux_psq::protocol::pqkem::PQKeyPair;
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
//! let responder_pq_keys = PQKeyPair::new(&mut rng);
//!
//! let responder_ecdh_keys = DHKeyPair::new(&mut rng);
//! let initiator_ecdh_keys = DHKeyPair::new(&mut rng);
//!
//! // Setup initiator
//! let mut initiator = Builder::new(rand::rng())
//!     .outer_aad(aad_initiator_outer)
//!     .inner_aad(aad_initiator_inner)
//!     .context(ctx)
//!     .longterm_ecdh_keys(&initiator_ecdh_keys)
//!     .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk)
//!     .peer_longterm_pq_pk(&responder_pq_keys.pk)
//!     .build_registration_initiator().unwrap();
//!
//! // Setup responder
//! let mut responder = Builder::new(rand::rng())
//!     .context(ctx)
//!     .outer_aad(aad_responder)
//!     .longterm_ecdh_keys(&responder_ecdh_keys)
//!     .recent_keys_upper_bound(30)
//!     .longterm_pq_keys(&responder_pq_keys)
//!     .build_responder().unwrap();
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
//!     Some(&responder_pq_keys.pk),
//! )
//! .unwrap();
//!
//! let mut channel_i = i_transport.channel().unwrap();
//! let mut channel_r = r_transport.channel().unwrap();
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

use api::Error;
use dhkem::DHPublicKey;
use pqkem::PQCiphertext;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

pub mod dhkem;
pub mod initiator;
mod keys;
pub mod pqkem;
pub mod responder;
pub mod session;
mod transcript;

pub mod api;

#[derive(TlsDeserialize, TlsSize)]
pub struct Message {
    pk: DHPublicKey,
    ciphertext: VLBytes,
    tag: [u8; 16],
    aad: VLBytes,
    pq_encapsulation: Option<PQCiphertext>,
}

#[derive(TlsSerialize, TlsSize)]
pub struct MessageOut<'a> {
    pk: &'a DHPublicKey,
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16], // XXX: implement Serialize for &[T; N]
    aad: VLByteSlice<'a>,
    pq_encapsulation: Option<&'a PQCiphertext>,
}

pub(crate) fn write_output(payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    let payload_len = payload.len();
    if out.len() < payload_len {
        return Err(Error::OutputBufferShort);
    }
    out[..payload_len].copy_from_slice(payload);
    Ok(payload_len)
}
