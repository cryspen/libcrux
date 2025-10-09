//! # Longterm Session
//!
//! This module implements long-term sessions derived from PSQ handshakes.

mod session_key;
mod transport;

use std::io::Cursor;

use libcrux_hkdf::Algorithm;
use session_key::{derive_session_key, SessionKey, SESSION_ID_LENGTH};
use tls_codec::{
    Deserialize, Serialize, SerializeBytes, Size, TlsDeserialize, TlsSerialize, TlsSize,
};
use transport::Transport;

use crate::{
    aead::{AEADError, AEADKey},
    handshake::{
        ciphersuite::types::PQEncapsulationKey, dhkem::DHPublicKey, transcript::Transcript,
    },
};

/// Session related errors
#[derive(Debug, PartialEq)]
pub enum SessionError {
    /// An error during session creation
    IntoSession,
    /// An error during serialization using TLSCodec
    Serialize(tls_codec::Error),
    /// An error during deserialization using TLSCodec
    Deserialize(tls_codec::Error),
    /// The given channel payload exceeded the maximum length
    PayloadTooLong(usize),
    /// An error in an underlying cryptographic primitive
    CryptoError,
    /// An error in storing or loading a session state
    Storage,
    /// The maxmium number of derivable channels has been reached
    ReachedMaxChannels,
    /// A channel message contains an inappropriate channel identifier
    IdentifierMismatch,
    /// The given payload exceeds the available output buffer
    OutputBufferShort,
}

impl From<AEADError> for SessionError {
    fn from(value: AEADError) -> Self {
        match value {
            AEADError::CryptoError => SessionError::CryptoError,
            AEADError::Serialize(error) => SessionError::Serialize(error),
            AEADError::Deserialize(error) => SessionError::Deserialize(error),
        }
    }
}
/// The length of the public key binder in bytes.
pub(crate) const PK_BINDER_LEN: usize = 8;

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
#[repr(u8)]
/// The holder of a `Session` struct.
///
/// Note that this refers only to the roles during the initial handshake,
/// as either peer can initiate a secure channel from a session.
pub(crate) enum SessionPrincipal {
    /// The handshake initiator
    Initiator,
    /// The handshake responder
    Responder,
}

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
/// A long-term session derived from the final handshake state.
///
/// Allows the creation of up to `u64::MAX` distinct, bi-directional
/// secure `Channel`s between initiator and responder, via
/// `Session::channel`.
///
/// The `Session` can be stored using `Session::serialize` and loaded
/// using `Session::deserialize`, which expects references to the same
/// public keys that were used in session creation to succeed.
///
/// **Warning**: Session state must only be stored and loaded using
/// `Session::serialize` and `Session::deserialize`.  While `Session`
/// implements `tls_codec::{Serialize, Deserialize}`, the associated
/// methods should not be called directly, since they do not consume the
/// `Session`. This opens up the possibility of continual use of a session
/// that has also been serialized. If the serialized session is then
/// deserialized, the deserialized version is stale and using it to
/// re-derive `Channel`s will result in nonce re-use with the potential
/// for loss of confidentiality.
pub struct Session {
    /// Which handshake party holds the `Session`
    pub(crate) principal: SessionPrincipal,
    /// The long-term session key derived from the handshake
    pub(crate) session_key: SessionKey,
    /// Binds this `Session` to the long-term public key material of both
    /// parties that was used during the handshake
    pub(crate) pk_binder: [u8; PK_BINDER_LEN],
    /// An increasing counter of derived secure channels
    pub(crate) channel_counter: u64,
}

// pkBinder = KDF(skCS, g^c | g^s | [pkS])
fn derive_pk_binder(
    key: &SessionKey,
    initiator_ecdh_pk: &DHPublicKey,
    responder_ecdh_pk: &DHPublicKey,
    responder_pq_pk: Option<PQEncapsulationKey>,
) -> Result<[u8; PK_BINDER_LEN], SessionError> {
    #[derive(TlsSerialize, TlsSize)]
    struct PkBinderInfo<'a> {
        initiator_ecdh_pk: &'a DHPublicKey,
        responder_ecdh_pk: &'a DHPublicKey,
        responder_pq_pk: Option<PQEncapsulationKey<'a>>,
    }

    let info = PkBinderInfo {
        initiator_ecdh_pk,
        responder_ecdh_pk,
        responder_pq_pk,
    };
    let mut info_buf = vec![0u8; info.tls_serialized_len()];
    info.tls_serialize(&mut &mut info_buf[..])
        .map_err(SessionError::Serialize)?;

    let prk = libcrux_hkdf::extract(
        Algorithm::Sha256,
        [],
        SerializeBytes::tls_serialize(&key.key).map_err(SessionError::Serialize)?,
    )
    .map_err(|_| SessionError::CryptoError)?;

    libcrux_hkdf::expand(Algorithm::Sha256, prk, info_buf, PK_BINDER_LEN)
        .map_err(|_| SessionError::CryptoError)?
        .try_into()
        .map_err(|_| SessionError::CryptoError)
}

impl Session {
    /// Create a new `Session`.
    ///
    /// This will derive the long-term session key, and compute a binder tying
    /// the session key to any long-term public key material that was used during the
    /// handshake.
    pub(crate) fn new(
        tx2: Transcript,
        k2: AEADKey,
        initiator_ecdh_pk: &DHPublicKey,
        responder_ecdh_pk: &DHPublicKey,
        responder_pq_pk: Option<PQEncapsulationKey>,
        is_initiator: bool,
    ) -> Result<Self, SessionError> {
        let session_key = derive_session_key(k2, tx2)?;
        let pk_binder = derive_pk_binder(
            &session_key,
            initiator_ecdh_pk,
            responder_ecdh_pk,
            responder_pq_pk,
        )?;
        Ok(Self {
            principal: if is_initiator {
                SessionPrincipal::Initiator
            } else {
                SessionPrincipal::Responder
            },
            session_key,
            pk_binder,
            channel_counter: 0,
        })
    }

    /// Serializes the session state for storage.
    ///
    /// WARN: `tls_serialize` should not be called directly, since it does
    /// not consume `Session`. This opens the possibility for nonce
    /// re-use by deserializing a stale `Session` since the original
    /// could be used after serialization.
    pub fn serialize(self, out: &mut [u8]) -> Result<usize, SessionError> {
        self.tls_serialize(&mut &mut out[..])
            .map_err(SessionError::Serialize)
    }

    /// Deserialize a session state.
    ///
    /// The public key inputs must be the same as those used originally to derive the
    /// stored session and are used to validate the public key binding of the
    /// session key.
    // XXX: Use `tls_codec::conditional_deserializable` to implement
    // the validation.
    pub fn deserialize(
        bytes: &[u8],
        initiator_ecdh_pk: &DHPublicKey,
        responder_ecdh_pk: &DHPublicKey,
        responder_pq_pk: Option<PQEncapsulationKey>,
    ) -> Result<Self, SessionError> {
        let session =
            Session::tls_deserialize(&mut Cursor::new(bytes)).map_err(SessionError::Deserialize)?;

        if derive_pk_binder(
            &session.session_key,
            initiator_ecdh_pk,
            responder_ecdh_pk,
            responder_pq_pk,
        )? == session.pk_binder
        {
            Ok(session)
        } else {
            Err(SessionError::Storage)
        }
    }

    /// Derive a new secure transport channel from the session state.
    ///
    /// The new transport channel allows both peers to send and receive
    /// messages AEAD encrypted under a fresh channel key derived from the
    /// long-term session key.
    pub fn transport_channel(&mut self) -> Result<Transport, SessionError> {
        let channel = Transport::new(self, matches!(self.principal, SessionPrincipal::Initiator))?;
        self.channel_counter = self
            .channel_counter
            .checked_add(1)
            .ok_or(SessionError::ReachedMaxChannels)?;
        Ok(channel)
    }

    /// Output the channel identifier.
    pub fn identifier(&self) -> &[u8; SESSION_ID_LENGTH] {
        &self.session_key.identifier
    }
}
