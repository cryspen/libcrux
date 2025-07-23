use std::io::Cursor;

use rand::CryptoRng;

use tls_codec::{
    Deserialize, Serialize, Size, TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes,
};

use crate::protocol::write_output;

use super::{
    dhkem::{DHKeyPair, DHPublicKey},
    initiator::{QueryInitiator, RegistrationInitiator},
    keys::{derive_session_key, AEADKey},
    pqkem::{PQKeyPair, PQPublicKey},
    responder::Responder,
    session::{SessionKey, SESSION_ID_LENGTH},
    transcript::Transcript,
};

#[derive(Debug)]
pub enum Error {
    BuilderState,
    Serialize(tls_codec::Error),
    Deserialize(tls_codec::Error),
    CryptoError,
    InitiatorState,
    ResponderState,
    TransportState,
    OutputBufferShort,
    PayloadTooLong,
    OtherError,
}

#[derive(Debug)]
pub(crate) struct ToTransportState {
    pub(crate) tx2: Transcript,
    pub(crate) k2: AEADKey,
    pub(crate) initiator_ecdh_pk: Option<DHPublicKey>,
}

pub struct Session {
    session_key: SessionKey,
    initiator_ecdh_pk: DHPublicKey,
    responder_ecdh_pk: DHPublicKey,
    responder_pq_pk: Option<PQPublicKey>,
}

impl Session {
    pub(crate) fn new(
        tx2: Transcript,
        k2: AEADKey,
        initiator_ecdh_pk: DHPublicKey,
        responder_ecdh_pk: DHPublicKey,
        responder_pq_pk: Option<PQPublicKey>,
    ) -> Result<Self, Error> {
        Ok(Self {
            session_key: derive_session_key(k2, tx2)?,
            initiator_ecdh_pk,
            responder_ecdh_pk,
            responder_pq_pk,
        })
    }

    pub fn id(&self) -> &[u8; SESSION_ID_LENGTH] {
        &self.session_key.identifier
    }
}

#[derive(TlsSerialize, TlsSize)]
struct TransportMessageOut<'a> {
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16],
}

#[derive(TlsDeserialize, TlsSize)]
struct TransportMessage {
    ciphertext: VLBytes,
    tag: [u8; 16],
}

impl Protocol for Session {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        // We match the maximum payload length of Noise.
        if payload.len() > 65535 {
            return Err(Error::PayloadTooLong);
        }
        let mut ciphertext = vec![0u8; payload.len()];
        let tag = self
            .session_key
            .key
            .encrypt(payload, &[], &mut ciphertext)?;
        let message = TransportMessageOut {
            ciphertext: VLByteSlice(ciphertext.as_ref()),
            tag,
        };

        message
            .tls_serialize(&mut &mut out[..])
            .map_err(|e| Error::Serialize(e))
    }

    fn read_message(&mut self, message: &[u8], out: &mut [u8]) -> Result<(usize, usize), Error> {
        let message = TransportMessage::tls_deserialize(&mut Cursor::new(message))
            .map_err(|e| Error::Deserialize(e))?;

        let bytes_deserialized = message.tls_serialized_len();

        let payload =
            self.session_key
                .key
                .decrypt(message.ciphertext.as_slice(), &message.tag, &[])?;

        let out_bytes_written = write_output(&payload, out)?;

        Ok((bytes_deserialized, out_bytes_written))
    }
}

pub trait IntoTransport {
    fn into_transport_mode(self) -> Result<Session, Error>;
    fn is_handshake_finished(&self) -> bool;
}

pub trait Protocol {
    /// Write a handshake message to `out` to drive the handshake forward.
    ///
    /// The message may include a `payload`. Returns the number of
    /// bytes written to `out`.  If the internal state is not ready to
    /// write a message, nothing is written to `out` and `Ok(0)` is
    /// returned.
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error>;

    /// Reads the bytes in `message` as input to the handshake, and
    /// writes any payload bytes to `payload`.
    ///
    /// Returns a pair of `(bytes_deserialized, bytes_written)`, where
    /// `bytes_deserialized` is the number of bytes read from
    /// `message` and `bytes_written` is the number of bytes written
    /// to `payload`. If the internal state is not ready to read a
    /// message, nothing is written to `payload` and `Ok((0,0))` is
    /// returned.
    fn read_message(&mut self, message: &[u8], payload: &mut [u8])
        -> Result<(usize, usize), Error>;
}

pub struct Builder<'a, Rng: CryptoRng> {
    rng: Rng,
    context: &'a [u8],
    inner_aad: &'a [u8],
    outer_aad: &'a [u8],
    longterm_ecdh_keys: Option<&'a DHKeyPair>,
    longterm_pq_keys: Option<&'a PQKeyPair>,
    peer_longterm_ecdh_pk: Option<&'a DHPublicKey>,
    peer_longterm_pq_pk: Option<&'a PQPublicKey>,
    recent_keys_upper_bound: Option<usize>,
}

impl<'a, Rng: CryptoRng> Builder<'a, Rng> {
    /// Create a new builder.
    pub fn new(rng: Rng) -> Self {
        Self {
            rng,
            context: &[],
            inner_aad: &[],
            outer_aad: &[],
            longterm_ecdh_keys: None,
            longterm_pq_keys: None,
            peer_longterm_ecdh_pk: None,
            peer_longterm_pq_pk: None,
            recent_keys_upper_bound: None,
        }
    }

    // properties

    /// Set the context.
    pub fn context(mut self, context: &'a [u8]) -> Self {
        self.context = context;
        self
    }

    /// Set the inner AAD.
    pub fn inner_aad(mut self, inner_aad: &'a [u8]) -> Self {
        self.inner_aad = inner_aad;
        self
    }

    /// Set the outer AAD.
    pub fn outer_aad(mut self, outer_aad: &'a [u8]) -> Self {
        self.outer_aad = outer_aad;
        self
    }

    /// Set the long-term ECDH key pair.
    pub fn longterm_ecdh_keys(mut self, longterm_ecdh_keys: &'a DHKeyPair) -> Self {
        self.longterm_ecdh_keys = Some(longterm_ecdh_keys);
        self
    }

    /// Set the long-term PQ key pair.
    pub fn longterm_pq_keys(mut self, longterm_pq_keys: &'a PQKeyPair) -> Self {
        self.longterm_pq_keys = Some(longterm_pq_keys);
        self
    }

    /// Set the peer's long-term ECDH public key.
    pub fn peer_longterm_ecdh_pk(mut self, peer_longterm_ecdh_pk: &'a DHPublicKey) -> Self {
        self.peer_longterm_ecdh_pk = Some(peer_longterm_ecdh_pk);
        self
    }

    /// Set the peer's long-term PQ public key.
    pub fn peer_longterm_pq_pk(mut self, peer_longterm_pq_pk: &'a PQPublicKey) -> Self {
        self.peer_longterm_pq_pk = Some(peer_longterm_pq_pk);
        self
    }

    /// Set the maximum number of recent keys stored for DoS protection.
    pub fn recent_keys_upper_bound(mut self, recent_keys_upper_bound: usize) -> Self {
        self.recent_keys_upper_bound = Some(recent_keys_upper_bound);
        self
    }

    // builders

    /// Build a new [`QueryInitiator`].
    ///
    /// This requires that a `responder_ecdh_pk` is set.
    /// It also uses the `context` and `outer_aad`.
    pub fn build_query_initiator(self) -> Result<QueryInitiator<'a>, Error> {
        let Some(responder_ecdh_pk) = self.peer_longterm_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        QueryInitiator::new(responder_ecdh_pk, self.context, self.outer_aad, self.rng)
    }

    /// Build a new [`RegistrationInitiator`].
    ///
    /// This requires that a `longterm_ecdh_keys` and a `peer_longterm_ecdh_pk`
    /// is set.
    /// It also uses the `context`, `inner_aad`, `outer_aad`, and
    /// `peer_longterm_pq_pk`.
    pub fn build_registration_initiator(self) -> Result<RegistrationInitiator<'a, Rng>, Error> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(Error::BuilderState);
        };

        let Some(peer_longterm_ecdh_pk) = self.peer_longterm_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        RegistrationInitiator::new(
            longterm_ecdh_keys,
            peer_longterm_ecdh_pk,
            self.peer_longterm_pq_pk,
            self.context,
            self.inner_aad,
            self.outer_aad,
            self.rng,
        )
    }

    /// Build a new [`Responder`].
    ///
    /// This requires that a `longterm_ecdh_keys`, and `recent_keys_upper_bound` is set.
    /// It also uses the `context`, `outer_aad`, and `longterm_pq_keys`.
    pub fn build_responder(self) -> Result<Responder<'a, Rng>, Error> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(Error::BuilderState);
        };

        let Some(recent_keys_upper_bound) = self.recent_keys_upper_bound else {
            return Err(Error::BuilderState);
        };

        Ok(Responder::new(
            longterm_ecdh_keys,
            self.longterm_pq_keys,
            self.context,
            self.outer_aad,
            recent_keys_upper_bound,
            self.rng,
        ))
    }
}
