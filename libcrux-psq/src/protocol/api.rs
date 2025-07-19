use rand::CryptoRng;

use libcrux_ml_kem::mlkem768::{MlKem768KeyPair, MlKem768PublicKey};

use super::{
    ecdh::{KEMKeyPair, PublicKey},
    initiator::{QueryInitiator, RegistrationInitiator},
    responder::Responder,
};

#[derive(Debug)]
pub enum Error {
    BuilderState,
    Serialize(tls_codec::Error),
    Deserialize(tls_codec::Error),
    CryptoError,
    ResponderState,
    OutputBufferShort,
    OtherError,
}

pub struct TransportState;

pub trait IntoTransport {
    fn into_transport_mode(self) -> TransportState;
    fn is_handshake_finished(&self) -> bool;
}

pub trait HandshakeState {
    fn is_initiator(&self) -> bool;

    /// Write a handshake message to `out` to drive the handshake forward.
    /// The message may include a `payload`.
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error>;

    /// Reads the bytes in `message` as input to the handshake, and returns bytes
    /// in the `payload`, if any.
    /// Returns (bytes deserialized, bytes written to payload)
    fn read_message(&mut self, message: &[u8], payload: &mut [u8])
        -> Result<(usize, usize), Error>;
}

pub struct Builder<'a, Rng: CryptoRng> {
    rng: Rng,
    context: &'a [u8],
    inner_aad: &'a [u8],
    outer_aad: &'a [u8],
    longterm_ecdh_keys: Option<&'a KEMKeyPair>,
    longterm_pq_keys: Option<&'a MlKem768KeyPair>,
    peer_longterm_ecdh_pk: Option<&'a PublicKey>,
    peer_longterm_pq_pk: Option<&'a MlKem768PublicKey>,
    recent_keys_len_bound: Option<usize>,
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
            recent_keys_len_bound: None,
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
    pub fn longterm_ecdh_keys(mut self, longterm_ecdh_keys: &'a KEMKeyPair) -> Self {
        self.longterm_ecdh_keys = Some(longterm_ecdh_keys);
        self
    }

    /// Set the long-term PQ key pair.
    pub fn longterm_pq_keys(mut self, longterm_pq_keys: &'a MlKem768KeyPair) -> Self {
        self.longterm_pq_keys = Some(longterm_pq_keys);
        self
    }

    /// Set the peer's long-term ECDH public key.
    pub fn peer_longterm_ecdh_pk(mut self, peer_longterm_ecdh_pk: &'a PublicKey) -> Self {
        self.peer_longterm_ecdh_pk = Some(peer_longterm_ecdh_pk);
        self
    }

    /// Set the peer's long-term PQ public key.
    pub fn peer_longterm_pq_pk(mut self, peer_longterm_pq_pk: &'a MlKem768PublicKey) -> Self {
        self.peer_longterm_pq_pk = Some(peer_longterm_pq_pk);
        self
    }

    /// Set the number of recent keys, stored for DoS protection.
    pub fn bound_recent_keys_by(mut self, recent_keys_len_bound: usize) -> Self {
        self.recent_keys_len_bound = Some(recent_keys_len_bound);
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
    /// This requires that a `longterm_ecdh_keys`, and `recent_keys_len_bound` is set.
    /// It also uses the `context`, `outer_aad`, and `longterm_pq_keys`.
    pub fn build_responder(self) -> Result<Responder<'a, Rng>, Error> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(Error::BuilderState);
        };

        let Some(recent_keys_len_bound) = self.recent_keys_len_bound else {
            return Err(Error::BuilderState);
        };

        Ok(Responder::new(
            longterm_ecdh_keys,
            self.longterm_pq_keys,
            self.context,
            self.outer_aad,
            recent_keys_len_bound,
            self.rng,
        ))
    }
}
