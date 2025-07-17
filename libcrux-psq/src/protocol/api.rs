use rand::CryptoRng;

use crate::protocol::{ecdh::PublicKey, initiator::QueryInitiator, responder::Responder};

use libcrux_ml_kem::mlkem768::{MlKem768KeyPair, MlKem768PublicKey};

use super::{ecdh::KEMKeyPair, initiator::RegistrationInitiator};

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
}

pub trait HandshakeState {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error>;
    // Returns (bytes deserialized, bytes written to payload)
    fn read_message(&mut self, message: &[u8], payload: &mut [u8])
        -> Result<(usize, usize), Error>;
}

pub struct Builder<'a, Rng: CryptoRng> {
    rng: &'a mut Rng,
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
    pub fn new(rng: &'a mut Rng) -> Self {
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
    pub fn context(mut self, context: &'a [u8]) -> Self {
        self.context = context;
        self
    }

    pub fn inner_aad(mut self, inner_aad: &'a [u8]) -> Self {
        self.inner_aad = inner_aad;
        self
    }

    pub fn outer_aad(mut self, outer_aad: &'a [u8]) -> Self {
        self.outer_aad = outer_aad;
        self
    }

    pub fn longterm_ecdh_keys(mut self, longterm_ecdh_keys: &'a KEMKeyPair) -> Self {
        self.longterm_ecdh_keys = Some(longterm_ecdh_keys);
        self
    }

    pub fn longterm_pq_keys(mut self, longterm_pq_keys: &'a MlKem768KeyPair) -> Self {
        self.longterm_pq_keys = Some(longterm_pq_keys);
        self
    }

    pub fn peer_longterm_ecdh_pk(mut self, peer_longterm_ecdh_pk: &'a PublicKey) -> Self {
        self.peer_longterm_ecdh_pk = Some(peer_longterm_ecdh_pk);
        self
    }

    pub fn peer_longterm_pq_pk(mut self, peer_longterm_pq_pk: &'a MlKem768PublicKey) -> Self {
        self.peer_longterm_pq_pk = Some(peer_longterm_pq_pk);
        self
    }

    pub fn bound_recent_keys_by(mut self, recent_keys_len_bound: usize) -> Self {
        self.recent_keys_len_bound = Some(recent_keys_len_bound);
        self
    }

    // builders
    pub fn build_query_initiator(self) -> Result<QueryInitiator<'a>, Error> {
        let Some(responder_ecdh_pk) = self.peer_longterm_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        QueryInitiator::new(responder_ecdh_pk, self.context, self.outer_aad, self.rng)
    }

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

    pub fn build_responder(self) -> Result<Responder<'a, Rng>, Error> {
        let Some(longterm_ecdh_keys) = self.longterm_ecdh_keys else {
            return Err(Error::BuilderState);
        };

        let Some(longterm_pq_keys) = self.longterm_pq_keys else {
            return Err(Error::BuilderState);
        };

        let Some(recent_keys_len_bound) = self.recent_keys_len_bound else {
            return Err(Error::BuilderState);
        };

        Ok(Responder::new(
            longterm_ecdh_keys,
            longterm_pq_keys,
            self.context,
            self.outer_aad,
            recent_keys_len_bound,
            self.rng,
        ))
    }
}
