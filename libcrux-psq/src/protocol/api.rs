use rand::CryptoRng;

use crate::protocol::{
    ecdh::{PrivateKey, PublicKey},
    initiator::{InitiatorOuterPayload, QueryInitiator},
    keys::AEADKey,
    responder::{Responder, ResponderState},
    transcript::Transcript,
};

use libcrux_ml_kem::mlkem768::{MlKem768PrivateKey, MlKem768PublicKey};

use super::initiator::RegistrationInitiator;

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
    responder_ecdh_pk: Option<&'a PublicKey>,
    responder_ecdh_sk: Option<&'a PrivateKey>,
    initiator_ecdh_pk: Option<&'a PublicKey>,
    initiator_ecdh_sk: Option<&'a PrivateKey>,
    responder_pq_pk: Option<&'a MlKem768PublicKey>,
    responder_pq_sk: Option<&'a MlKem768PrivateKey>,
}

impl<'a, Rng: CryptoRng> Builder<'a, Rng> {
    pub fn new(rng: &'a mut Rng) -> Self {
        Self {
            rng,
            context: &[],
            inner_aad: &[],
            outer_aad: &[],
            responder_ecdh_pk: None,
            responder_ecdh_sk: None,
            initiator_ecdh_pk: None,
            initiator_ecdh_sk: None,

            responder_pq_pk: None,
            responder_pq_sk: None,
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

    pub fn responder_ecdh_pk(mut self, responder_ecdh_pk: &'a PublicKey) -> Self {
        self.responder_ecdh_pk = Some(responder_ecdh_pk);
        self
    }

    pub fn responder_ecdh_sk(mut self, responder_ecdh_sk: &'a PrivateKey) -> Self {
        self.responder_ecdh_sk = Some(responder_ecdh_sk);
        self
    }

    pub fn responder_pq_pk(mut self, responder_pq_pk: &'a MlKem768PublicKey) -> Self {
        self.responder_pq_pk = Some(responder_pq_pk);
        self
    }

    pub fn responder_pq_sk(mut self, responder_pq_sk: &'a MlKem768PrivateKey) -> Self {
        self.responder_pq_sk = Some(responder_pq_sk);
        self
    }

    pub fn initiator_ecdh_sk(mut self, initiator_ecdh_sk: &'a PrivateKey) -> Self {
        self.initiator_ecdh_sk = Some(initiator_ecdh_sk);
        self
    }

    pub fn initiator_ecdh_pk(mut self, initiator_ecdh_pk: &'a PublicKey) -> Self {
        self.initiator_ecdh_pk = Some(initiator_ecdh_pk);
        self
    }

    // builders
    pub fn build_query_initiator(self) -> Result<QueryInitiator<'a>, Error> {
        let Some(responder_ecdh_pk) = self.responder_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        Ok(QueryInitiator::new(
            responder_ecdh_pk,
            self.context,
            self.outer_aad,
            self.rng,
        )?)
    }

    pub fn build_registration_initiator(self) -> Result<RegistrationInitiator<'a, Rng>, Error> {
        let Some(responder_ecdh_pk) = self.responder_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        let Some(initiator_ecdh_pk) = self.initiator_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        let Some(initiator_ecdh_sk) = self.initiator_ecdh_sk else {
            return Err(Error::BuilderState);
        };

        Ok(RegistrationInitiator::new(
            responder_ecdh_pk,
            initiator_ecdh_pk,
            initiator_ecdh_sk,
            self.responder_pq_pk,
            self.context,
            self.inner_aad,
            self.outer_aad,
            self.rng,
        )?)
    }

    pub fn build_responder(self) -> Result<Responder<'a, Rng>, Error> {
        let Some(longterm_ecdh_pk) = self.responder_ecdh_pk else {
            return Err(Error::BuilderState);
        };
        let Some(longterm_ecdh_sk) = self.responder_ecdh_sk else {
            return Err(Error::BuilderState);
        };
        let Some(longterm_pq_pk) = self.responder_pq_pk else {
            return Err(Error::BuilderState);
        };
        let Some(longterm_pq_sk) = self.responder_pq_sk else {
            return Err(Error::BuilderState);
        };

        Ok(Responder::new(
            longterm_ecdh_pk,
            longterm_ecdh_sk,
            longterm_pq_pk,
            longterm_pq_sk,
            self.context,
            self.outer_aad,
            self.rng,
        ))
    }
}
