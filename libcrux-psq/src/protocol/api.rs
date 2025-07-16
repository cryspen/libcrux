use rand::CryptoRng;

use crate::protocol::{
    ecdh::{PrivateKey, PublicKey},
    initiator::{InitiatorOuterPayload, QueryInitiator},
    keys::AEADKey,
    responder::{Responder, ResponderState},
    transcript::Transcript,
};

#[derive(Debug)]
pub enum Error {
    BuilderState,
    Serialize(tls_codec::Error),
    Deserialize(tls_codec::Error),
    CryptoError,
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
    aad: &'a [u8],
    responder_ecdh_pk: Option<&'a PublicKey>,
    responder_ecdh_sk: Option<&'a PrivateKey>,
}

impl<'a, Rng: CryptoRng> Builder<'a, Rng> {
    pub fn new(rng: &'a mut Rng) -> Self {
        Self {
            rng,
            context: &[],
            aad: &[],
            responder_ecdh_pk: None,
            responder_ecdh_sk: None,
        }
    }

    // properties
    pub fn context(mut self, context: &'a [u8]) -> Self {
        self.context = context;
        self
    }

    pub fn aad(mut self, aad: &'a [u8]) -> Self {
        self.aad = aad;
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

    // builders
    pub fn build_query_initiator(self) -> Result<QueryInitiator<'a>, Error> {
        let Some(responder_ecdh_pk) = self.responder_ecdh_pk else {
            return Err(Error::BuilderState);
        };

        Ok(QueryInitiator::new(
            responder_ecdh_pk,
            self.context,
            self.aad,
            self.rng,
        )?)
    }

    pub fn build_query_responder(self) -> Result<Responder<'a, Rng>, Error> {
        let Some(longterm_ecdh_pk) = self.responder_ecdh_pk else {
            return Err(Error::BuilderState);
        };
        let Some(longterm_ecdh_sk) = self.responder_ecdh_sk else {
            return Err(Error::BuilderState);
        };

        Ok(Responder {
            setup: ResponderState {
                longterm_ecdh_pk,
                longterm_ecdh_sk,
                context: self.context,
                rng: self.rng,
            },
            outer: InitiatorOuterPayload::Reserved,
            tx0: Transcript::default(),
            k0: AEADKey::default(),
            aad: self.aad.to_vec(),
            initiator_ephemeral_ecdh_pk: None,
        })
    }
}
