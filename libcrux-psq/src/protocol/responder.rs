use std::io::Write;

use libcrux_kem::MlKem768Ciphertext;
use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768PrivateKey, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{
    DeserializeBytes, SerializeBytes, TlsDeserializeBytes, TlsSerializeBytes, TlsSize,
};

use crate::protocol::api::{Error, HandshakeState};

use super::{
    ecdh::{PrivateKey, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message,
};

pub(crate) struct ResponderState<'a, T: CryptoRng> {
    pub(crate) longterm_ecdh_pk: &'a PublicKey,
    pub(crate) longterm_ecdh_sk: &'a PrivateKey,
    pub(crate) context: &'a [u8],
    pub(crate) rng: &'a mut T,
}

pub struct Responder<'a, T: CryptoRng> {
    pub(crate) setup: ResponderState<'a, T>,
    pub(crate) outer: InitiatorOuterPayload,
    pub(crate) tx: Transcript,
    pub(crate) k0: AEADKey,
    pub(crate) aad: Vec<u8>,
    pub(crate) initiator_ephemeral_ecdh_pk: Option<PublicKey>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub enum ResponderPayload {
    Query,
    Registration,
}

pub struct ResponderRegistrationState {
    tx1: Transcript,
    k1: AEADKey,
    pq: bool,
}

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize, Default)]
pub struct ResponderQueryPayload(pub Vec<u8>);

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload;

impl<'a, Rng: CryptoRng> Responder<'a, Rng> {
    pub fn new(
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        context: &'a [u8],
        rng: &'a mut Rng,
    ) -> Self {
        Self {
            setup: ResponderState {
                longterm_ecdh_pk,
                longterm_ecdh_sk,
                context,
                rng,
            },
            outer: InitiatorOuterPayload::Reserved,
            tx: Transcript::default(),
            k0: AEADKey::default(),
            aad: vec![],
            initiator_ephemeral_ecdh_pk: None,
        }
    }

    fn respond_query_self(&mut self, payload: &[u8]) -> Message {
        // XXX: Copied from respond_query

        let responder_ephemeral_ecdh_sk = PrivateKey::new(self.setup.rng);
        let responder_ephemeral_ecdh_pk = PublicKey::from(&responder_ephemeral_ecdh_sk);

        let tx2 = tx2(&self.tx, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_query_responder(
            &self.k0,
            self.initiator_ephemeral_ecdh_pk.as_ref().unwrap(),
            &responder_ephemeral_ecdh_sk,
            self.setup.longterm_ecdh_sk,
            &tx2,
        );

        // XXX: Don't copy `payload`
        let ciphertext = k2.serialize_encrypt(&ResponderQueryPayload(payload.to_vec()), &self.aad);

        Message {
            ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
            ciphertext,
            aad: self.aad.clone(),
        }
    }

    pub fn respond_query(
        responder_longterm_ecdh_sk: &PrivateKey,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_msg: &Message,
        response: &ResponderQueryPayload,
        aad: &[u8],
        rng: &mut impl CryptoRng,
    ) -> Message {
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ..
        } = initiator_msg;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let responder_ephemeral_ecdh_pk = PublicKey::from(&responder_ephemeral_ecdh_sk);

        let tx2 = tx2(tx0, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_query_responder(
            k0,
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
            responder_longterm_ecdh_sk,
            &tx2,
        );

        let ciphertext = k2.serialize_encrypt(response, &aad);

        Message {
            ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
            ciphertext,
            aad: aad.to_vec(),
        }
    }

    pub fn respond_registration(
        responder_longterm_ecdh_pk: &'a PublicKey,
        responder_pq_pk: &'a MlKem768PublicKey,
        state: &'a ResponderRegistrationState,
        initiator_longterm_ecdh_pk: &'a PublicKey,
        initiator_msg: &'a Message,
        response: &'a ResponderRegistrationPayload,
        aad: &'a [u8],
        rng: &'a mut impl CryptoRng,
    ) -> (SessionState<'a>, Message) {
        let ResponderRegistrationState { tx1, k1, pq } = state;
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ..
        } = initiator_msg;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let responder_ephemeral_ecdh_pk = PublicKey::from(&responder_ephemeral_ecdh_sk);
        let tx2 = tx2(&tx1, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_responder(
            &k1,
            &tx2,
            &Box::new(initiator_longterm_ecdh_pk),
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
        );

        let ciphertext = k2.serialize_encrypt(&ResponderRegistrationPayload {}, aad);

        let responder_pq_pk = if *pq { Some(responder_pq_pk) } else { None };
        let session_state = SessionState::new(
            false,
            response,
            responder_longterm_ecdh_pk,
            &initiator_longterm_ecdh_pk,
            responder_pq_pk,
            &k2,
            &tx2,
        );
        (
            session_state,
            Message {
                ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
                ciphertext,
                aad: aad.to_vec(),
            },
        )
    }

    pub fn decrypt_inner(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_pq_sk: &MlKem768PrivateKey,
        responder_pq_pk: &MlKem768PublicKey,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_longterm_ecdh_pk: &PublicKey,
        pq_encaps: Option<&libcrux_ml_kem::mlkem768::MlKem768Ciphertext>,
        ciphertext: &[u8],
        aad: &[u8],
    ) -> (InitiatorInnerPayload, ResponderRegistrationState) {
        let pq_shared_secret = pq_encaps.map(|enc| decapsulate(responder_pq_sk, &enc));
        let responder_pq_pk_opt = if pq_encaps.as_ref().is_some() {
            Some(responder_pq_pk)
        } else {
            None
        };

        let tx1 = tx1(
            tx0,
            initiator_longterm_ecdh_pk,
            responder_pq_pk_opt,
            pq_encaps,
        );

        let k1 = derive_k1(
            k0,
            &responder_longterm_ecdh_sk,
            initiator_longterm_ecdh_pk,
            &pq_shared_secret,
            &tx1,
        );

        let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(&ciphertext, &aad);

        (
            inner_payload,
            ResponderRegistrationState {
                tx1,
                k1,
                pq: pq_encaps.is_some(),
            },
        )
    }

    fn decrypt_outer_msg(&mut self, initiator_msg: Message) {
        // XXX: duplicated from `decrypt_outer`

        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ciphertext,
            aad,
        } = initiator_msg;
        let (tx0, k0) = derive_k0(
            self.setup.longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            self.setup.longterm_ecdh_sk,
            self.setup.context,
            true,
        );

        self.outer = k0.decrypt_deserialize(&ciphertext, &aad);
        self.k0 = k0;
        self.tx = tx0;
        self.aad = aad;
        self.initiator_ephemeral_ecdh_pk = Some(initiator_ephemeral_ecdh_pk);
    }

    pub fn decrypt_outer(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_longterm_ecdh_pk: &PublicKey,
        initiator_msg: &Message,
        ctx: &[u8],
    ) -> (InitiatorOuterPayload, Transcript, AEADKey) {
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ciphertext,
            aad,
        } = initiator_msg;
        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            responder_longterm_ecdh_sk,
            ctx,
            true,
        );

        let received_payload = k0.decrypt_deserialize(&ciphertext, &aad);

        (received_payload, tx0, k0)
    }
}

impl<'a, Rng: CryptoRng> HandshakeState for Responder<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let msg = self.respond_query_self(payload);
        let msg_out = msg.tls_serialize().map_err(|e| Error::Serialize(e))?;
        out[0..msg_out.len()].copy_from_slice(&msg_out);
        Ok(msg_out.len())
    }

    fn read_message(&mut self, message: &[u8], _payload: &mut [u8]) -> Result<usize, Error> {
        let (msg, _remainder) =
            Message::tls_deserialize_bytes(message).map_err(|e| Error::Deserialize(e))?;

        self.decrypt_outer_msg(msg);

        // XXX: not using the bytes version we wouldn't need to do this math
        Ok(message.len() - _remainder.len())
    }
}
