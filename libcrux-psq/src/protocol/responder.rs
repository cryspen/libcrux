use std::io::Write;
use std::{
    collections::HashMap,
    time::{Duration, SystemTime},
};

use libcrux_kem::MlKem768Ciphertext;
use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768PrivateKey, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{
    DeserializeBytes, SerializeBytes, TlsDeserializeBytes, TlsSerializeBytes, TlsSize,
};

use crate::protocol::api::{Error, HandshakeState};

use super::{
    ecdh::{KEMKeyPair, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message, ResponderAppContext, TTL_THRESHOLD,
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
    registration_msg: Message,
    initiator_eph_pk: PublicKey,
    tx1: Transcript,
    k1: AEADKey,
}

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize, Default)]
pub struct ResponderQueryPayload(pub Vec<u8>);

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload(pub Vec<u8>);

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
        responder_keys: &KEMKeyPair,
        responder_context: &ResponderAppContext<'context>,
        initiator_eph_pk: &PublicKey,
        tx0: &Transcript,
        k0: &AEADKey,
        response: &ResponderQueryPayload,
        rng: &mut impl CryptoRng,
    ) -> Result<Message, Error> {
        let responder_eph_keys = KEMKeyPair::new(rng);

        let tx2 = tx2(tx0, &responder_eph_keys.pk);
        let k2 = derive_k2_query_responder(
            k0,
            initiator_eph_pk,
            &responder_eph_keys.sk,
            &responder_keys.sk,
            &tx2,
        )?;

        let mut ciphertext = vec![0u8; response.tls_serialized_len() + 16];

        k2.serialize_encrypt(response, responder_context.aad, &mut ciphertext)?;

        Ok(Message {
            pk: responder_eph_keys.pk,
            ciphertext,
            aad: responder_context.aad.map(|aad| aad.to_vec()),
            pq_encaps: None,
        })
    }

    pub fn respond_registration(
        responder_longterm_ecdh_pk: &'a PublicKey,
        responder_pq_pk: &'a MlKem768PublicKey,
        state: &'a ResponderRegistrationState,
        response: &'a ResponderRegistrationPayload,
        rng: &'a mut impl CryptoRng,
    ) -> Result<(SessionState<'a>, Message), Error> {
        let responder_eph_keys = KEMKeyPair::new(rng);

        let tx2 = tx2(&state.tx1, &responder_eph_keys.pk);

        let k2 = derive_k2_registration_responder(
            &state.k1,
            &tx2,
            &state.registration_msg.pk,
            &state.initiator_eph_pk,
            &responder_eph_keys.sk,
        )?;

        let mut ciphertext = vec![0u8; response.tls_serialized_len() + 16];

        k2.serialize_encrypt(&response, responder_context.aad, &mut ciphertext)?;

        let responder_pq_pk = state
            .registration_msg
            .pq_encaps
            .is_some()
            .then_some(responder_pq_keys.public_key());

        let session_state = SessionState::new(
            false,
            response,
            &responder_keys.pk,
            &state.registration_msg.pk,
            responder_pq_pk,
            &k2,
            &tx2,
        );
        Ok((
            session_state,
            Message {
                pk: responder_eph_keys.pk,
                ciphertext,
                aad: responder_context.aad.map(|aad| aad.to_vec()),
                pq_encaps: None,
            },
        ))
    }

    pub fn decrypt_inner(
        responder_keys: &KEMKeyPair,
        responder_pq_keys: &MlKem768KeyPair,
        tx0: &Transcript,
        k0: &AEADKey,
        registration_msg: Message,
        initiator_eph_pk: &PublicKey,
    ) -> Result<(InitiatorInnerPayload, ResponderRegistrationState), Error> {
        let pq_shared_secret = registration_msg
            .pq_encaps
            .as_ref()
            .map(|enc| decapsulate(responder_pq_keys.private_key(), enc));
        let responder_pq_pk_opt = registration_msg
            .pq_encaps
            .as_ref()
            .map(|_| responder_pq_keys.public_key());

        let tx1 = tx1(
            tx0,
            &registration_msg.pk,
            responder_pq_pk_opt,
            registration_msg.pq_encaps.as_ref(),
        );

        let k1 = derive_k1(
            k0,
            &responder_keys.sk,
            &registration_msg.pk,
            &pq_shared_secret,
            &tx1,
        )?;

        let inner_payload: InitiatorInnerPayload =
            k1.decrypt_deserialize(&registration_msg.ciphertext, registration_msg.aad.as_ref());

        Ok((
            inner_payload,
            ResponderRegistrationState {
                tx1,
                k1,
                registration_msg,
                initiator_eph_pk: initiator_eph_pk.clone(),
            },
        ))
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
        eph_keys: &mut HashMap<PublicKey, Duration>,
        responder_keys: &KEMKeyPair,
        responder_context: &ResponderAppContext<'context>,
        initiator_msg: Message,
    ) -> Result<(InitiatorOuterPayload, Transcript, AEADKey, PublicKey), Error> {
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| Error::OsError)?;
        if let Some(timestamp) = eph_keys.get(&initiator_msg.pk) {
            if now - *timestamp < TTL_THRESHOLD {
                return Err(Error::TimestampElapsed);
            }
        } else {
            eph_keys.insert(initiator_msg.pk.clone(), now);
        }

        let (tx0, k0) = derive_k0(
            &initiator_msg.pk,
            responder_keys,
            responder_context.context,
            true,
        )?;

        let received_payload =
            k0.decrypt_deserialize(&initiator_msg.ciphertext, initiator_msg.aad.as_ref());

        Ok((received_payload, tx0, k0, initiator_msg.pk))
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
