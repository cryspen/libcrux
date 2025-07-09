use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768KeyPair};
use rand::CryptoRng;
use tls_codec::{Size, TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

use crate::Error;

use super::{
    ecdh::{KEMKeyPair, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message, ResponderAppContext,
};

pub struct Responder {}

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
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderQueryPayload;

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload;

impl<'context> Responder {
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

    pub fn respond_registration<'a>(
        responder_keys: &'a KEMKeyPair,
        responder_pq_keys: &'a MlKem768KeyPair,
        responder_context: &'a ResponderAppContext<'context>,
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

        let responder_payload = ResponderRegistrationPayload {};
        let mut ciphertext = vec![0u8; responder_payload.tls_serialized_len() + 16];

        k2.serialize_encrypt(&responder_payload, responder_context.aad, &mut ciphertext)?;

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

    pub fn decrypt_outer(
        responder_keys: &KEMKeyPair,
        responder_context: &ResponderAppContext<'context>,
        initiator_msg: Message,
    ) -> Result<(InitiatorOuterPayload, Transcript, AEADKey, PublicKey), Error> {
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
