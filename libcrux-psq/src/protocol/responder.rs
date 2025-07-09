use libcrux_ml_kem::mlkem768::{
    decapsulate, MlKem768Ciphertext, MlKem768KeyPair, MlKem768PublicKey,
};
use rand::CryptoRng;
use tls_codec::{Size, TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    ecdh::{KEMKeyPair, PrivateKey, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message,
};

pub struct Responder {}

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
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderQueryPayload;

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload;

impl Responder {
    pub fn respond_query(
        responder_longterm_ecdh_sk: &PrivateKey,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_msg: &Message,
        response: &ResponderQueryPayload,
        aad: &[u8],
        rng: &mut impl CryptoRng,
    ) -> Result<Message, crate::Error> {
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ..
        } = initiator_msg;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let responder_ephemeral_ecdh_pk = responder_ephemeral_ecdh_sk.to_public();

        let tx2 = tx2(tx0, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_query_responder(
            k0,
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
            responder_longterm_ecdh_sk,
            &tx2,
        );

        let mut ciphertext = vec![0u8; response.tls_serialized_len() + 16];

        k2.serialize_encrypt(response, &aad, &mut ciphertext)?;

        Ok(Message {
            ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
            ciphertext,
            aad: aad.to_vec(),
        })
    }

    pub fn respond_registration<'a>(
        responder_longterm_ecdh_pk: &'a PublicKey,
        responder_pq_pk: &'a MlKem768PublicKey,
        state: &'a ResponderRegistrationState,
        initiator_longterm_ecdh_pk: &'a PublicKey,
        initiator_msg: &'a Message,
        response: &'a ResponderRegistrationPayload,
        aad: &'a [u8],
        rng: &'a mut impl CryptoRng,
    ) -> Result<(SessionState<'a>, Message), crate::Error> {
        let ResponderRegistrationState { tx1, k1, pq } = state;
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ..
        } = initiator_msg;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let responder_ephemeral_ecdh_pk = responder_ephemeral_ecdh_sk.to_public();

        let tx2 = tx2(&tx1, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_responder(
            &k1,
            &tx2,
            &Box::new(initiator_longterm_ecdh_pk),
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
        );

        let responder_payload = ResponderRegistrationPayload {};
        let mut ciphertext = vec![0u8; responder_payload.tls_serialized_len() + 16];

        k2.serialize_encrypt(&responder_payload, aad, &mut ciphertext)?;

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
        Ok((
            session_state,
            Message {
                ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
                ciphertext,
                aad: aad.to_vec(),
            },
        ))
    }

    pub fn decrypt_inner(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_pq_keypair: &MlKem768KeyPair,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_longterm_ecdh_pk: &PublicKey,
        pq_encaps: Option<&MlKem768Ciphertext>,
        ciphertext: &[u8],
        aad: &[u8],
    ) -> (InitiatorInnerPayload, ResponderRegistrationState) {
        let pq_shared_secret =
            pq_encaps.map(|enc| decapsulate(&responder_pq_keypair.private_key(), &enc));
        let responder_pq_pk_opt = if pq_encaps.as_ref().is_some() {
            Some(responder_pq_keypair.public_key())
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

    pub fn decrypt_outer(
        responder_longterm_ecdh_keys: &KEMKeyPair,
        initiator_msg: &Message,
        ctx: &[u8],
    ) -> (InitiatorOuterPayload, Transcript, AEADKey) {
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ciphertext,
            aad,
        } = initiator_msg;
        let (tx0, k0) = derive_k0(
            &responder_longterm_ecdh_keys.pk,
            &initiator_ephemeral_ecdh_pk,
            &responder_longterm_ecdh_keys.sk,
            ctx,
            true,
        );

        let received_payload = k0.decrypt_deserialize(&ciphertext, &aad);

        (received_payload, tx0, k0)
    }
}
