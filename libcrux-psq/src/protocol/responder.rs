use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768PrivateKey, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

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

pub(crate) struct Responder<'keys> {
    pub(crate) session_state: SessionState<'keys>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub(crate) enum ResponderPayload {
    Query,
    Registration,
}

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderQueryPayload;

// XXX: Determine what should be the contents here.
#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload;

impl<'keys> Responder<'keys> {
    pub(crate) fn respond_query(
        responder_longterm_ecdh_sk: &'keys PrivateKey,
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

    pub(crate) fn respond_registration(
        responder_longterm_ecdh_sk: &'keys PrivateKey,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        responder_pq_sk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PrivateKey>,
        responder_pq_pk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        tx1: &Transcript,
        k1: &AEADKey,
        initiator_longterm_ecdh_pk: &'keys PublicKey,
        initiator_msg: &Message,
        response: &ResponderRegistrationPayload,
        aad: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (SessionState<'keys>, Message) {
        let Message {
            ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
            ..
        } = initiator_msg;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let responder_ephemeral_ecdh_pk = PublicKey::from(&responder_ephemeral_ecdh_sk);
        let tx2 = tx2(tx1, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_responder(
            k1,
            &tx2,
            &Box::new(initiator_longterm_ecdh_pk),
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
        );

        let ciphertext = k2.serialize_encrypt(&ResponderPayload::Registration, aad);

        let session_state = SessionState::new(
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

    pub(crate) fn decrypt_inner(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_longterm_ecdh_pk: &PublicKey,
        responder_pq_sk: &libcrux_ml_kem::mlkem768::MlKem768PrivateKey,
        responder_pq_pk: &libcrux_ml_kem::mlkem768::MlKem768PublicKey,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_longterm_ecdh_pk: &PublicKey,
        pq_encaps: Option<&libcrux_ml_kem::mlkem768::MlKem768Ciphertext>,
        ciphertext: &[u8],
        aad: &[u8],
    ) -> (InitiatorInnerPayload, Transcript, AEADKey) {
        let pq_shared_secret =
            pq_encaps.map(|enc| libcrux_ml_kem::mlkem768::decapsulate(responder_pq_sk, &enc));
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
            &tx0,
        );

        let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(&ciphertext, &aad);

        (inner_payload, tx1, k1)
    }

    pub(crate) fn decrypt_outer(
        responder_longterm_ecdh_sk: &'keys PrivateKey,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        responder_pq_pk: &'keys MlKem768PublicKey,
        responder_pq_sk: &'keys MlKem768PrivateKey,
        initiator_msg: &Message,
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (InitiatorOuterPayload, Transcript, AEADKey) {
        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_msg.ephemeral_ecdh_pk,
            responder_longterm_ecdh_sk,
            ctx,
            true,
        );

        let received_payload =
            k0.decrypt_deserialize(&initiator_msg.ciphertext, &initiator_msg.aad);

        (received_payload, tx0, k0)
    }
}
