use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768PrivateKey, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    ecdh::{PrivateKey, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder},
    session::SessionState,
    transcript::{tx1, tx2},
    Message,
};

pub(crate) struct Responder {
    pub(crate) session_state: SessionState,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub(crate) enum ResponderOuterPayload {
    Query,
    Registration,
}

impl Responder {
    // This doesn't check if the Initiator key is fresh, which should be done outside.
    fn respond(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_longterm_ecdh_pk: &PublicKey,
        responder_pq_pk: &MlKem768PublicKey,
        responder_pq_sk: &MlKem768PrivateKey,
        initiator_msg: &Message,
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_msg.ephemeral_ecdh_pk,
            responder_longterm_ecdh_sk,
            ctx,
            true,
        );

        let received_payload =
            k0.decrypt_deserialize(&initiator_msg.ciphertext, &initiator_msg.aad);

        let ephemeral_ecdh_sk = PrivateKey::new(rng);
        let ephemeral_ecdh_pk = PublicKey::from(&ephemeral_ecdh_sk);

        let (aad, ciphertext, session_state) = match received_payload {
            InitiatorOuterPayload::Query => {
                let tx2 = tx2(&tx0, &ephemeral_ecdh_pk);
                let key_2 = derive_k2_query_responder(
                    &initiator_msg.ephemeral_ecdh_pk,
                    &ephemeral_ecdh_sk,
                    responder_longterm_ecdh_sk,
                    &tx2,
                );

                let aad = vec![];
                let ciphertext = key_2.serialize_encrypt(&ResponderOuterPayload::Query, &aad);

                (
                    aad,
                    ciphertext,
                    SessionState::query_mode(responder_longterm_ecdh_pk, &key_2, &tx2),
                )
            }
            InitiatorOuterPayload::Registration {
                initiator_longterm_ecdh_pk,
                pq_encaps,
                ciphertext,
                aad,
            } => {
                let pq_shared_secret = pq_encaps.map(|enc| decapsulate(responder_pq_sk, &enc));
                let responder_pq_pk_opt = if pq_encaps.as_ref().is_some() {
                    Some(responder_pq_pk)
                } else {
                    None
                };
                let tx1 = tx1(
                    &tx0,
                    &initiator_longterm_ecdh_pk,
                    responder_pq_pk_opt,
                    pq_encaps.as_ref(),
                );

                let k1 = derive_k1(
                    &k0,
                    &responder_longterm_ecdh_sk,
                    &initiator_longterm_ecdh_pk,
                    &pq_shared_secret,
                    &tx0,
                );

                let inner_payload: InitiatorInnerPayload =
                    k1.decrypt_deserialize(&ciphertext, &aad);

                let tx2 = tx2(&tx1, &ephemeral_ecdh_pk);
                let k2 = derive_k2_registration_responder(
                    &k1,
                    &tx2,
                    &initiator_longterm_ecdh_pk,
                    &initiator_msg.ephemeral_ecdh_pk,
                    &ephemeral_ecdh_sk,
                );

                let aad = vec![];
                let ciphertext = k2.serialize_encrypt(&ResponderOuterPayload::Registration, &aad);

                (
                    aad,
                    ciphertext,
                    SessionState::registration_mode(
                        responder_longterm_ecdh_pk,
                        &initiator_longterm_ecdh_pk,
                        responder_pq_pk_opt,
                        &k2,
                        &tx2,
                    ),
                )
            }
        };

        (
            Self { session_state },
            Message {
                ephemeral_ecdh_pk,
                ciphertext,
                aad,
            },
        )
    }
}
