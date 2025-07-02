use libcrux_chacha20poly1305::decrypt;
use libcrux_ml_kem::mlkem768::MlKem768PrivateKey;
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    ecdh::{PrivateKey, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder},
    session::SessionState,
    signature::VerificationKey,
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
    Registration, // {
                  //         responder_ephemeral_ecdh_pk: PublicKey,
                  //         ciphertext: Vec<u8>,
                  //         aad: Vec<u8>,
                  //     },
}

impl Responder {
    // This doesn't check if the Initiator key is fresh, which should be done outside.
    fn respond(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_longterm_ecdh_pk: &PublicKey,
        responder_pq_key_pair: libcrux_ml_kem::mlkem768::MlKem768KeyPair,
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

        let received_payload = k0.decrypt_deserialize(initiator_msg);

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
                initiator_longterm_ecdh_pk: initiator_vk,
                pq_encaps: kem_ciphertext,
                ciphertext,
                aad,
            } => {
                let (responder_pq_pk, pq_shared_secret) = if let Some(pq_encaps) = kem_ciphertext {
                    let responder_pq_pk = responder_pq_key_pair.public_key().clone();
                    let pq_shared_secret = libcrux_ml_kem::mlkem768::decapsulate(
                        responder_pq_key_pair.private_key(),
                        &pq_encaps,
                    );
                    (Some(responder_pq_pk), Some(pq_shared_secret))
                } else {
                    (None, None)
                };
                let tx1 = tx1(&tx0, &initiator_vk, &responder_pq_pk, &kem_ciphertext);

                let k1 = derive_k1(
                    &k0,
                    &responder_longterm_ecdh_sk,
                    &initiator_vk,
                    &pq_shared_secret,
                    &tx0,
                );

                let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(ciphertext);

                let tx2 = tx2(&tx1, &ephemeral_ecdh_pk);
                let k2 = derive_k2_registration_responder(
                    &k1,
                    &tx2,
                    &initiator_vk,
                    &initiator_msg.ephemeral_ecdh_pk,
                    &ephemeral_ecdh_sk,
                );

                let aad = vec![];
                let ciphertext = k2.serialize_encrypt(&ResponderOuterPayload::Registration, &aad);

                (aad, ciphertext, SessionState::registration_mode())
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
