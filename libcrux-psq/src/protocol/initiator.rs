use super::{
    ecdh::{PrivateKey, PublicKey},
    keys::{
        derive_k0, derive_k1, derive_k2_query_initiator, derive_k2_registration_initiator, AEADKey,
    },
    responder::ResponderOuterPayload,
    session::SessionState,
    signature::{Signature, VerificationKey},
    transcript::{tx1, tx2, Transcript},
    Message, ProtocolMode,
};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

/// The protocol initiator's initial state
pub(crate) enum InitiatorPre {
    Query {
        responder_longterm_ecdh_pk: PublicKey,
        initiator_ephemeral_ecdh_pk: PublicKey,
        initiator_ephemeral_ecdh_sk: PrivateKey,
        tx0: Transcript,
    },
    Registration {
        responder_longterm_ecdh_pk: PublicKey,
        initiator_ephemeral_ecdh_pk: PublicKey,
        initiator_ephemeral_ecdh_sk: PrivateKey,
        initiator_longterm_ecdh_sk: PrivateKey,
        initiator_longterm_ecdh_pk: PublicKey,
        responder_pq_pk: Option<libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        tx1: Transcript,
        k1: AEADKey,
    },
}

pub(crate) struct InitiatorDone {
    session_state: SessionState,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub(crate) enum InitiatorOuterPayload {
    Query,
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        pq_encaps: Option<libcrux_ml_kem::mlkem768::MlKem768Ciphertext>,
        ciphertext: Vec<u8>,
        aad: Vec<u8>,
    },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
// XXX: Determine what should go in here
pub(crate) struct InitiatorInnerPayload {}

impl InitiatorPre {
    pub(crate) fn first_message(
        mode: ProtocolMode,
        responder_longterm_ecdh_pk: &PublicKey,
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = PublicKey::from(&initiator_ephemeral_ecdh_sk);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let (payload0, initator_pre) = match mode {
            ProtocolMode::Registration {
                responder_pq_pk,
                initiator_longterm_ecdh_pk,
                initiator_longterm_ecdh_sk,
            } => {
                let pq_encaps_pair = responder_pq_pk.map(|pk| {
                    let mut randomness = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
                    rng.fill_bytes(&mut randomness);
                    libcrux_ml_kem::mlkem768::encapsulate(&pk, randomness)
                });

                let (pq_encaps, pq_shared_secret) =
                    if let Some((pq_encaps, pq_shared_secret)) = pq_encaps_pair {
                        (Some(pq_encaps), Some(pq_shared_secret))
                    } else {
                        (None, None)
                    };

                let tx1 = tx1(
                    &tx0,
                    &initiator_longterm_ecdh_pk,
                    &responder_pq_pk,
                    &pq_encaps,
                );
                let k1 = derive_k1(
                    &k0,
                    &initiator_longterm_ecdh_sk,
                    responder_longterm_ecdh_pk,
                    &pq_shared_secret,
                    &tx0,
                );
                let aad = vec![];

                let ciphertext = k1.serialize_encrypt(&InitiatorInnerPayload {}, &aad);

                (
                    InitiatorOuterPayload::Registration {
                        initiator_longterm_ecdh_pk,
                        pq_encaps,
                        aad,
                        ciphertext,
                    },
                    Self::Registration {
                        responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
                        initiator_ephemeral_ecdh_pk,
                        initiator_ephemeral_ecdh_sk,
                        initiator_longterm_ecdh_sk,
                        initiator_longterm_ecdh_pk,
                        responder_pq_pk: responder_pq_pk.clone(),
                        tx1,
                        k1,
                    },
                )
            }
            ProtocolMode::Query => (
                InitiatorOuterPayload::Query,
                Self::Query {
                    responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
                    initiator_ephemeral_ecdh_pk,
                    initiator_ephemeral_ecdh_sk,
                    tx0,
                },
            ),
        };

        let aad = vec![];
        let ciphertext = k0.serialize_encrypt(&payload0, &aad);

        (
            initator_pre,
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext,
                aad,
            },
        )
    }

    pub(crate) fn complete_registration(self, responder_msg: &Message) -> InitiatorDone {
        let tx2 = tx2(&self.tx0, &responder_msg.ephemeral_ecdh_pk);
        match self {
            Self::Query {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_pk,
                initiator_ephemeral_ecdh_sk,
                tx0,
            } => {
                let k2 = derive_k2_query_initiator(
                    &responder_msg.ephemeral_ecdh_pk,
                    &initiator_ephemeral_ecdh_sk,
                    &responder_longterm_ecdh_pk,
                    &tx2,
                );

                let payload2 = k2.decrypt_deserialize(&responder_msg.ciphertext);

                if matches!(payload2, ResponderOuterPayload::Query) {
                    InitiatorDone {
                        session_state: SessionState::query_mode(
                            &responder_longterm_ecdh_pk,
                            &k2,
                            &tx2,
                        ),
                    }
                } else {
                    panic!("wrong responder message")
                }
            }

            Self::Registration {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_pk,
                initiator_ephemeral_ecdh_sk,
                initiator_longterm_ecdh_sk,
                initiator_longterm_ecdh_pk,
                tx1,
                k1,
                responder_pq_pk,
            } => {
                let k2 = derive_k2_registration_initiator(
                    &k1,
                    &tx2,
                    &initiator_longterm_ecdh_sk,
                    &initiator_ephemeral_ecdh_sk,
                    &responder_msg.ephemeral_ecdh_pk,
                );

                let payload2 = k2.decrypt_deserialize(&responder_msg.ciphertext);
                if matches!(payload2, ResponderOuterPayload::Registration) {
                    InitiatorDone {
                        session_state: SessionState::registration_mode(
                            &responder_longterm_ecdh_pk,
                            &initiator_longterm_ecdh_pk,
                            &responder_pq_pk,
                            &k2,
                            &tx2,
                        ),
                    }
                } else {
                    panic!("wrong responder message")
                }
            }
        }
    }
}
