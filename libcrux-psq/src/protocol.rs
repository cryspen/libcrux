//! The PSQ registration protocol
#![allow(missing_docs)]

use ecdh::{PrivateKey, PublicKey};
use keys::{
    derive_k0, derive_k2_query_initiator, derive_k2_query_responder, derive_session_key, AEADKey,
};
use libcrux_chacha20poly1305::{decrypt, NONCE_LEN};
use rand::CryptoRng;
use session::SessionState;
use tls_codec::{
    DeserializeBytes, SerializeBytes, TlsDeserializeBytes, TlsSerializeBytes, TlsSize,
};
use transcript::Transcript;

mod ecdh;
mod keys;
mod session;
mod transcript;

/// The protocol initiator's initial state
pub(crate) struct InitiatorPre {
    responder_longterm_ecdh_pk: PublicKey,
    initiator_ephemeral_ecdh_pk: PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    tx0: Transcript,
    tx1: Option<Transcript>,
}

pub(crate) struct InitiatorDone {
    initiator_ecdh_sk: PrivateKey,
    session_state: SessionState,
}

pub(crate) struct Responder {
    pub(crate) responder_ecdh_sk: PrivateKey,
    pub(crate) responder_pq_sk: Option<Vec<u8>>,
    pub(crate) session_state: SessionState,
}

#[derive(Debug, PartialEq)]
pub enum ProtocolMode {
    Registration,
    Query,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub enum MessageOriginator {
    Initiator,
    Responder,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub(crate) enum OuterPayload {
    Query(MessageOriginator),
    Registration { originator: MessageOriginator },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub(crate) struct Message {
    ephemeral_ecdh_pk: PublicKey,
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

impl InitiatorPre {
    pub(crate) fn first_message(
        mode: ProtocolMode,
        responder_longterm_ecdh_pk: &PublicKey,
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let initiator_ephemeral_ecdh_sk = ecdh::PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = ecdh::PublicKey::from(&initiator_ephemeral_ecdh_sk);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let payload0 = match mode {
            ProtocolMode::Registration => todo!(),
            ProtocolMode::Query => OuterPayload::Query(MessageOriginator::Initiator),
        };

        let aad = vec![];
        let ciphertext = serialize_encrypt_outer_payload(&k0, payload0, &aad);

        (
            Self {
                tx0,
                tx1: None,
                responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
                initiator_ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk.clone(),
                initiator_ephemeral_ecdh_sk,
            },
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext,
                aad,
            },
        )
    }

    pub(crate) fn complete_registration(self, responder_msg: &Message) -> InitiatorDone {
        let tx2 = transcript::tx2(&self.tx0, &responder_msg.ephemeral_ecdh_pk);

        let k2 = derive_k2_query_initiator(
            &responder_msg.ephemeral_ecdh_pk,
            &self.initiator_ephemeral_ecdh_sk,
            &self.responder_longterm_ecdh_pk,
            &tx2,
        );

        let payload2 = decrypt_deserialize_payload(&k2, responder_msg);

        match payload2 {
            OuterPayload::Query(MessageOriginator::Responder) => InitiatorDone {
                initiator_ecdh_sk: self.initiator_ephemeral_ecdh_sk,
                session_state: SessionState::query_mode(
                    &self.responder_longterm_ecdh_pk,
                    &k2,
                    &tx2,
                ),
            },
            OuterPayload::Registration {
                originator: MessageOriginator::Responder,
            } => todo!(),
            _ => panic!("Only accept messages from the Responder"),
        }
    }
}

fn serialize_encrypt_outer_payload(key: &AEADKey, payload: OuterPayload, aad: &[u8]) -> Vec<u8> {
    let payload_serialized = payload.tls_serialize().unwrap();
    let mut ciphertext = vec![0u8; payload_serialized.len() + 16];
    let _ = libcrux_chacha20poly1305::encrypt(
        key.as_ref(),
        &payload_serialized,
        &mut ciphertext,
        aad,
        &[0; NONCE_LEN],
    )
    .expect("Encryption Error");

    ciphertext
}

impl Responder {
    // This doesn't check if the Initiator key is fresh, which should be done outside.
    fn respond(
        responder_longterm_ecdh_sk: &PrivateKey,
        responder_longterm_ecdh_pk: &PublicKey,
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

        let received_payload = decrypt_deserialize_payload(&k0, initiator_msg);

        let ephemeral_ecdh_sk = PrivateKey::new(rng);
        let ephemeral_ecdh_pk = PublicKey::from(&ephemeral_ecdh_sk);

        match received_payload {
            OuterPayload::Query(MessageOriginator::Initiator) => {
                let tx2 = transcript::tx2(&tx0, &ephemeral_ecdh_pk);
                let key_2 = derive_k2_query_responder(
                    &initiator_msg.ephemeral_ecdh_pk,
                    &ephemeral_ecdh_sk,
                    responder_longterm_ecdh_sk,
                    &tx2,
                );

                let aad = vec![];
                let ciphertext = serialize_encrypt_outer_payload(
                    &key_2,
                    OuterPayload::Query(MessageOriginator::Responder),
                    &aad,
                );

                (
                    Self {
                        responder_ecdh_sk: responder_longterm_ecdh_sk.clone(),
                        responder_pq_sk: None,
                        session_state: SessionState::query_mode(
                            responder_longterm_ecdh_pk,
                            &key_2,
                            &tx2,
                        ),
                    },
                    Message {
                        ephemeral_ecdh_pk,
                        ciphertext,
                        aad,
                    },
                )
            }
            OuterPayload::Registration {
                originator: MessageOriginator::Initiator,
            } => todo!(),
            _ => panic!("Only accept messages from the initiator"),
        }
    }
}

fn decrypt_deserialize_payload(key: &AEADKey, msg: &Message) -> OuterPayload {
    let mut payload_serialized = vec![0u8; msg.ciphertext.len() - 16];
    let _ = decrypt(
        key.as_ref(),
        &mut payload_serialized,
        &msg.ciphertext,
        &msg.aad,
        &[0; NONCE_LEN],
    )
    .unwrap();

    let received_payload = OuterPayload::tls_deserialize_exact_bytes(&payload_serialized).unwrap();
    received_payload
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_mode() {
        macro_rules! assert_state_agreement {
            ($i:ident, $r:ident, $field:ident) => {
                assert_eq!(
                    $i.session_state.$field,
                    $r.session_state.$field,
                    "Mismatch of session state field {}",
                    stringify!($field)
                );
            };
            ($i:ident, $r:ident, $field:ident, $($fields_rest:ident),+) => {
                assert_eq!(
                    $i.session_state.$field,
                    $r.session_state.$field,
                    "Mismatch of session state field {}",
                    stringify!($field)
                );
                assert_state_agreement!($i, $r, $($fields_rest),+);
            };
        }
        let mut rng = rand::rng();
        let ctx = b"Test Context";
        let responder_ecdh_sk = PrivateKey::new(&mut rng);
        let responder_ecdh_pk = PublicKey::from(&responder_ecdh_sk);

        // let mut mlkem_keygen_rand = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
        // rng.fill_bytes(&mut mlkem_keygen_rand);
        // let mlkem_key_pair = libcrux_ml_kem::mlkem768::generate_key_pair(mlkem_keygen_rand);

        let (initiator_pre, initiator_msg) = InitiatorPre::first_message(
            ProtocolMode::Query,
            &responder_ecdh_pk,
            ctx.as_slice(),
            &mut rng,
        );

        let (responder, responder_msg) = Responder::respond(
            &responder_ecdh_sk,
            &responder_ecdh_pk,
            &initiator_msg,
            ctx.as_slice(),
            &mut rng,
        );

        let initiator = initiator_pre.complete_registration(&responder_msg);

        assert_state_agreement!(
            initiator,
            responder,
            session_type,
            initiator_credential_vk,
            responder_longterm_ecdh_pk,
            responder_pq_pk,
            session_key
        );
    }
}
