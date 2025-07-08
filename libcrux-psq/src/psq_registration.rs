//! The PSQ registration protocol
#![allow(missing_docs)]

use libcrux_chacha20poly1305::{decrypt, NONCE_LEN};
use libcrux_ecdh::{derive, generate_secret, secret_to_public};
use libcrux_sha2::SHA256_LENGTH;
use rand::{rng, CryptoRng};
use tls_codec::{
    DeserializeBytes, SerializeBytes, TlsDeserializeBytes, TlsSerializeBytes, TlsSize,
};

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

/// The length of a sessin key in bytes.
pub const SESSION_KEY_LENGTH: usize = 32;

pub const TX0_LENGTH: usize = 32;
pub const TX0_DOMAIN_SEP: u8 = 0;
pub const TX1_DOMAIN_SEP: u8 = 1;
pub const TX2_DOMAIN_SEP: u8 = 2;

/// The protocol initiator's initial state
pub struct InitiatorPre {
    responder_longterm_ecdh_pk: Vec<u8>,
    initiator_ephemeral_ecdh_pk: Vec<u8>,
    initiator_ephemeral_ecdh_sk: Vec<u8>,
    tx0: [u8; 32],
    tx1: Option<[u8; 32]>,
}

#[derive(Debug, PartialEq)]
pub struct SessionKey {
    identifier: [u8; SESSION_ID_LENGTH],
    key: [u8; SESSION_KEY_LENGTH],
}

#[derive(Debug)]
pub struct SessionState {
    pub(crate) session_identifier: usize,
    pub(crate) initiator_ecdh_pk: Vec<u8>,
    pub(crate) responder_ecdh_pk: Vec<u8>,
    pub(crate) responder_pq_pk: Option<Vec<u8>>,
    pub(crate) session_key: SessionKey,
}

pub struct InitiatorDone {
    pub(crate) initiator_ecdh_sk: Vec<u8>,
    pub(crate) session_state: SessionState,
}

pub struct Responder {
    pub(crate) responder_ecdh_sk: Vec<u8>,
    pub(crate) responder_pq_sk: Option<Vec<u8>>,
    pub(crate) session_state: SessionState,
}

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
pub enum OuterPayload {
    Query(MessageOriginator),
    Registration { originator: MessageOriginator },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
struct Message {
    ephemeral_ecdh_pk: Vec<u8>,
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

fn tx0(ctxt: &[u8], responder_ecdh_pk: &[u8], initiator_ecdh_pk: &[u8]) -> [u8; SHA256_LENGTH] {
    let mut input = ctxt.to_vec();
    input.extend_from_slice(responder_ecdh_pk);
    input.extend_from_slice(initiator_ecdh_pk);

    tx::<TX0_DOMAIN_SEP>(&input)
}

fn tx2(prev_tx: &[u8], responder_ephemeral_pk: &[u8]) -> [u8; SHA256_LENGTH] {
    let mut input = prev_tx.to_vec();
    input.extend_from_slice(responder_ephemeral_pk);

    tx::<TX2_DOMAIN_SEP>(&input)
}

fn tx<const DOMAIN_SEPARATOR: u8>(input: &[u8]) -> [u8; SHA256_LENGTH] {
    let mut domain_separated_input = vec![DOMAIN_SEPARATOR];
    domain_separated_input.extend_from_slice(input);
    libcrux_sha2::sha256(input)
}

fn k0(point: &[u8], scalar: &[u8], tx0: &[u8; SHA256_LENGTH]) -> [u8; 32] {
    let ikm = libcrux_ecdh::derive(libcrux_ecdh::Algorithm::X25519, point, scalar).unwrap();
    let prk = libcrux_hkdf::extract(libcrux_hkdf::Algorithm::Sha256, &[], &ikm).unwrap();
    libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, prk, tx0, 32)
        .unwrap()
        .try_into()
        .unwrap()
}

fn k2(ikm: &[u8], prev_tx: &[u8; SHA256_LENGTH]) -> [u8; 32] {
    let prk = libcrux_hkdf::extract(libcrux_hkdf::Algorithm::Sha256, &[], &ikm).unwrap();
    libcrux_hkdf::expand(libcrux_hkdf::Algorithm::Sha256, prk, prev_tx, 32)
        .unwrap()
        .try_into()
        .unwrap()
}

impl InitiatorPre {
    pub fn first_message(
        mode: ProtocolMode,
        responder_longterm_ecdh_pk: &[u8],
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let initiator_ephemeral_ecdh_sk =
            generate_secret(libcrux_ecdh::Algorithm::X25519, rng).expect("Insufficient Randomness");
        let initiator_ephemeral_ecdh_pk = secret_to_public(
            libcrux_ecdh::Algorithm::X25519,
            &initiator_ephemeral_ecdh_sk,
        )
        .unwrap();

        let (tx0, key_0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            &ctx,
            false,
        );

        let payload0 = match mode {
            ProtocolMode::Registration => todo!(),
            ProtocolMode::Query => OuterPayload::Query(MessageOriginator::Initiator),
        };

        let aad = vec![];
        let ciphertext = serialize_encrypt_outer_payload(&key_0, payload0, &aad);

        (
            Self {
                tx0,
                tx1: None,
                responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.to_vec(),
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

    fn complete_registration(self, responder_msg: &Message) -> InitiatorDone {
        let tx2 = tx2(&self.tx0, &responder_msg.ephemeral_ecdh_pk);

        let key_2 = derive_k2_query_initiator(
            &self.initiator_ephemeral_ecdh_pk,
            &responder_msg.ephemeral_ecdh_pk,
            &self.initiator_ephemeral_ecdh_sk,
            &self.responder_longterm_ecdh_pk,
            &tx2,
        );

        let payload2 = decrypt_deserialize_payload(&key_2, responder_msg);

        match payload2 {
            OuterPayload::Query(MessageOriginator::Responder) => todo!(),
            OuterPayload::Registration {
                originator: MessageOriginator::Responder,
            } => todo!(),
            _ => panic!("Only accept messages from the Responder"),
        }

        let session_key = derive_session_key(&key_2, &tx2);
        todo!()
    }
}

fn derive_session_key(k2: &[u8; 32], tx_2: &[u8; 32]) -> [u8; 32] {
    todo!()
}
fn serialize_encrypt_outer_payload(key: &[u8; 32], payload: OuterPayload, aad: &[u8]) -> Vec<u8> {
    let payload_serialized = payload.tls_serialize().unwrap();
    let mut ciphertext = vec![0u8; payload_serialized.len() + 16];
    let (ciphertext_ref, tag_ref) = libcrux_chacha20poly1305::encrypt(
        key,
        &payload_serialized,
        &mut ciphertext,
        aad,
        &[0; NONCE_LEN],
    )
    .expect("Encryption Error");

    ciphertext
}

fn derive_k0(
    responder_ecdh_pk: &[u8],
    ephemeral_ecdh_pk: &[u8],
    own_ecdh_sk: &[u8],
    ctx: &[u8],
    responder: bool,
) -> ([u8; 32], [u8; 32]) {
    let tx0 = tx0(ctx, responder_ecdh_pk, &ephemeral_ecdh_pk);
    if responder {
        (tx0, k0(ephemeral_ecdh_pk, &own_ecdh_sk, &tx0))
    } else {
        (tx0, k0(responder_ecdh_pk, &own_ecdh_sk, &tx0))
    }
}

fn derive_k2_query_responder(
    initiator_ephemeral_ecdh_pk: &[u8],
    responder_ephemeral_ecdh_pk: &[u8],
    responder_ephemeral_ecdh_sk: &[u8],
    responder_longterm_ecdh_sk: &[u8],
    tx2: &[u8; 32],
) -> [u8; 32] {
    let mut ikm = derive(
        libcrux_ecdh::Algorithm::X25519,
        initiator_ephemeral_ecdh_pk,
        responder_longterm_ecdh_sk,
    )
    .unwrap();
    let g_xy = derive(
        libcrux_ecdh::Algorithm::X25519,
        initiator_ephemeral_ecdh_pk,
        responder_ephemeral_ecdh_sk,
    )
    .unwrap();

    ikm.extend_from_slice(&g_xy);

    k2(&ikm, tx2)
}

fn derive_k2_query_initiator(
    initiator_ephemeral_ecdh_pk: &[u8],
    responder_ephemeral_ecdh_pk: &[u8],
    initiator_ephemeral_ecdh_sk: &[u8],
    responder_longterm_ecdh_pk: &[u8],
    tx2: &[u8; 32],
) -> [u8; 32] {
    let mut ikm = derive(
        libcrux_ecdh::Algorithm::X25519,
        responder_longterm_ecdh_pk,
        initiator_ephemeral_ecdh_sk,
    )
    .unwrap();
    let g_xy = derive(
        libcrux_ecdh::Algorithm::X25519,
        responder_ephemeral_ecdh_pk,
        initiator_ephemeral_ecdh_sk,
    )
    .unwrap();

    ikm.extend_from_slice(&g_xy);

    k2(&ikm, tx2)
}

impl Responder {
    // This doesn't check if the Initiator key is fresh, which should be done outside.
    fn respond(
        responder_longterm_ecdh_sk: &[u8],
        responder_longterm_ecdh_pk: &[u8],
        initiator_msg: &Message,
        ctx: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let (tx0, key_0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_msg.ephemeral_ecdh_pk,
            responder_longterm_ecdh_sk,
            ctx,
            true,
        );

        let received_payload = decrypt_deserialize_payload(&key_0, initiator_msg);

        let ephemeral_ecdh_sk =
            generate_secret(libcrux_ecdh::Algorithm::X25519, rng).expect("Insufficient Randomness");
        let ephemeral_ecdh_pk =
            secret_to_public(libcrux_ecdh::Algorithm::X25519, &ephemeral_ecdh_sk).unwrap();

        match received_payload {
            OuterPayload::Query(MessageOriginator::Initiator) => {
                let tx2 = tx2(&tx0, &ephemeral_ecdh_pk);
                let key_2 = derive_k2_query_responder(
                    &initiator_msg.ephemeral_ecdh_pk,
                    &ephemeral_ecdh_pk,
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
                        responder_ecdh_sk: todo!(),
                        responder_pq_sk: todo!(),
                        session_state: todo!(),
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

fn decrypt_deserialize_payload(key: &[u8; 32], msg: &Message) -> OuterPayload {
    let mut payload_serialized = vec![0u8; msg.ciphertext.len() - 16];
    let payload_serialized_ref = decrypt(
        key,
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
    use std::time::Duration;

    use libcrux_ecdh::{generate_secret, key_gen, secret_to_public};
    use rand::RngCore;

    use crate::{
        cred::{Ed25519, NoAuth},
        impls::MlKem768,
    };

    use super::*;

    #[test]
    fn registration_mode() {
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
        let responder_ecdh_sk = generate_secret(libcrux_ecdh::Algorithm::X25519, &mut rng).unwrap();
        let responder_ecdh_pk =
            secret_to_public(libcrux_ecdh::Algorithm::X25519, &responder_ecdh_sk).unwrap();

        let mut mlkem_keygen_rand = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
        rng.fill_bytes(&mut mlkem_keygen_rand);
        let mlkem_key_pair = libcrux_ml_kem::mlkem768::generate_key_pair(mlkem_keygen_rand);

        let (initiator_pre, initiator_msg) = InitiatorPre::first_message(
            ProtocolMode::Registration,
            &responder_ecdh_pk,
            ctx.as_slice(),
            &mut rng,
        );

        let (responder, responder_msg) = Responder::respond(
            &responder_ecdh_sk,
            &responder_ecdh_sk,
            &initiator_msg,
            ctx.as_slice(),
            &mut rng,
        );

        let initiator = initiator_pre.complete_registration(&responder_msg);

        assert_state_agreement!(
            initiator,
            responder,
            session_identifier,
            initiator_ecdh_pk,
            responder_ecdh_pk,
            responder_pq_pk,
            session_key
        );
    }
}
