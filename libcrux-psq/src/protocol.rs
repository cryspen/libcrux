//! The PSQ registration protocol
#![allow(missing_docs)]

use ecdh::PublicKey;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

mod ecdh;
mod initiator;
mod keys;
mod responder;
mod session;
mod signature;
mod transcript;

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub(crate) struct Message {
    ephemeral_ecdh_pk: PublicKey,
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use tls_codec::{DeserializeBytes, SerializeBytes, Size};

    use crate::protocol::{
        initiator::InitiatorOuterPayload,
        responder::{Responder, ResponderPayload, ResponderQueryPayload},
        session::SessionState,
    };

    use super::{
        ecdh::PrivateKey,
        initiator::{QueryInitiator, RegistrationInitiatorPre},
        responder::ResponderRegistrationPayload,
        *,
    };

    #[test]
    fn query_mode() {
        let mut rng = rand::rng();
        let ctx = b"Test Context";
        let aad_initiator = b"Test Data I";
        let aad_responder = b"Test Data R";

        let responder_ecdh_sk = PrivateKey::new(&mut rng);
        let responder_ecdh_pk = PublicKey::from(&responder_ecdh_sk);

        let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);
        let (initiator_pre, initiator_msg) = QueryInitiator::query(
            &responder_ecdh_pk,
            ctx.as_slice(),
            aad_initiator.as_slice(),
            &mut rng,
        );

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        match Responder::decrypt_outer(
            &responder_ecdh_sk,
            &responder_ecdh_pk,
            responder_pq_keys.public_key(),
            responder_pq_keys.private_key(),
            &initiator_msg_deserialized,
            ctx.as_slice(),
            &mut rng,
        ) {
            (InitiatorOuterPayload::Query, tx0, k0) => {
                let responder_message = Responder::respond_query(
                    &responder_ecdh_sk,
                    &tx0,
                    &k0,
                    &initiator_msg_deserialized,
                    &ResponderQueryPayload {},
                    aad_responder.as_slice(),
                    &mut rng,
                );

                let responder_message_serialized = responder_message
                    .tls_serialize()
                    .expect("Failed to serialize responder message");

                let responder_message_deserialized =
                    Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                        .expect("Failed to deserialize responder message");

                let received_response =
                    initiator_pre.read_response(&responder_message_deserialized);
            }

            _ => panic!("Wrong message from query initiator"),
        }
    }

    #[test]
    fn registration_mode() {
        let mut rng = rand::rng();
        let ctx = b"Test Context";
        let aad_initiator_outer = b"Test Data I outer";
        let aad_initiator_inner = b"Test Data I inner";
        let aad_responder = b"Test Data R";

        let responder_ecdh_sk = PrivateKey::new(&mut rng);
        let responder_ecdh_pk = PublicKey::from(&responder_ecdh_sk);

        let initator_ecdh_sk = PrivateKey::new(&mut rng);
        let initiator_ecdh_pk = PublicKey::from(&responder_ecdh_sk);

        let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);
        let (initiator_pre, initiator_msg) = RegistrationInitiatorPre::registration_message(
            &initiator_ecdh_pk,
            &initator_ecdh_sk,
            Some(&responder_pq_keys.public_key()),
            &responder_ecdh_pk,
            ctx.as_slice(),
            aad_initiator_outer.as_slice(),
            aad_initiator_inner.as_slice(),
            &mut rng,
        );

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        match Responder::decrypt_outer(
            &responder_ecdh_sk,
            &responder_ecdh_pk,
            responder_pq_keys.public_key(),
            responder_pq_keys.private_key(),
            &initiator_msg_deserialized,
            ctx.as_slice(),
            &mut rng,
        ) {
            (
                InitiatorOuterPayload::Registration {
                    initiator_longterm_ecdh_pk,
                    pq_encaps,
                    ciphertext,
                    aad,
                },
                tx0,
                k0,
            ) => {
                let (inner_payload, tx1, k1) = Responder::decrypt_inner(
                    &responder_ecdh_sk,
                    &responder_ecdh_pk,
                    responder_pq_keys.private_key(),
                    responder_pq_keys.public_key(),
                    &tx0,
                    &k0,
                    &initiator_longterm_ecdh_pk,
                    pq_encaps.as_ref(),
                    &ciphertext,
                    &aad,
                );

                // pretend we did some validation of the inner_payload here
                let (session_state_responder, responder_message) = Responder::respond_registration(
                    &responder_ecdh_sk,
                    &responder_ecdh_pk,
                    Some(responder_pq_keys.private_key()),
                    Some(responder_pq_keys.public_key()),
                    &tx1,
                    &k1,
                    &initiator_longterm_ecdh_pk,
                    &initiator_msg_deserialized,
                    &ResponderRegistrationPayload {},
                    aad_responder.as_slice(),
                    &mut rng,
                );

                let responder_message_serialized = responder_message
                    .tls_serialize()
                    .expect("Failed to serialize responder message");

                let responder_message_deserialized =
                    Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                        .expect("Failed to deserialize responder message");

                let session_state_initiator =
                    initiator_pre.complete_registration(&responder_message_deserialized);
            }

            _ => panic!("Wrong message from query initiator"),
        }
    }
}
