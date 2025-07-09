//! The PSQ registration protocol
#![allow(missing_docs)]

use ecdh::PublicKey;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

mod ecdh;
pub mod initiator;
mod keys;
pub mod responder;
pub mod session;
mod transcript;

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct Message {
    ephemeral_ecdh_pk: PublicKey,
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

pub struct TransportMessage {
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use tls_codec::{DeserializeBytes, SerializeBytes};

    use crate::protocol::{
        initiator::InitiatorOuterPayload,
        responder::{Responder, ResponderQueryPayload},
    };

    use super::{
        ecdh::{KEMKeyPair, PrivateKey},
        initiator::{QueryInitiator, RegistrationInitiatorPre},
        responder::ResponderRegistrationPayload,
        *,
    };

    #[test]
    fn query_mode() {
        let mut rng = rand::rng();
        let ctx = b"Test Context".as_slice();
        let aad_initiator = b"Test Data I".as_slice();
        let aad_responder = b"Test Data R".as_slice();

        let responder_longterm_ecdh_keys = KEMKeyPair::new(&mut rng);

        let (initiator_pre, initiator_msg) = QueryInitiator::query(
            &responder_longterm_ecdh_keys.pk,
            ctx,
            aad_initiator,
            &mut rng,
        )
        .expect("Failed to build initiator query message");

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (initiator_outer_payload, tx0, k0) = Responder::decrypt_outer(
            &responder_longterm_ecdh_keys,
            &initiator_msg_deserialized,
            ctx,
        );

        assert!(initiator_outer_payload.as_query_msg().is_some());

        let responder_message = Responder::respond_query(
            &responder_longterm_ecdh_keys.sk,
            &tx0,
            &k0,
            &initiator_msg_deserialized,
            &ResponderQueryPayload {},
            aad_responder,
            &mut rng,
        )
        .expect("Failed to build responder query response");

        let responder_message_serialized = responder_message
            .tls_serialize()
            .expect("Failed to serialize responder message");

        let responder_message_deserialized =
            Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                .expect("Failed to deserialize responder message");

        let _received_response = initiator_pre.read_response(&responder_message_deserialized);
    }

    #[test]
    fn registration_mode_pq() {
        let mut rng = rand::rng();
        let ctx = b"Test Context".as_slice();
        let aad_initiator_outer = b"Test Data I outer".as_slice();
        let aad_initiator_inner = b"Test Data I inner".as_slice();
        let aad_responder = b"Test Data R".as_slice();

        let responder_longterm_ecdh_keys = KEMKeyPair::new(&mut rng);
        let initiator_longterm_ecdh_keys = KEMKeyPair::new(&mut rng);
        let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);

        let (initiator_pre, initiator_msg) = RegistrationInitiatorPre::registration_message(
            &initiator_longterm_ecdh_keys,
            Some(responder_pq_keys.public_key()),
            &responder_longterm_ecdh_keys.pk,
            ctx,
            aad_initiator_outer,
            aad_initiator_inner,
            &mut rng,
        )
        .expect("Failed to build initiator registration message");

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (initiator_outer_payload, tx0, k0) = Responder::decrypt_outer(
            &responder_longterm_ecdh_keys,
            &initiator_msg_deserialized,
            ctx,
        );

        let Some((initiator_longterm_ecdh_pk, pq_encaps, ciphertext, aad)) =
            initiator_outer_payload.as_registration_msg()
        else {
            panic!("Wrong message type from initiator");
        };

        let (_inner_payload, state) = Responder::decrypt_inner(
            &responder_longterm_ecdh_keys.sk,
            &responder_pq_keys,
            &tx0,
            &k0,
            &initiator_longterm_ecdh_pk,
            pq_encaps,
            &ciphertext,
            &aad,
        );

        // pretend we did some validation of the inner_payload here
        let (session_state_responder, responder_message) = Responder::respond_registration(
            &responder_longterm_ecdh_keys.pk,
            responder_pq_keys.public_key(),
            &state,
            &initiator_longterm_ecdh_pk,
            &initiator_msg_deserialized,
            &ResponderRegistrationPayload {},
            aad_responder,
            &mut rng,
        )
        .expect("Failed to build responder registration message");

        let responder_message_serialized = responder_message
            .tls_serialize()
            .expect("Failed to serialize responder message");

        let responder_message_deserialized =
            Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                .expect("Failed to deserialize responder message");

        let session_state_initiator =
            initiator_pre.complete_registration(&responder_message_deserialized);

        assert_eq!(
            session_state_initiator.initiator_longterm_ecdh_pk.as_ref(),
            session_state_responder.initiator_longterm_ecdh_pk.as_ref()
        );
        assert_eq!(
            session_state_initiator.responder_longterm_ecdh_pk.as_ref(),
            session_state_responder.responder_longterm_ecdh_pk.as_ref()
        );
        match (
            session_state_initiator.responder_pq_pk,
            session_state_responder.responder_pq_pk,
        ) {
            (Some(pk_at_i), Some(pk_at_r)) => {
                assert_eq!(pk_at_i.as_ref(), pk_at_r.as_ref())
            }
            (None, None) => (),
            _ => panic!("Incongruent session state: responder PQ public key"),
        }

        assert_eq!(
            session_state_initiator.session_key.identifier,
            session_state_responder.session_key.identifier
        );
        assert_eq!(
            session_state_initiator.session_key.key.as_ref(),
            session_state_responder.session_key.key.as_ref()
        );
    }

    #[test]
    fn registration_mode_classical() {
        let mut rng = rand::rng();
        let ctx = b"Test Context".as_slice();
        let aad_initiator_outer = b"Test Data I outer".as_slice();
        let aad_initiator_inner = b"Test Data I inner".as_slice();
        let aad_responder = b"Test Data R".as_slice();

        let responder_longterm_ecdh_keys = KEMKeyPair::new(&mut rng);
        let initiator_longterm_ecdh_keys = KEMKeyPair::new(&mut rng);
        let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);

        let (initiator_pre, initiator_msg) = RegistrationInitiatorPre::registration_message(
            &initiator_longterm_ecdh_keys,
            None,
            &responder_longterm_ecdh_keys.pk,
            ctx,
            aad_initiator_outer,
            aad_initiator_inner,
            &mut rng,
        )
        .expect("Failed to build initiator registration message");

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (initiator_outer_payload, tx0, k0) = Responder::decrypt_outer(
            &responder_longterm_ecdh_keys,
            &initiator_msg_deserialized,
            ctx,
        );

        let Some((initiator_longterm_ecdh_pk, pq_encaps, ciphertext, aad)) =
            initiator_outer_payload.as_registration_msg()
        else {
            panic!("Wrong message type from initiator");
        };
        let (_inner_payload, state) = Responder::decrypt_inner(
            &responder_longterm_ecdh_keys.sk,
            &responder_pq_keys,
            &tx0,
            &k0,
            &initiator_longterm_ecdh_pk,
            pq_encaps,
            &ciphertext,
            &aad,
        );

        // pretend we did some validation of the inner_payload here
        let (session_state_responder, responder_message) = Responder::respond_registration(
            &responder_longterm_ecdh_keys.pk,
            responder_pq_keys.public_key(),
            &state,
            &initiator_longterm_ecdh_pk,
            &initiator_msg_deserialized,
            &ResponderRegistrationPayload {},
            aad_responder,
            &mut rng,
        )
        .expect("Failed to build initiator registration message");

        let responder_message_serialized = responder_message
            .tls_serialize()
            .expect("Failed to serialize responder message");

        let responder_message_deserialized =
            Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                .expect("Failed to deserialize responder message");

        let session_state_initiator =
            initiator_pre.complete_registration(&responder_message_deserialized);

        assert_eq!(
            session_state_initiator.initiator_longterm_ecdh_pk.as_ref(),
            session_state_responder.initiator_longterm_ecdh_pk.as_ref()
        );
        assert_eq!(
            session_state_initiator.responder_longterm_ecdh_pk.as_ref(),
            session_state_responder.responder_longterm_ecdh_pk.as_ref()
        );
        match (
            session_state_initiator.responder_pq_pk,
            session_state_responder.responder_pq_pk,
        ) {
            (Some(pk_at_i), Some(pk_at_r)) => {
                assert_eq!(pk_at_i.as_ref(), pk_at_r.as_ref())
            }
            (None, None) => (),
            _ => panic!("Incongruent session state: responder PQ public key"),
        }

        assert_eq!(
            session_state_initiator.session_key.identifier,
            session_state_responder.session_key.identifier
        );
        assert_eq!(
            session_state_initiator.session_key.key.as_ref(),
            session_state_responder.session_key.key.as_ref()
        );
    }
}
