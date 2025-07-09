//! The PSQ registration protocol
#![allow(missing_docs)]

use ecdh::PublicKey;
use libcrux_ml_kem::mlkem768::MlKem768Ciphertext;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

mod ecdh;
pub mod initiator;
mod keys;
pub mod responder;
pub mod session;
mod transcript;

const TTL_THRESHOLD: std::time::Duration = std::time::Duration::from_secs(2);

#[derive(Copy, Clone)]
pub struct InitiatorAppContext<'context> {
    pub context: &'context [u8],
    pub aad_inner: Option<&'context [u8]>,
    pub aad_outer: Option<&'context [u8]>,
}

pub struct ResponderAppContext<'context> {
    pub context: &'context [u8],
    pub aad: Option<&'context [u8]>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct Message {
    pk: PublicKey,
    ciphertext: Vec<u8>,
    pq_encaps: Option<MlKem768Ciphertext>,
    aad: Option<Vec<u8>>,
}

pub struct TransportMessage {
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, time::Duration};

    use tls_codec::{DeserializeBytes, SerializeBytes};

    use crate::protocol::{
        initiator::{InitiatorOuterPayload, ResponderKeyPackage},
        responder::{Responder, ResponderQueryPayload},
    };

    use super::{
        ecdh::KEMKeyPair,
        initiator::{QueryInitiator, RegistrationInitiatorPre},
        responder::ResponderRegistrationPayload,
        *,
    };

    #[test]
    fn query() {
        let mut rng = rand::rng();
        let context = b"Test Context".as_slice();
        let aad_initiator = b"Test Data I".as_slice();
        let aad_responder = b"Test Data R".as_slice();
        let query = b"Application Query".as_slice();
        let response = b"Application Response".as_slice();

        let mut eph_keys: HashMap<PublicKey, Duration> = HashMap::new();

        let responder_keys = KEMKeyPair::new(&mut rng);

        let responder_key_package = ResponderKeyPackage {
            kem_pk: &responder_keys.pk,
            pq_pk: None,
        };

        let initiator_context = InitiatorAppContext {
            context,
            aad_outer: Some(aad_initiator),
            aad_inner: None,
        };

        let responder_context = ResponderAppContext {
            context,
            aad: Some(aad_responder),
        };

        let (initiator_pre, initiator_msg) =
            QueryInitiator::query(&responder_key_package, &initiator_context, query, &mut rng)
                .expect("Failed to build initiator query message");

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (initiator_outer_payload, tx0, k0, initiator_eph_pk) = Responder::decrypt_outer(
            &mut eph_keys,
            &responder_keys,
            &responder_context,
            initiator_msg_deserialized,
        )
        .expect("Failed to read query");

        let Some(received_query) = initiator_outer_payload.as_query_msg() else {
            panic!("Wrong message type from initiator")
        };

        assert_eq!(received_query, query);

        let responder_message = Responder::respond_query(
            &responder_keys,
            &responder_context,
            &initiator_eph_pk,
            &tx0,
            &k0,
            &ResponderQueryPayload(response.to_vec()),
            &mut rng,
        )
        .expect("Failed to build responder query response");

        let responder_message_serialized = responder_message
            .tls_serialize()
            .expect("Failed to serialize responder message");

        let responder_message_deserialized =
            Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                .expect("Failed to deserialize responder message");

        let received_response = initiator_pre
            .read_response(responder_message_deserialized)
            .expect("Failed to read query response");

        assert_eq!(received_response.as_ref(), response)
    }

    #[test]
    fn registration_pq() {
        registration(true)
    }

    #[test]
    fn registration_classical() {
        registration(false)
    }

    fn registration(pq: bool) {
        let mut rng = rand::rng();
        let context = b"Test Context".as_slice();
        let aad_initiator_outer = b"Test Data I outer".as_slice();
        let aad_initiator_inner = b"Test Data I inner".as_slice();
        let aad_responder = b"Test Data R".as_slice();
        let registration_payload = b"Application Payload".as_slice();
        let response = b"Application Response".as_slice();

        let mut eph_keys: HashMap<PublicKey, Duration> = HashMap::new();

        let responder_keys = KEMKeyPair::new(&mut rng);
        let initiator_keys = KEMKeyPair::new(&mut rng);
        let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);

        let initiator_context = InitiatorAppContext {
            context,
            aad_outer: Some(aad_initiator_outer),
            aad_inner: Some(aad_initiator_inner),
        };

        let responder_context = ResponderAppContext {
            context,
            aad: Some(aad_responder),
        };

        let responder_key_package = ResponderKeyPackage {
            kem_pk: &responder_keys.pk,
            pq_pk: pq.then_some(responder_pq_keys.public_key()),
        };

        let (initiator_pre, initiator_msg) = RegistrationInitiatorPre::registration_message(
            &initiator_keys,
            &responder_key_package,
            &initiator_context,
            registration_payload,
            &mut rng,
        )
        .expect("Failed to build initiator registration message");

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msg_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (initiator_outer_payload, tx0, k0, initiator_eph_pk) = Responder::decrypt_outer(
            &mut eph_keys,
            &responder_keys,
            &responder_context,
            initiator_msg_deserialized,
        )
        .expect("Failed to read registration message");

        let Some(registration_msg) = initiator_outer_payload.as_registration_msg() else {
            panic!("Wrong message type from initiator");
        };

        let (inner_payload, state) = Responder::decrypt_inner(
            &responder_keys,
            &responder_pq_keys,
            &tx0,
            &k0,
            registration_msg,
            &initiator_eph_pk,
        )
        .expect("Failed to read registration_payload");

        assert_eq!(inner_payload.0, registration_payload);

        let response_payload = ResponderRegistrationPayload(response.to_vec());
        // pretend we did some validation of the inner_payload here
        let (session_state_responder, responder_message) = Responder::respond_registration(
            &responder_keys,
            &responder_pq_keys,
            &responder_context,
            &state,
            &response_payload,
            &mut rng,
        )
        .expect("Failed to build responder registration message");

        let responder_message_serialized = responder_message
            .tls_serialize()
            .expect("Failed to serialize responder message");

        let responder_message_deserialized =
            Message::tls_deserialize_exact_bytes(&responder_message_serialized)
                .expect("Failed to deserialize responder message");

        let session_state_initiator = initiator_pre
            .complete_registration(&responder_message_deserialized)
            .expect("Failed to read registration response");

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
