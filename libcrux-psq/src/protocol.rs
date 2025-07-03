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
    use crate::protocol::session::SessionState;

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

        let (initiator_pre, initiator_msg) =
            QueryInitiatorPre::first_message(&responder_ecdh_pk, ctx.as_slice(), &mut rng);

        let initiator_msg_wire = initiator_msg
            .tls_serialize()
            .expect("Failed to serialize initiator message");
        let initiator_msd_deserialized = Message::tls_deserialize_exact_bytes(&initiator_msg_wire)
            .expect("Failed to deserialize initiator message");

        let (responder, responder_msg) = Responder::respond(
            &responder_ecdh_sk,
            &responder_ecdh_pk,
            &initiator_msg_deserialized,
            ctx.as_slice(),
            &mut rng,
        );

        let initiator = initiator_pre.complete_registration(&responder_msg);

        let SessionState::Query {
            responder_longterm_ecdh_pk: i_responder_longterm_ecdh_pk,
            session_key: i_session_key,
        } = initiator.session_state
        else {
            panic!("Wrong session state at Initiator.")
        };

        let SessionState::Query {
            responder_longterm_ecdh_pk: r_responder_longterm_ecdh_pk,
            session_key: r_session_key,
        } = responder.session_state
        else {
            panic!("Wrong session state at Responder.")
        };

        assert_eq!(
            i_responder_longterm_ecdh_pk.as_ref(),
            r_responder_longterm_ecdh_pk.as_ref()
        );
        assert_eq!(i_session_key.as_ref(), r_session_key.as_ref());
    }
}
