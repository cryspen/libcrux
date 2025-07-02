//! The PSQ registration protocol
#![allow(missing_docs)]

use ecdh::{PrivateKey, PublicKey};
use libcrux_ml_kem::mlkem768::MlKem768PublicKey;
use signature::CredentialKeyPair;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

mod ecdh;
mod initiator;
mod keys;
mod responder;
mod session;
mod signature;
mod transcript;

#[derive(Debug, PartialEq)]
pub enum ProtocolMode {
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        initiator_longterm_ecdh_sk: PrivateKey,
        responder_pq_pk: Option<MlKem768PublicKey>,
    },
    Query,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub(crate) struct Message {
    ephemeral_ecdh_pk: PublicKey,
    ciphertext: Vec<u8>,
    aad: Vec<u8>,
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

        assert!(matches!(
            initiator.session_state,
            SessionState::Query { .. }
        ));

        assert_eq!(initiator.session_state, responder.session_state);
    }
}
