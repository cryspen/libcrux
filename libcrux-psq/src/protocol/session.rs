use super::{
    ecdh::PublicKey,
    keys::{derive_session_key, AEADKey},
    transcript::Transcript,
};

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

/// The length of a sessin key in bytes.
pub const SESSION_KEY_LENGTH: usize = 32;

pub struct SessionKey {
    pub(crate) identifier: [u8; SESSION_ID_LENGTH],
    pub(crate) key: AEADKey,
}

pub(crate) enum SessionState {
    Query {
        responder_longterm_ecdh_pk: PublicKey,
        session_key: SessionKey, // This carries a key_id that can also serve as the session ID
    },
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        responder_longterm_ecdh_pk: PublicKey,
        responder_pq_pk: Option<libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        session_key: SessionKey, // This carries a key_id that can also serve as the session ID
    },
}

impl SessionState {
    pub(crate) fn query_mode(
        responder_longterm_ecdh_pk: &PublicKey,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Self {
        let session_key = derive_session_key(&k2, &tx2);
        Self::Query {
            session_key,
            responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
        }
    }

    pub(crate) fn registration_mode(
        responder_longterm_ecdh_pk: &PublicKey,
        initiator_longterm_ecdh_pk: &PublicKey,
        responder_pq_pk: Option<&libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Self {
        let session_key = derive_session_key(&k2, &tx2);
        Self::Registration {
            initiator_longterm_ecdh_pk: initiator_longterm_ecdh_pk.clone(),
            responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
            responder_pq_pk: responder_pq_pk.map(|i| *i.clone()),
            session_key,
        }
    }
}
