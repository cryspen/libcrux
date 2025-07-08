use super::{
    ecdh::PublicKey,
    keys::{derive_session_key, AEADKey},
    responder::ResponderRegistrationPayload,
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

pub(crate) struct SessionState<'keys> {
    initiator_longterm_ecdh_pk: &'keys PublicKey,
    responder_longterm_ecdh_pk: &'keys PublicKey,
    responder_pq_pk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
    session_key: SessionKey, // This carries a key_id that can also serve as the session ID
}

impl<'keys> SessionState<'keys> {
    pub(crate) fn new(
        _responder_reg_info: &ResponderRegistrationPayload,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        initiator_longterm_ecdh_pk: &'keys PublicKey,
        responder_pq_pk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Self {
        let session_key = derive_session_key(&k2, &tx2);
        Self {
            initiator_longterm_ecdh_pk,
            responder_longterm_ecdh_pk,
            responder_pq_pk,
            session_key,
        }
    }
}
