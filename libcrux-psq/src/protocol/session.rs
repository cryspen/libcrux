use super::{
    ecdh::PublicKey,
    keys::{derive_session_key, AEADKey},
    // responder::ResponderRegistrationPayload,
    transcript::Transcript,
    // TransportMessage,
};

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

/// The length of a sessin key in bytes.
pub const SESSION_KEY_LENGTH: usize = 32;

pub struct SessionKey {
    pub(crate) identifier: [u8; SESSION_ID_LENGTH],
    pub(crate) key: AEADKey,
}

pub struct SessionState<'keys> {
    pub(crate) is_initiator: bool,
    pub(crate) nonce: u64,
    pub(crate) initiator_longterm_ecdh_pk: &'keys PublicKey,
    pub(crate) responder_longterm_ecdh_pk: &'keys PublicKey,
    pub(crate) responder_pq_pk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
    pub(crate) session_key: SessionKey, // This carries a key_id that can also serve as the session ID
}

impl<'keys> SessionState<'keys> {
    pub(crate) fn new(
        is_initiator: bool,
        // _responder_reg_info: &ResponderRegistrationPayload,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        initiator_longterm_ecdh_pk: &'keys PublicKey,
        responder_pq_pk: Option<&'keys libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Self {
        let session_key = derive_session_key(k2, tx2);
        Self {
            is_initiator,
            nonce: 0,
            initiator_longterm_ecdh_pk,
            responder_longterm_ecdh_pk,
            responder_pq_pk,
            session_key,
        }
    }

    // pub fn transport_encrypt(&mut self, _payload: &[u8], _aad: &[u8]) -> TransportMessage {
    //     todo!()
    // }

    // pub fn transport_decrypt(&mut self, _message: &TransportMessage) -> Vec<u8> {
    //     todo!()
    // }
}
