use super::{
    derive_session_key, ecdh::PublicKey, keys::AEADKey, transcript::Transcript, ProtocolMode,
};

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

/// The length of a sessin key in bytes.
pub const SESSION_KEY_LENGTH: usize = 32;

#[derive(Debug, PartialEq)]
pub struct SessionKey {
    pub(crate) identifier: [u8; SESSION_ID_LENGTH],
    pub(crate) key: AEADKey,
}

#[derive(Debug)]
pub struct SessionState {
    pub(crate) session_type: ProtocolMode,
    pub(crate) initiator_credential_vk: Option<PublicKey>,
    pub(crate) responder_longterm_ecdh_pk: PublicKey,
    pub(crate) responder_pq_pk: Option<Vec<u8>>,
    pub(crate) session_key: SessionKey, // This carries a key_id that can also serve as the session ID
}

impl SessionState {
    pub(crate) fn query_mode(
        responder_longterm_ecdh_pk: &PublicKey,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Self {
        let session_key = derive_session_key(&k2, &tx2);
        Self {
            session_type: ProtocolMode::Query,
            session_key,
            initiator_credential_vk: None,
            responder_longterm_ecdh_pk: responder_longterm_ecdh_pk.clone(),
            responder_pq_pk: None,
        }
    }
}
