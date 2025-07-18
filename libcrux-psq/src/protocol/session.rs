use libcrux_ml_kem::mlkem768::MlKem768PublicKey;

use super::{
    api::Error,
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

pub struct SessionState<'keys> {
    pub(crate) is_initiator: bool,
    pub(crate) nonce: u64,
    pub(crate) initiator_longterm_ecdh_pk: &'keys PublicKey,
    pub(crate) responder_longterm_ecdh_pk: &'keys PublicKey,
    pub(crate) responder_pq_pk: Option<&'keys MlKem768PublicKey>,
    pub(crate) session_key: SessionKey, // This carries a key_id that can also serve as the session ID
}

impl<'keys> SessionState<'keys> {
    pub fn new(
        is_initiator: bool,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        initiator_longterm_ecdh_pk: &'keys PublicKey,
        responder_pq_pk: Option<&'keys MlKem768PublicKey>,
        k2: &AEADKey,
        tx2: &Transcript,
    ) -> Result<Self, Error> {
        let session_key = derive_session_key(k2, tx2)?;
        Ok(Self {
            is_initiator,
            nonce: 0,
            initiator_longterm_ecdh_pk,
            responder_longterm_ecdh_pk,
            responder_pq_pk,
            session_key,
        })
    }
}
