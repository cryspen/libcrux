use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize};

use super::keys::AEADKey;

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

/// The length of a sessin key in bytes.
pub const SESSION_KEY_LENGTH: usize = 32;

// XXX: Session storage to be implemented (cf. https://github.com/cryspen/libcrux/issues/1077)
#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
pub struct SessionKey {
    pub(crate) identifier: [u8; SESSION_ID_LENGTH],
    pub(crate) key: AEADKey,
}
