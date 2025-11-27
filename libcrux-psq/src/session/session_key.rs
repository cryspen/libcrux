//! # Session Keys
use tls_codec::{SerializeBytes, TlsDeserialize, TlsSerialize, TlsSerializeBytes, TlsSize};

use crate::{
    aead::{AEADKeyNonce, AEAD},
    handshake::transcript::Transcript,
};

use super::SessionError as Error;

/// The length of a session ID in bytes.
pub const SESSION_ID_LENGTH: usize = 32;

#[derive(TlsSerialize, TlsDeserialize, TlsSize)]
/// A long-term session key.
///
/// Derived from the final handshake states of the PSQ handshake. This key
/// is used to derive transport channel keys, and is not itself used for
/// transport encryption.
pub struct SessionKey {
    /// The session key identifier
    pub(crate) identifier: [u8; SESSION_ID_LENGTH],
    /// The actual key
    pub(crate) key: AEADKeyNonce,
}

const SESSION_KEY_INFO: &[u8] = b"session key id";
const SESSION_KEY_SALT: &[u8] = b"session key salt";

// id_skCS = KDF(skCS, "shared key id")
fn session_key_id(key: &AEADKeyNonce) -> Result<[u8; SESSION_ID_LENGTH], Error> {
    let mut session_id = [0u8; SESSION_ID_LENGTH];

    libcrux_hkdf::sha2_256::hkdf(
        &mut session_id,
        SESSION_KEY_SALT,
        &SerializeBytes::tls_serialize(&key).map_err(Error::Serialize)?,
        SESSION_KEY_INFO,
    )
    .map_err(|_| Error::CryptoError)?;

    Ok(session_id)
}

// skCS = KDF(K2, "session secret" | tx2)
pub(super) fn derive_session_key(
    k2: AEADKeyNonce,
    tx2: Transcript,
    aead_type: AEAD,
) -> Result<SessionKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct SessionKeyInfo<'a> {
        domain_separator: &'static [u8],
        tx2: &'a Transcript,
    }

    const SESSION_KEY_LABEL: &[u8] = b"session key";
    let key = AEADKeyNonce::new(
        &k2,
        &SessionKeyInfo {
            domain_separator: SESSION_KEY_LABEL,
            tx2: &tx2,
        },
        aead_type,
    )?;
    let identifier = session_key_id(&key)?;
    Ok(SessionKey { key, identifier })
}
