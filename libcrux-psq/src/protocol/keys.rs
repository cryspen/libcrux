use libcrux_chacha20poly1305::{decrypt_detached, encrypt_detached, KEY_LEN, NONCE_LEN};
use libcrux_hkdf::Algorithm;
use tls_codec::{Deserialize, Serialize, SerializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    api::Error,
    ecdh::{PrivateKey, PublicKey, SharedSecret},
    session::{SessionKey, SESSION_ID_LENGTH},
    transcript::{self, Transcript},
};

#[derive(Default, Clone, TlsSerializeBytes, TlsSize)]
pub struct AEADKey([u8; KEY_LEN], #[tls_codec(skip)] [u8; NONCE_LEN]);

impl std::fmt::Debug for AEADKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("AEADKey").field(&"***").finish()
    }
}

fn serialize_error(e: tls_codec::Error) -> Error {
    Error::Serialize(e)
}

impl AEADKey {
    fn new(ikm: &impl SerializeBytes, info: &impl SerializeBytes) -> Result<AEADKey, Error> {
        let prk = libcrux_hkdf::extract(
            Algorithm::Sha256,
            [],
            ikm.tls_serialize().map_err(serialize_error)?,
        )
        .map_err(|_| Error::CryptoError)?;

        Ok(AEADKey(
            libcrux_hkdf::expand(
                Algorithm::Sha256,
                prk,
                info.tls_serialize().map_err(serialize_error)?,
                KEY_LEN,
            )
            .map_err(|_| Error::CryptoError)?
            .try_into()
            .map_err(|_| Error::CryptoError)?, // We don't expect this to fail, unless HDKF gave us the wrong output length,
            [0u8; NONCE_LEN],
        ))
    }

    fn increment_nonce(&mut self) {
        let mut buf = [0u8; 16];
        buf[16 - NONCE_LEN..].copy_from_slice(self.1.as_slice());
        let mut nonce = u128::from_be_bytes(buf);
        nonce += 1;
        let buf = nonce.to_be_bytes();
        self.1.copy_from_slice(&buf[16 - NONCE_LEN..]);
    }

    pub(crate) fn encrypt(
        &mut self,
        payload: &[u8],
        aad: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<[u8; 16], crate::protocol::api::Error> {
        let mut tag = [0u8; 16];

        // XXX: We could do better if we'd have an inplace API here.
        let _ = encrypt_detached(&self.0, payload, ciphertext, &mut tag, aad, &self.1)
            .map_err(|_| Error::CryptoError)?;

        self.increment_nonce();

        Ok(tag)
    }

    pub(crate) fn serialize_encrypt<T: Serialize>(
        &mut self,
        payload: &T,
        aad: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), crate::protocol::api::Error> {
        let serialization_buffer = payload.tls_serialize_detached().map_err(Error::Serialize)?;

        let mut ciphertext = vec![0u8; serialization_buffer.len()];
        let tag = self.encrypt(&serialization_buffer, aad, &mut ciphertext)?;

        Ok((ciphertext, tag))
    }

    pub(crate) fn decrypt(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let mut plaintext = vec![0u8; ciphertext.len()];
        let _ = decrypt_detached(&self.0, &mut plaintext, ciphertext, tag, aad, &self.1)
            .map_err(|_| Error::CryptoError)?;

        self.increment_nonce();

        Ok(plaintext)
    }

    pub(crate) fn decrypt_deserialize<T: Deserialize>(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
    ) -> Result<T, crate::protocol::api::Error> {
        let payload_serialized_buf = self.decrypt(ciphertext, tag, aad)?;

        T::tls_deserialize_exact(&payload_serialized_buf).map_err(Error::Deserialize)
    }
}
impl AsRef<[u8; KEY_LEN]> for AEADKey {
    fn as_ref(&self) -> &[u8; KEY_LEN] {
        &self.0
    }
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K0Ikm<'a> {
    g_xs: &'a SharedSecret,
}

const SESSION_KEY_INFO: &[u8] = b"shared key id";

// id_skCS = KDF(skCS, "shared key id")
fn session_key_id(key: &AEADKey) -> Result<[u8; SESSION_ID_LENGTH], Error> {
    let prk = libcrux_hkdf::extract(
        Algorithm::Sha256,
        [],
        key.tls_serialize().map_err(serialize_error)?,
    )
    .map_err(|_| Error::CryptoError)?;

    Ok(
        libcrux_hkdf::expand(Algorithm::Sha256, prk, SESSION_KEY_INFO, SESSION_ID_LENGTH)
            .map_err(|_| Error::CryptoError)?
            .try_into()
            .map_err(|_| Error::CryptoError)?, // We don't expect this to fail, unless HDKF gave us the wrong output length
    )
}

// skCS = KDF(K2, "shared secret" | tx2)
pub(super) fn derive_session_key(k2: AEADKey, tx2: Transcript) -> Result<SessionKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct SessionKeyInfo<'a> {
        domain_separator: &'static [u8],
        tx2: &'a Transcript,
    }

    const SHARED_KEY_LABEL: &'static [u8] = b"shared key";
    let key = AEADKey::new(
        &k2,
        &SessionKeyInfo {
            domain_separator: SHARED_KEY_LABEL,
            tx2: &tx2,
        },
    )?;
    let identifier = session_key_id(&key)?;
    Ok(SessionKey { key, identifier })
}

// K0 = KDF(g^xs, tx0)
pub(super) fn derive_k0(
    peer_pk: &PublicKey,
    own_pk: &PublicKey,
    own_sk: &PrivateKey,
    ctx: &[u8],
    is_responder: bool,
) -> Result<(Transcript, AEADKey), Error> {
    let tx0 = if is_responder {
        transcript::tx0(ctx, own_pk, peer_pk)?
    } else {
        transcript::tx0(ctx, peer_pk, own_pk)?
    };
    let ikm = K0Ikm {
        g_xs: &SharedSecret::derive(own_sk, peer_pk)?,
    };

    Ok((tx0, AEADKey::new(&ikm, &tx0)?))
}

// K1 = KDF(K0 | g^cs | SS, tx1)
pub(super) fn derive_k1(
    k0: &AEADKey,
    own_longterm_key: &PrivateKey,
    peer_longterm_pk: &PublicKey,
    pq_shared_secret: &Option<[u8; 32]>,
    tx1: &Transcript,
) -> Result<AEADKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K1Ikm<'a, 'b, 'c> {
        k0: &'a AEADKey,
        ecdh_shared_secret: &'b SharedSecret,
        pq_shared_secret: &'c Option<[u8; 32]>,
    }

    let ecdh_shared_secret = SharedSecret::derive(own_longterm_key, peer_longterm_pk)?;

    AEADKey::new(
        &K1Ikm {
            k0,
            ecdh_shared_secret: &ecdh_shared_secret,
            pq_shared_secret,
        },
        &tx1,
    )
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2IkmQuery<'a> {
    k0: &'a AEADKey,
    g_xs: &'a SharedSecret,
    g_xy: &'a SharedSecret,
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2IkmRegistration<'a, 'b> {
    k1: &'a AEADKey,
    g_cy: &'b SharedSecret,
    g_xy: &'b SharedSecret,
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_responder(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_pk: &PublicKey,
    initiator_ephemeral_pk: &PublicKey,
    responder_ephemeral_sk: &PrivateKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &SharedSecret::derive(responder_ephemeral_sk, initiator_longterm_pk)?,
        g_xy: &SharedSecret::derive(responder_ephemeral_sk, initiator_ephemeral_pk)?,
    };

    Ok(AEADKey::new(&responder_ikm, tx2)?)
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_initiator(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_sk: &PrivateKey,
    initiator_ephemeral_sk: &PrivateKey,
    responder_ephemeral_pk: &PublicKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &SharedSecret::derive(initiator_longterm_sk, responder_ephemeral_pk)?,
        g_xy: &SharedSecret::derive(initiator_ephemeral_sk, responder_ephemeral_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_responder(
    k0: &AEADKey,
    initiator_ephemeral_ecdh_pk: &PublicKey,
    responder_ephemeral_ecdh_sk: &PrivateKey,
    responder_longterm_ecdh_sk: &PrivateKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmQuery {
        k0,
        g_xs: &SharedSecret::derive(responder_longterm_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
        g_xy: &SharedSecret::derive(responder_ephemeral_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_initiator(
    k0: &AEADKey,
    responder_ephemeral_ecdh_pk: &PublicKey,
    initiator_ephemeral_ecdh_sk: &PrivateKey,
    responder_longterm_ecdh_pk: &PublicKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let initiator_ikm = K2IkmQuery {
        k0,
        g_xs: &SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_longterm_ecdh_pk)?,
        g_xy: &SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&initiator_ikm, tx2)
}
