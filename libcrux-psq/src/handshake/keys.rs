use libcrux_chacha20poly1305::{decrypt_detached, encrypt_detached, KEY_LEN, NONCE_LEN};
use libcrux_hkdf::Algorithm;
use tls_codec::{
    Deserialize, Serialize, SerializeBytes, TlsDeserialize, TlsSerialize, TlsSerializeBytes,
    TlsSize,
};

use crate::handshake::pqkem::PQSharedSecret;

use super::{
    api::{serialize_error, Error, Session},
    dhkem::{DHPrivateKey, DHPublicKey, DHSharedSecret},
    session::{SessionKey, SESSION_ID_LENGTH},
    transcript::{self, Transcript},
};

#[derive(Default, Clone, TlsSerialize, TlsDeserialize, TlsSerializeBytes, TlsSize)]
pub struct AEADKey([u8; KEY_LEN], #[tls_codec(skip)] [u8; NONCE_LEN]);

impl std::fmt::Debug for AEADKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("AEADKey").field(&"***").finish()
    }
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

    fn increment_nonce(&mut self) -> Result<(), Error> {
        if self.1 == [0xff; NONCE_LEN] {
            return Err(Error::CryptoError);
        }
        let mut buf = [0u8; 16];
        buf[16 - NONCE_LEN..].copy_from_slice(self.1.as_slice());
        let mut nonce = u128::from_be_bytes(buf);
        nonce += 1;
        let buf = nonce.to_be_bytes();
        self.1.copy_from_slice(&buf[16 - NONCE_LEN..]);
        Ok(())
    }

    pub(crate) fn encrypt(
        &mut self,
        payload: &[u8],
        aad: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<[u8; 16], crate::handshake::api::Error> {
        let mut tag = [0u8; 16];

        self.increment_nonce()?;

        // XXX: We could do better if we'd have an inplace API here.
        let _ = encrypt_detached(&self.0, payload, ciphertext, &mut tag, aad, &self.1)
            .map_err(|_| Error::CryptoError)?;

        Ok(tag)
    }

    pub(crate) fn serialize_encrypt<T: Serialize>(
        &mut self,
        payload: &T,
        aad: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), crate::handshake::api::Error> {
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
        self.increment_nonce()?;
        let mut plaintext = vec![0u8; ciphertext.len()];

        let _ = decrypt_detached(&self.0, &mut plaintext, ciphertext, tag, aad, &self.1)
            .map_err(|_| Error::CryptoError)?;

        Ok(plaintext)
    }

    pub(crate) fn decrypt_deserialize<T: Deserialize>(
        &mut self,
        ciphertext: &[u8],
        tag: &[u8; 16],
        aad: &[u8],
    ) -> Result<T, crate::handshake::api::Error> {
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
    g_xs: &'a DHSharedSecret,
}

const SESSION_KEY_INFO: &[u8] = b"session key id";
const SESSION_KEY_SALT: &[u8] = b"session key salt";

// id_skCS = KDF(skCS, "shared key id")
fn session_key_id(key: &AEADKey) -> Result<[u8; SESSION_ID_LENGTH], Error> {
    let prk = libcrux_hkdf::extract(
        Algorithm::Sha256,
        SESSION_KEY_SALT,
        SerializeBytes::tls_serialize(&key).map_err(serialize_error)?,
    )
    .map_err(|_| Error::CryptoError)?;

    Ok(
        libcrux_hkdf::expand(Algorithm::Sha256, prk, SESSION_KEY_INFO, SESSION_ID_LENGTH)
            .map_err(|_| Error::CryptoError)?
            .try_into()
            .map_err(|_| Error::CryptoError)?, // We don't expect this to fail, unless HDKF gave us the wrong output length
    )
}

// skCS = KDF(K2, "session secret" | tx2)
pub(super) fn derive_session_key(k2: AEADKey, tx2: Transcript) -> Result<SessionKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct SessionKeyInfo<'a> {
        domain_separator: &'static [u8],
        tx2: &'a Transcript,
    }

    const SESSION_KEY_LABEL: &'static [u8] = b"session key";
    let key = AEADKey::new(
        &k2,
        &SessionKeyInfo {
            domain_separator: SESSION_KEY_LABEL,
            tx2: &tx2,
        },
    )?;
    let identifier = session_key_id(&key)?;
    Ok(SessionKey { key, identifier })
}

const I2R_CHANNEL_KEY_LABEL: &'static [u8] = b"i2r channel key";
const R2I_CHANNEL_KEY_LABEL: &'static [u8] = b"r2i channel key";

// skChanneli2r = KDF(skCS, "i2r channel key" | pk_binder | channel_counter)
// skChannelr2i = KDF(skCS, "r2i channel key" | pk_binder | channel_counter)
fn derive_channel_key<const IS_INITIATOR: bool>(session: &Session) -> Result<AEADKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct ChannelKeyInfo<'a> {
        domain_separator: &'static [u8],
        pk_binder: &'a [u8],
        counter: u64,
    }

    AEADKey::new(
        &session.session_key.key,
        &ChannelKeyInfo {
            domain_separator: if IS_INITIATOR {
                I2R_CHANNEL_KEY_LABEL
            } else {
                R2I_CHANNEL_KEY_LABEL
            },
            pk_binder: session.pk_binder.as_slice(),
            counter: session.channel_counter,
        }
        .tls_serialize()
        .map_err(serialize_error)?,
    )
}

pub(super) fn derive_i2r_channel_key(session: &Session) -> Result<AEADKey, Error> {
    derive_channel_key::<true>(session)
}

pub(super) fn derive_r2i_channel_key(session: &Session) -> Result<AEADKey, Error> {
    derive_channel_key::<false>(session)
}

// K0 = KDF(g^xs, tx0)
pub(super) fn derive_k0(
    peer_pk: &DHPublicKey,
    own_pk: &DHPublicKey,
    own_sk: &DHPrivateKey,
    ctx: &[u8],
    is_responder: bool,
) -> Result<(Transcript, AEADKey), Error> {
    let tx0 = if is_responder {
        transcript::tx0(ctx, own_pk, peer_pk)?
    } else {
        transcript::tx0(ctx, peer_pk, own_pk)?
    };
    let ikm = K0Ikm {
        g_xs: &DHSharedSecret::derive(own_sk, peer_pk)?,
    };

    Ok((tx0, AEADKey::new(&ikm, &tx0)?))
}

// K1 = KDF(K0 | g^cs | SS, tx1)
pub(super) fn derive_k1(
    k0: &AEADKey,
    own_longterm_key: &DHPrivateKey,
    peer_longterm_pk: &DHPublicKey,
    pq_shared_secret: &Option<PQSharedSecret>,
    tx1: &Transcript,
) -> Result<AEADKey, Error> {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K1Ikm<'a, 'b, 'c> {
        k0: &'a AEADKey,
        ecdh_shared_secret: &'b DHSharedSecret,
        pq_shared_secret: &'c Option<PQSharedSecret>,
    }

    let ecdh_shared_secret = DHSharedSecret::derive(own_longterm_key, peer_longterm_pk)?;

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
    g_xs: &'a DHSharedSecret,
    g_xy: &'a DHSharedSecret,
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2IkmRegistration<'a, 'b> {
    k1: &'a AEADKey,
    g_cy: &'b DHSharedSecret,
    g_xy: &'b DHSharedSecret,
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_responder(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_pk: &DHPublicKey,
    initiator_ephemeral_pk: &DHPublicKey,
    responder_ephemeral_sk: &DHPrivateKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &DHSharedSecret::derive(responder_ephemeral_sk, initiator_longterm_pk)?,
        g_xy: &DHSharedSecret::derive(responder_ephemeral_sk, initiator_ephemeral_pk)?,
    };

    Ok(AEADKey::new(&responder_ikm, tx2)?)
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_initiator(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_sk: &DHPrivateKey,
    initiator_ephemeral_sk: &DHPrivateKey,
    responder_ephemeral_pk: &DHPublicKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &DHSharedSecret::derive(initiator_longterm_sk, responder_ephemeral_pk)?,
        g_xy: &DHSharedSecret::derive(initiator_ephemeral_sk, responder_ephemeral_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_responder(
    k0: &AEADKey,
    initiator_ephemeral_ecdh_pk: &DHPublicKey,
    responder_ephemeral_ecdh_sk: &DHPrivateKey,
    responder_longterm_ecdh_sk: &DHPrivateKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmQuery {
        k0,
        g_xs: &DHSharedSecret::derive(responder_longterm_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
        g_xy: &DHSharedSecret::derive(responder_ephemeral_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_initiator(
    k0: &AEADKey,
    responder_ephemeral_ecdh_pk: &DHPublicKey,
    initiator_ephemeral_ecdh_sk: &DHPrivateKey,
    responder_longterm_ecdh_pk: &DHPublicKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let initiator_ikm = K2IkmQuery {
        k0,
        g_xs: &DHSharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_longterm_ecdh_pk)?,
        g_xy: &DHSharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&initiator_ikm, tx2)
}
