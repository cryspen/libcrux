use libcrux_chacha20poly1305::{decrypt, encrypt, KEY_LEN, NONCE_LEN};
use tls_codec::{DeserializeBytes, SerializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    ecdh::{self, PrivateKey, PublicKey, SharedSecret},
    session::{SessionKey, SESSION_ID_LENGTH},
    transcript::{self, Transcript},
};

#[derive(TlsSerializeBytes, TlsSize)]
pub struct AEADKey([u8; KEY_LEN]);

impl AEADKey {
    fn new(ikm: &impl SerializeBytes, info: &impl SerializeBytes) -> AEADKey {
        let prk = libcrux_hkdf::extract(
            libcrux_hkdf::Algorithm::Sha256,
            &[],
            &ikm.tls_serialize().unwrap(),
        )
        .unwrap();
        AEADKey(
            libcrux_hkdf::expand(
                libcrux_hkdf::Algorithm::Sha256,
                prk,
                &info.tls_serialize().unwrap(),
                KEY_LEN,
            )
            .unwrap()
            .try_into()
            .unwrap(),
        )
    }

    pub(crate) fn serialize_encrypt(
        &self,
        payload: &impl SerializeBytes,
        aad: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<(), crate::Error> {
        debug_assert!(ciphertext.len() == payload.tls_serialized_len() + 16);
        let payload_serialized = payload
            .tls_serialize()
            .map_err(|_| crate::Error::Serialization)?;

        let _ = encrypt(
            self.as_ref(),
            &payload_serialized,
            ciphertext,
            aad,
            &[0; NONCE_LEN],
        )
        .expect("Encryption Error");

        Ok(())
    }

    pub(crate) fn decrypt_deserialize<T: DeserializeBytes>(&self, msg: &[u8], aad: &[u8]) -> T {
        let mut payload_serialized = vec![0u8; msg.len() - 16];
        let _ = decrypt(
            self.as_ref(),
            &mut payload_serialized,
            msg,
            aad,
            &[0; NONCE_LEN],
        )
        .unwrap();

        let received_payload = T::tls_deserialize_exact_bytes(&payload_serialized).unwrap();
        received_payload
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

const SESSION_KEY_INFO: &'static [u8] = b"shared key id";

// id_skCS = KDF(skCS, "shared key id")
fn session_key_id(key: &AEADKey) -> [u8; SESSION_ID_LENGTH] {
    let prk = libcrux_hkdf::extract(
        libcrux_hkdf::Algorithm::Sha256,
        &[],
        &key.tls_serialize().unwrap(),
    )
    .unwrap();

    libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        prk,
        SESSION_KEY_INFO,
        SESSION_ID_LENGTH,
    )
    .unwrap()
    .try_into()
    .unwrap()
}

// skCS = KDF(K2, "shared secret" | tx2)
pub(super) fn derive_session_key(k2: &AEADKey, tx2: &Transcript) -> SessionKey {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct SessionKeyInfo<'a> {
        domain_separator: &'static [u8],
        tx2: &'a Transcript,
    }

    let key = AEADKey::new(
        k2,
        &SessionKeyInfo {
            domain_separator: b"shared key",
            tx2,
        },
    );
    let identifier = session_key_id(&key);
    SessionKey { key, identifier }
}

// K0 = KDF(g^xs, tx0)
pub(super) fn derive_k0(
    responder_ecdh_pk: &ecdh::PublicKey,
    ephemeral_ecdh_pk: &ecdh::PublicKey,
    own_ecdh_sk: &ecdh::PrivateKey,
    ctx: &[u8],
    responder: bool,
) -> (Transcript, AEADKey) {
    let tx0 = transcript::tx0(ctx, responder_ecdh_pk, &ephemeral_ecdh_pk);
    let ikm = K0Ikm {
        g_xs: if responder {
            &SharedSecret::derive(own_ecdh_sk, ephemeral_ecdh_pk)
        } else {
            &SharedSecret::derive(own_ecdh_sk, responder_ecdh_pk)
        },
    };
    (tx0, AEADKey::new(&ikm, &tx0))
}

// K1 = KDF(K0 | g^cs | SS, tx1)
pub(super) fn derive_k1(
    k0: &AEADKey,
    own_longterm_key: &PrivateKey,
    peer_longterm_pk: &PublicKey,
    pq_shared_secret: &Option<[u8; 32]>,
    tx1: &Transcript,
) -> AEADKey {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct K1Ikm<'a, 'b, 'c> {
        k0: &'a AEADKey,
        ecdh_shared_secret: &'b SharedSecret,
        pq_shared_secret: &'c Option<[u8; 32]>,
    }

    let ecdh_shared_secret = SharedSecret::derive(own_longterm_key, peer_longterm_pk);

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
) -> AEADKey {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &SharedSecret::derive(responder_ephemeral_sk, initiator_longterm_pk),
        g_xy: &SharedSecret::derive(responder_ephemeral_sk, initiator_ephemeral_pk),
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_initiator(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_sk: &PrivateKey,
    initiator_ephemeral_sk: &PrivateKey,
    responder_ephemeral_pk: &PublicKey,
) -> AEADKey {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &SharedSecret::derive(initiator_longterm_sk, responder_ephemeral_pk),
        g_xy: &SharedSecret::derive(initiator_ephemeral_sk, responder_ephemeral_pk),
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
) -> AEADKey {
    let responder_ikm = K2IkmQuery {
        k0,
        g_xs: &SharedSecret::derive(responder_longterm_ecdh_sk, initiator_ephemeral_ecdh_pk),
        g_xy: &SharedSecret::derive(responder_ephemeral_ecdh_sk, initiator_ephemeral_ecdh_pk),
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
) -> AEADKey {
    let initiator_ikm = K2IkmQuery {
        k0,
        g_xs: &SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_longterm_ecdh_pk),
        g_xy: &SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_ephemeral_ecdh_pk),
    };

    AEADKey::new(&initiator_ikm, tx2)
}
