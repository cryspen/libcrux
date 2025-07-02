use libcrux_chacha20poly1305::KEY_LEN;
use tls_codec::{SerializeBytes, TlsSerializeBytes, TlsSize};

use super::{
    ecdh::{self, PrivateKey, PublicKey, SharedSecret},
    session::{SessionKey, SESSION_ID_LENGTH},
    transcript::{self, Transcript},
};

#[derive(PartialEq, Debug, TlsSerializeBytes, TlsSize)]
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
}
impl AsRef<[u8; KEY_LEN]> for AEADKey {
    fn as_ref(&self) -> &[u8; KEY_LEN] {
        &self.0
    }
}

#[derive(Debug, TlsSerializeBytes, TlsSize)]
struct K0Ikm {
    g_xs: SharedSecret,
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
    struct SessionKeyInfo {
        domain_separator: Vec<u8>,
        tx2: Transcript,
    }

    let key = AEADKey::new(
        k2,
        &SessionKeyInfo {
            domain_separator: b"shared key".to_vec(),
            tx2: *tx2,
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
            SharedSecret::derive(own_ecdh_sk, ephemeral_ecdh_pk)
        } else {
            SharedSecret::derive(own_ecdh_sk, responder_ecdh_pk)
        },
    };
    (tx0, AEADKey::new(&ikm, &tx0))
}

#[derive(TlsSerializeBytes, TlsSize)]
struct K2Ikm {
    g_xs: SharedSecret,
    g_xy: SharedSecret,
}

// K2 = KDF(g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_responder(
    initiator_ephemeral_ecdh_pk: &PublicKey,
    responder_ephemeral_ecdh_sk: &PrivateKey,
    responder_longterm_ecdh_sk: &PrivateKey,
    tx2: &Transcript,
) -> AEADKey {
    let responder_ikm = K2Ikm {
        g_xs: SharedSecret::derive(responder_longterm_ecdh_sk, initiator_ephemeral_ecdh_pk),
        g_xy: SharedSecret::derive(responder_ephemeral_ecdh_sk, initiator_ephemeral_ecdh_pk),
    };

    AEADKey::new(&responder_ikm, tx2)
}

// K2 = KDF(g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_initiator(
    responder_ephemeral_ecdh_pk: &PublicKey,
    initiator_ephemeral_ecdh_sk: &PrivateKey,
    responder_longterm_ecdh_pk: &PublicKey,
    tx2: &Transcript,
) -> AEADKey {
    let initiator_ikm = K2Ikm {
        g_xs: SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_longterm_ecdh_pk),
        g_xy: SharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_ephemeral_ecdh_pk),
    };

    AEADKey::new(&initiator_ikm, tx2)
}
