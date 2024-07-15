use libcrux::aead::Algorithm;
use std::time::Duration;

use rand::{CryptoRng, Rng};

const DH_PSK_CONTEXT: &[u8] = b"DH-PSK";
const DH_PSK_LENGTH: usize = 32;

const AEAD_RESPONDER: &[u8] = b"AEAD-Responder";
const AEAD_INITIATOR: &[u8] = b"AEAD-Initiator";
const AEAD_KEY_NONCE: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305)
    + Algorithm::nonce_size(Algorithm::Chacha20Poly1305);

const AEAD_KEY_LENGTH: usize = Algorithm::key_size(Algorithm::Chacha20Poly1305);

fn bind_ecdh(
    psq_pk: crate::psq::PublicKey,
    dh_pk: libcrux_ecdh::X25519PublicKey,
    dh_sk: libcrux_ecdh::X25519PrivateKey,
    rng: &mut (impl CryptoRng + Rng),
) {
    let sctx = b"";
    let psk_ttl = Duration::from_secs(3600);
    let (ss_q, enc) = psq_pk.send_psk(sctx, psk_ttl, rng).unwrap();
    let ss_dh = libcrux_ecdh::x25519_derive(&dh_pk, &dh_sk).unwrap();

    let mut ikm = Vec::from(ss_q);
    ikm.extend_from_slice(&ss_dh.0);

    let prk = libcrux_hkdf::extract(libcrux_hkdf::Algorithm::Sha256, b"", ikm);

    let psk: [u8; DH_PSK_LENGTH] = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        &prk,
        DH_PSK_CONTEXT,
        DH_PSK_LENGTH,
    )
    .unwrap()
    .try_into()
    .expect("should receive the correct number of bytes from HKDF");

    let initiator_bytes = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        psk,
        AEAD_INITIATOR,
        AEAD_KEY_NONCE,
    )
    .unwrap();
    let (k_initiator, n_initiator) = initiator_bytes.split_at(AEAD_KEY_LENGTH);

    let responder_bytes = libcrux_hkdf::expand(
        libcrux_hkdf::Algorithm::Sha256,
        prk,
        AEAD_RESPONDER,
        AEAD_KEY_NONCE,
    )
    .unwrap();
    let (k_responder, n_responder) = responder_bytes.split_at(AEAD_KEY_LENGTH);

    let msg = b"";
    let k_initiator = libcrux::aead::Key::from_bytes(
        libcrux::aead::Algorithm::Chacha20Poly1305,
        k_initiator.to_vec(),
    )
    .unwrap();
    let k_responder = libcrux::aead::Key::from_bytes(
        libcrux::aead::Algorithm::Chacha20Poly1305,
        k_responder.to_vec(),
    )
    .unwrap();
    let _ = libcrux::aead::encrypt_detached(
        &k_initiator,
        msg,
        libcrux::aead::Iv(n_initiator.try_into().unwrap()),
        b"",
    );
}
