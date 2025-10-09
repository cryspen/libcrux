use libcrux_ml_kem::mlkem768::MlKem768KeyPair;
#[cfg(feature = "classic-mceliece")]
use libcrux_psq::classic_mceliece::KeyPair;

use libcrux_psq::{
    handshake::{
        builders::{CiphersuiteBuilder, PrincipalBuilder},
        ciphersuites::CiphersuiteName,
        types::DHKeyPair,
    },
    Channel,
};
use rand::rngs::ThreadRng;

struct CommonSetup {
    pub rng: ThreadRng,
    pub responder_mlkem_keys: MlKem768KeyPair,
    #[cfg(feature = "classic-mceliece")]
    pub responder_cmc_keys: KeyPair,
    pub responder_ecdh_keys: DHKeyPair,
}

impl CommonSetup {
    fn new() -> Self {
        let mut rng = rand::rng();
        let responder_mlkem_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);
        #[cfg(feature = "classic-mceliece")]
        let responder_cmc_keys =
            libcrux_psq::classic_mceliece::KeyPair::generate_key_pair(&mut rng);

        let responder_ecdh_keys = DHKeyPair::new(&mut rng);

        CommonSetup {
            rng,
            responder_mlkem_keys,
            #[cfg(feature = "classic-mceliece")]
            responder_cmc_keys,
            responder_ecdh_keys,
        }
    }
}

fn query(responder_ciphersuite_id: CiphersuiteName) {
    let mut setup = CommonSetup::new();
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // Setup initiator
    let mut initiator = PrincipalBuilder::new(&mut setup.rng)
        .outer_aad(aad_initiator)
        .context(ctx)
        .build_query_initiator(&setup.responder_ecdh_keys.pk)
        .unwrap();

    // Setup responder
    #[allow(unused_mut)] // we need it mutable for the CMC case
    let mut responder_cbuilder = CiphersuiteBuilder::new(responder_ciphersuite_id)
        .longterm_ecdh_keys(&setup.responder_ecdh_keys)
        .longterm_mlkem_encapsulation_key(setup.responder_mlkem_keys.public_key())
        .longterm_mlkem_decapsulation_key(setup.responder_mlkem_keys.private_key());

    #[cfg(feature = "classic-mceliece")]
    {
        responder_cbuilder = responder_cbuilder
            .longterm_cmc_encapsulation_key(&setup.responder_cmc_keys.pk)
            .longterm_cmc_decapsulation_key(&setup.responder_cmc_keys.sk);
    }
    let responder_ciphersuite = responder_cbuilder.build_responder_ciphersuite().unwrap();

    let mut responder = PrincipalBuilder::new(&mut setup.rng)
        .context(ctx)
        .outer_aad(aad_responder)
        .recent_keys_upper_bound(30)
        .build_responder(responder_ciphersuite)
        .unwrap();

    // Send first message
    let query_payload_initiator = b"Query_init";
    let len_i = initiator
        .write_message(query_payload_initiator, &mut msg_channel)
        .unwrap();

    // Read first message
    let (len_r_deserialized, len_r_payload) = responder
        .read_message(&msg_channel, &mut payload_buf_responder)
        .unwrap();

    // We read the same amount of data.
    assert_eq!(len_r_deserialized, len_i);
    assert_eq!(len_r_payload, b"Query init".len());
    assert_eq!(
        &payload_buf_responder[0..len_r_payload],
        query_payload_initiator
    );

    // Respond
    let query_payload_responder = b"Query_respond";
    let len_r = responder
        .write_message(query_payload_responder, &mut msg_channel)
        .unwrap();

    // Finalize on query initiator
    let (len_i_deserialized, len_i_payload) = initiator
        .read_message(&msg_channel, &mut payload_buf_initiator)
        .unwrap();

    // We read the same amount of data.
    assert_eq!(len_r, len_i_deserialized);
    assert_eq!(query_payload_responder.len(), len_i_payload);
    assert_eq!(
        &payload_buf_initiator[0..len_i_payload],
        query_payload_responder
    );
}

#[test]
fn compatibility_query() {
    query(CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256);
    query(CiphersuiteName::X25519_MLKEM768_CHACHA20POLY1305_HKDFSHA256);
    #[cfg(feature = "classic-mceliece")]
    query(CiphersuiteName::X25519_CLASSICMCELIECE_CHACHA20POLY1305_HKDFSHA256);
}
