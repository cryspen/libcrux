use libcrux_psq::protocol::{api::HandshakeState, ecdh::PrivateKey, *};
use rand::RngCore;

#[test]
fn query() {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    let responder_ecdh_sk = PrivateKey::new(&mut rng);
    let responder_ecdh_pk = responder_ecdh_sk.to_public();

    let mut pq_randomness = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    rng.fill_bytes(&mut pq_randomness);
    let responder_pq_keys = libcrux_ml_kem::mlkem768::generate_key_pair(pq_randomness);

    // Setup initiator
    let mut initiator_rng = rand::rng();
    let mut initiator = api::Builder::new(&mut initiator_rng)
        .outer_aad(aad_initiator)
        .context(ctx)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .build_query_initiator()
        .unwrap();

    // Setup responder
    let mut responder_rng = rand::rng();
    let mut responder = api::Builder::new(&mut responder_rng)
        .context(ctx)
        .outer_aad(aad_responder)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .responder_ecdh_sk(&responder_ecdh_sk)
        .responder_pq_sk(responder_pq_keys.private_key())
        .responder_pq_pk(responder_pq_keys.public_key())
        .build_responder()
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

fn registration(pq: bool) {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator_outer = b"Test Data I Outer";
    let aad_initiator_inner = b"Test Data I Inner";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    let mut pq_randomness = [0u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];
    rng.fill_bytes(&mut pq_randomness);
    let responder_pq_keys = libcrux_ml_kem::mlkem768::generate_key_pair(pq_randomness);

    let responder_ecdh_sk = PrivateKey::new(&mut rng);
    let responder_ecdh_pk = responder_ecdh_sk.to_public();

    let initiator_ecdh_sk = PrivateKey::new(&mut rng);
    let initiator_ecdh_pk = initiator_ecdh_sk.to_public();

    // Setup initiator
    let mut initiator_rng = rand::rng();
    let initiator = api::Builder::new(&mut initiator_rng)
        .outer_aad(aad_initiator_outer)
        .inner_aad(aad_initiator_inner)
        .context(ctx)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .initiator_ecdh_sk(&initiator_ecdh_sk)
        .initiator_ecdh_pk(&initiator_ecdh_pk);

    let mut initiator = if pq {
        initiator
            .responder_pq_pk(responder_pq_keys.public_key())
            .build_registration_initiator()
            .unwrap()
    } else {
        initiator.build_registration_initiator().unwrap()
    };

    // Setup responder
    let mut responder_rng = rand::rng();
    let mut responder = api::Builder::new(&mut responder_rng)
        .context(ctx)
        .outer_aad(aad_responder)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .responder_ecdh_sk(&responder_ecdh_sk)
        .responder_pq_sk(responder_pq_keys.private_key())
        .responder_pq_pk(responder_pq_keys.public_key())
        .build_responder()
        .unwrap();

    // Send first message
    let registration_payload_initiator = b"Registration_init";
    let len_i = initiator
        .write_message(registration_payload_initiator, &mut msg_channel)
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
        registration_payload_initiator
    );

    // Respond
    let registration_payload_responder = b"Registration_respond";
    let len_r = responder
        .write_message(registration_payload_responder, &mut msg_channel)
        .unwrap();

    // Finalize on registration initiator
    let (len_i_deserialized, len_i_payload) = initiator
        .read_message(&msg_channel, &mut payload_buf_initiator)
        .unwrap();

    // We read the same amount of data.
    assert_eq!(len_r, len_i_deserialized);
    assert_eq!(registration_payload_responder.len(), len_i_payload);
    assert_eq!(
        &payload_buf_initiator[0..len_i_payload],
        registration_payload_responder
    );
}

#[test]
fn registration_pq() {
    registration(true);
}

#[test]
fn registration_classic() {
    registration(false);
}
