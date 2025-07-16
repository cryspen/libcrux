use libcrux_psq::protocol::{api::HandshakeState, ecdh::PrivateKey, *};

#[test]
fn query() {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    let responder_ecdh_sk = PrivateKey::new(&mut rng);
    let responder_ecdh_pk = responder_ecdh_sk.to_public();

    // Setup initiator
    let mut initiator_rng = rand::rng();
    let mut initiator = api::Builder::new(&mut initiator_rng)
        .aad(aad_initiator)
        .context(ctx)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .build_query_initiator()
        .unwrap();

    // Setup responder
    let mut responder_rng = rand::rng();
    let mut responder = api::Builder::new(&mut responder_rng)
        .context(ctx)
        .responder_ecdh_pk(&responder_ecdh_pk)
        .responder_ecdh_sk(&responder_ecdh_sk)
        .build_query_responder()
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
