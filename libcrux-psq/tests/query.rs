use libcrux_psq::{
    handshake::{builder, dhkem::DHKeyPair, pqkem::PQKeyPair},
    traits::*,
};

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
    let responder_ecdh_keys = DHKeyPair::new(&mut rng);

    let responder_pq_keys = PQKeyPair::new(&mut rng);

    // Setup initiator
    let mut initiator = builder::Builder::new(rand::rng())
        .outer_aad(aad_initiator)
        .context(ctx)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk)
        .build_query_initiator()
        .unwrap();

    // Setup responder
    let mut responder = builder::Builder::new(rand::rng())
        .context(ctx)
        .outer_aad(aad_responder)
        .longterm_ecdh_keys(&responder_ecdh_keys)
        .longterm_pq_keys(&responder_pq_keys)
        .recent_keys_upper_bound(30)
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
