use libcrux_psq::protocol::{
    api::HandshakeState,
    ecdh::{PrivateKey, PublicKey},
    *,
};

#[test]
fn query() {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";

    let mut msg_channel = vec![0u8; 4096];

    // External setup
    let responder_ecdh_sk = PrivateKey::new(&mut rng);
    let responder_ecdh_pk = PublicKey::from(&responder_ecdh_sk);

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
    let len_i = initiator.write_message(&[], &mut msg_channel).unwrap();

    // Read first message
    let mut _payload = vec![]; // There's nothing in here
    let len_r = responder.read_message(&msg_channel, &mut _payload).unwrap();

    // We read the same amount of data.
    assert_eq!(len_r, len_i);

    // Respond
    let payload = vec![0x13u8; 32];
    let len_r = responder.write_message(&payload, &mut msg_channel).unwrap();

    // Finalize on query initiator
    let mut responder_payload = vec![0u8; 1024];
    let len_i = initiator
        .read_message(&msg_channel, &mut responder_payload)
        .unwrap();

    // We read the same amount of data.
    // XXX: The len_i is the network bytes, not the payload bytes.
    //      We need to get that from somewhere.
    assert_eq!(len_r, len_i);
    assert_eq!(&responder_payload[0..payload.len()], &payload);
}
