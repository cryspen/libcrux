use libcrux_psq::{
    handshake::{dhkem::DHKeyPair, *},
    session::Session,
    traits::*,
};

fn registration_ml_kem(pq: bool) {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator_outer = b"Test Data I Outer";
    let aad_initiator_inner = b"Test Data I Inner";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);

    let responder_ecdh_keys = DHKeyPair::new(&mut rng);
    let initiator_ecdh_keys = DHKeyPair::new(&mut rng);

    // Setup initiator
    let mut initiator = builder::Builder::new(rand::rng())
        .outer_aad(aad_initiator_outer)
        .inner_aad(aad_initiator_inner)
        .context(ctx)
        .longterm_ecdh_keys(&initiator_ecdh_keys)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk);

    if pq {
        initiator = initiator.peer_longterm_pq_pk(responder_pq_keys.public_key());
    }

    let mut initiator = initiator.build_registration_initiator().unwrap();

    // Setup responder
    let mut builder = builder::Builder::new(rand::rng())
        .context(ctx)
        .outer_aad(aad_responder)
        .longterm_ecdh_keys(&responder_ecdh_keys)
        .recent_keys_upper_bound(30);
    if pq {
        builder = builder.longterm_pq_keys(&responder_pq_keys);
    }
    let mut responder = builder.build_responder().unwrap();

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
    assert_eq!(len_r_payload, registration_payload_initiator.len());
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

    // Ready for transport mode
    assert!(initiator.is_handshake_finished());
    assert!(responder.is_handshake_finished());

    let i_transport = initiator.into_session().unwrap();
    let mut r_transport = responder.into_session().unwrap();

    // test serialization, deserialization
    let mut session_storage = vec![0u8; 4096];
    i_transport.serialize(&mut session_storage).unwrap();
    let mut i_transport = Session::deserialize(
        &session_storage,
        &initiator_ecdh_keys.pk,
        &responder_ecdh_keys.pk,
        pq.then_some(responder_pq_keys.public_key().into()),
    )
    .unwrap();

    let mut channel_i = i_transport.transport_channel().unwrap();
    let mut channel_r = r_transport.transport_channel().unwrap();

    assert_eq!(channel_i.identifier(), channel_r.identifier());

    let app_data_i = b"Derived session hey".as_slice();
    let app_data_r = b"Derived session ho".as_slice();

    let len_i = channel_i
        .write_message(app_data_i, &mut msg_channel)
        .unwrap();

    let (len_r_deserialized, len_r_payload) = channel_r
        .read_message(&msg_channel, &mut payload_buf_responder)
        .unwrap();

    // We read the same amount of data.
    assert_eq!(len_r_deserialized, len_i);
    assert_eq!(len_r_payload, app_data_i.len());
    assert_eq!(&payload_buf_responder[0..len_r_payload], app_data_i);

    let len_r = channel_r
        .write_message(app_data_r, &mut msg_channel)
        .unwrap();

    let (len_i_deserialized, len_i_payload) = channel_i
        .read_message(&msg_channel, &mut payload_buf_initiator)
        .unwrap();

    assert_eq!(len_r, len_i_deserialized);
    assert_eq!(app_data_r.len(), len_i_payload);
    assert_eq!(&payload_buf_initiator[0..len_i_payload], app_data_r);
}

fn registration_classic_mceliece(pq: bool) {
    let mut rng = rand::rng();
    let ctx = b"Test Context";
    let aad_initiator_outer = b"Test Data I Outer";
    let aad_initiator_inner = b"Test Data I Inner";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    let responder_pq_keys = libcrux_psq::classic_mceliece::KeyPair::generate_key_pair(&mut rng);

    let responder_ecdh_keys = DHKeyPair::new(&mut rng);
    let initiator_ecdh_keys = DHKeyPair::new(&mut rng);

    // Setup initiator
    let mut initiator = builder::Builder::new(rand::rng())
        .outer_aad(aad_initiator_outer)
        .inner_aad(aad_initiator_inner)
        .context(ctx)
        .longterm_ecdh_keys(&initiator_ecdh_keys)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk);

    if pq {
        initiator = initiator.peer_longterm_pq_pk(&responder_pq_keys.pk);
    }

    let mut initiator = initiator.build_registration_initiator().unwrap();

    // Setup responder
    let mut builder = builder::Builder::new(rand::rng())
        .context(ctx)
        .outer_aad(aad_responder)
        .longterm_ecdh_keys(&responder_ecdh_keys)
        .recent_keys_upper_bound(30);
    if pq {
        builder = builder.longterm_pq_keys(&responder_pq_keys);
    }
    let mut responder = builder.build_responder().unwrap();

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
    assert_eq!(len_r_payload, registration_payload_initiator.len());
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

    // Ready for transport mode
    assert!(initiator.is_handshake_finished());
    assert!(responder.is_handshake_finished());

    let i_transport = initiator.into_session().unwrap();
    let mut r_transport = responder.into_session().unwrap();

    // test serialization, deserialization
    let mut session_storage = vec![0u8; 4096];
    i_transport.serialize(&mut session_storage).unwrap();
    let mut i_transport = Session::deserialize(
        &session_storage,
        &initiator_ecdh_keys.pk,
        &responder_ecdh_keys.pk,
        pq.then_some((&responder_pq_keys.pk).into()),
    )
    .unwrap();

    let mut channel_i = i_transport.transport_channel().unwrap();
    let mut channel_r = r_transport.transport_channel().unwrap();

    assert_eq!(channel_i.identifier(), channel_r.identifier());

    let app_data_i = b"Derived session hey".as_slice();
    let app_data_r = b"Derived session ho".as_slice();

    let len_i = channel_i
        .write_message(app_data_i, &mut msg_channel)
        .unwrap();

    let (len_r_deserialized, len_r_payload) = channel_r
        .read_message(&msg_channel, &mut payload_buf_responder)
        .unwrap();

    // We read the same amount of data.
    assert_eq!(len_r_deserialized, len_i);
    assert_eq!(len_r_payload, app_data_i.len());
    assert_eq!(&payload_buf_responder[0..len_r_payload], app_data_i);

    let len_r = channel_r
        .write_message(app_data_r, &mut msg_channel)
        .unwrap();

    let (len_i_deserialized, len_i_payload) = channel_i
        .read_message(&msg_channel, &mut payload_buf_initiator)
        .unwrap();

    assert_eq!(len_r, len_i_deserialized);
    assert_eq!(app_data_r.len(), len_i_payload);
    assert_eq!(&payload_buf_initiator[0..len_i_payload], app_data_r);
}

#[test]
fn registration_pq_ml_kem() {
    registration_ml_kem(true);
}

#[test]
fn registration_classic_ml_kem() {
    registration_ml_kem(false);
}

#[test]
fn registration_classic_cmc() {
    registration_classic_mceliece(false);
}

#[test]
fn registration_pq_cmc() {
    registration_classic_mceliece(true);
}
