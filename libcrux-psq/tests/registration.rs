use libcrux_ml_kem::mlkem768::MlKem768KeyPair;
#[cfg(feature = "classic-mceliece")]
use libcrux_psq::classic_mceliece::KeyPair;
use libcrux_psq::{
    handshake::{
        ciphersuite::{
            CiphersuiteBuilder, CiphersuiteName, DynamicEncapsulationKeyRef, InitiatorCiphersuite,
        },
        dhkem::DHKeyPair,
        *,
    },
    session::Session,
    traits::{Channel, IntoSession},
};

struct CommonSetup {
    pub responder_mlkem_keys: MlKem768KeyPair,
    #[cfg(feature = "classic-mceliece")]
    pub responder_cmc_keys: KeyPair,
    pub responder_ecdh_keys: DHKeyPair,
    pub initiator_ecdh_keys: DHKeyPair,
}

impl CommonSetup {
    fn pq_encapsulation_key(
        &self,
        name: CiphersuiteName,
    ) -> Option<DynamicEncapsulationKeyRef<'_>> {
        match name {
            CiphersuiteName::X25519ChachaPolyHkdfSha256 => None,
            CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256 => Some(
                DynamicEncapsulationKeyRef::MlKem(self.responder_mlkem_keys.public_key()),
            ),
            #[cfg(feature = "classic-mceliece")]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                Some(DynamicEncapsulationKeyRef::CMC(&self.responder_cmc_keys.pk))
            }
            #[cfg(not(feature = "classic-mceliece"))]
            CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256 => {
                panic!("unsupported ciphersuite")
            }
        }
    }

    fn new() -> Self {
        let mut rng = rand::rng();
        let responder_mlkem_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);
        #[cfg(feature = "classic-mceliece")]
        let responder_cmc_keys =
            libcrux_psq::classic_mceliece::KeyPair::generate_key_pair(&mut rng);

        let responder_ecdh_keys = DHKeyPair::new(&mut rng);
        let initiator_ecdh_keys = DHKeyPair::new(&mut rng);

        CommonSetup {
            responder_mlkem_keys,
            #[cfg(feature = "classic-mceliece")]
            responder_cmc_keys,
            responder_ecdh_keys,
            initiator_ecdh_keys,
        }
    }
}

fn registration(
    initiator_ciphersuite_id: CiphersuiteName,
    responder_ciphersuite_id: CiphersuiteName,
) {
    let setup = CommonSetup::new();
    let ctx = b"Test Context";
    let aad_initiator_outer = b"Test Data I Outer";
    let aad_initiator_inner = b"Test Data I Inner";
    let aad_responder = b"Test Data R";

    let mut msg_channel = vec![0u8; 4096];
    let mut payload_buf_responder = vec![0u8; 4096];
    let mut payload_buf_initiator = vec![0u8; 4096];

    // External setup
    // let responder_pq_keys = libcrux_ml_kem::mlkem768::rand::generate_key_pair(&mut rng);

    // let responder_ecdh_keys = DHKeyPair::new(&mut rng);
    // let initiator_ecdh_keys = DHKeyPair::new(&mut rng);

    // Setup initiator
    // We add everything here to construct any ciphersuite.
    #[allow(unused_mut)] // we need it mutable for the CMC case
    let mut initiator_cbuilder = CiphersuiteBuilder::new()
        .longterm_ecdh_keys(&setup.initiator_ecdh_keys)
        .peer_longterm_ecdh_pk(&setup.responder_ecdh_keys.pk)
        .peer_longterm_mlkem_pk(setup.responder_mlkem_keys.public_key());
    // .finish_initiator(CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256)
    // .unwrap();

    #[cfg(feature = "classic-mceliece")]
    {
        initiator_cbuilder = initiator_cbuilder.peer_longterm_cmc_pk(&setup.responder_cmc_keys.pk);
    }
    let initiator_ciphersuite = initiator_cbuilder
        .finish_initiator(initiator_ciphersuite_id)
        .unwrap();

    let mut initiator = builder::BuilderContext::new(rand::rng())
        .outer_aad(aad_initiator_outer)
        .inner_aad(aad_initiator_inner)
        .context(ctx)
        .build_registration_initiator(initiator_ciphersuite)
        .unwrap();

    // Setup responder
    #[allow(unused_mut)] // we need it mutable for the CMC case
    let mut responder_cbuilder = CiphersuiteBuilder::new()
        .longterm_ecdh_keys(&setup.responder_ecdh_keys)
        .longterm_mlkem_encapsulation_key(setup.responder_mlkem_keys.public_key())
        .longterm_mlkem_decapsulation_key(setup.responder_mlkem_keys.private_key());

    #[cfg(feature = "classic-mceliece")]
    {
        responder_cbuilder = responder_cbuilder
            .longterm_cmc_encapsulation_key(&setup.responder_cmc_keys.pk)
            .longterm_cmc_decapsulation_key(&setup.responder_cmc_keys.sk);
    }
    let responder_ciphersuite = responder_cbuilder
        .finish_responder(responder_ciphersuite_id)
        .unwrap();

    let mut responder = builder::BuilderContext::new(rand::rng())
        .context(ctx)
        .outer_aad(aad_responder)
        .recent_keys_upper_bound(30)
        .build_responder(responder_ciphersuite)
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
    let mut i_transport = Session::deserialize::<InitiatorCiphersuite>(
        &session_storage,
        &setup.initiator_ecdh_keys.pk,
        &setup.responder_ecdh_keys.pk,
        setup.pq_encapsulation_key(initiator_ciphersuite_id),
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
fn compatibility_matching_ciphersuites() {
    // Matching ciphersuites work
    registration(
        CiphersuiteName::X25519ChachaPolyHkdfSha256,
        CiphersuiteName::X25519ChachaPolyHkdfSha256,
    );

    registration(
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256,
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256,
    );

    #[cfg(feature = "classic-mceliece")]
    registration(
        CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256,
        CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256,
    );
}

#[test]
fn compatible_ciphersuites_asymmetric_mlkem() {
    registration(
        CiphersuiteName::X25519ChachaPolyHkdfSha256,
        CiphersuiteName::X25519Mlkem768ChachaPolyHkdfSha256,
    );
}
#[test]
#[cfg(feature = "classic-mceliece")]
fn compatible_ciphersuites_asymmetric_cmc() {
    registration(
        CiphersuiteName::X25519ChachaPolyHkdfSha256,
        CiphersuiteName::X25519ClassicMcElieceChachaPolyHkdfSha256,
    );
}

// TODO: Ciphersuite mismatch errors
