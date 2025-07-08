use super::{
    ecdh::{PrivateKey, PublicKey},
    keys::{
        derive_k0, derive_k1, derive_k2_query_initiator, derive_k2_registration_initiator, AEADKey,
    },
    responder::ResponderQueryPayload,
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message,
};
use libcrux_ml_kem::mlkem768::{MlKem768Ciphertext, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

pub(crate) struct QueryInitiator<'keys> {
    responder_longterm_ecdh_pk: &'keys PublicKey,
    initiator_ephemeral_ecdh_pk: PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    tx0: Transcript,
    k0: AEADKey,
}

pub(crate) struct RegistrationInitiatorPre<'keys> {
    initiator_ephemeral_ecdh_pk: PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    initiator_longterm_ecdh_sk: &'keys PrivateKey,
    initiator_longterm_ecdh_pk: &'keys PublicKey,
    responder_longterm_ecdh_pk: &'keys PublicKey,
    responder_pq_pk: Option<&'keys MlKem768PublicKey>,
    tx1: Transcript,
    k1: AEADKey,
}

pub(crate) struct InitiatorDone<'keys> {
    session_state: SessionState<'keys>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub(crate) enum InitiatorOuterPayload {
    Query,
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        pq_encaps: Option<MlKem768Ciphertext>,
        ciphertext: Vec<u8>,
        aad: Vec<u8>,
    },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub(crate) struct InitiatorInnerPayload {}

impl<'rkeys> QueryInitiator<'rkeys> {
    pub(crate) fn query(
        responder_longterm_ecdh_pk: &'rkeys PublicKey,
        ctx: &[u8],
        aad: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = PublicKey::from(&initiator_ephemeral_ecdh_sk);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let ciphertext = k0.serialize_encrypt(&InitiatorOuterPayload::Query, &aad);

        (
            Self {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk.clone(),
                initiator_ephemeral_ecdh_sk,
                tx0,
                k0,
            },
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext,
                aad: aad.to_vec(),
            },
        )
    }

    pub(crate) fn read_response(self, responder_msg: &Message) -> ResponderQueryPayload {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            tx0,
            k0,
        } = self;
        let tx2 = tx2(&tx0, &responder_msg.ephemeral_ecdh_pk);

        let k2 = derive_k2_query_initiator(
            &responder_msg.ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            &responder_longterm_ecdh_pk,
            &tx2,
        );

        k2.decrypt_deserialize(&responder_msg.ciphertext, &responder_msg.aad)
    }
}

impl<'keys> RegistrationInitiatorPre<'keys> {
    pub(crate) fn registration_message(
        initiator_longterm_ecdh_pk: &'keys PublicKey,
        initiator_longterm_ecdh_sk: &'keys PrivateKey,
        responder_pq_pk: Option<&'keys MlKem768PublicKey>,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        ctx: &[u8],
        aad_outer: &[u8],
        aad_inner: &[u8],
        rng: &mut impl CryptoRng,
    ) -> (Self, Message) {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = PublicKey::from(&initiator_ephemeral_ecdh_sk);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let (pq_encaps, tx1, k1, ciphertext) = encrypt_inner_payload(
            initiator_longterm_ecdh_pk,
            initiator_longterm_ecdh_sk,
            responder_pq_pk,
            responder_longterm_ecdh_pk,
            aad_inner,
            rng,
            tx0,
            &k0,
        );

        let payload0 = InitiatorOuterPayload::Registration {
            pq_encaps,
            aad: aad_outer.to_vec(),
            ciphertext,
            initiator_longterm_ecdh_pk: initiator_longterm_ecdh_pk.clone(),
        };

        let ciphertext = k0.serialize_encrypt(&payload0, &aad_outer);

        (
            Self {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk.clone(),
                initiator_ephemeral_ecdh_sk,
                initiator_longterm_ecdh_sk,
                initiator_longterm_ecdh_pk,
                responder_pq_pk,
                tx1,
                k1,
            },
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext,
                aad: aad_outer.to_vec(),
            },
        )
    }

    pub(crate) fn complete_registration(self, responder_msg: &'keys Message) -> SessionState {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_longterm_ecdh_sk,
            initiator_longterm_ecdh_pk,
            responder_pq_pk,
            tx1,
            k1,
        } = self;

        let tx2 = tx2(&tx1, &responder_msg.ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_initiator(
            &k1,
            &tx2,
            &initiator_longterm_ecdh_sk,
            &initiator_ephemeral_ecdh_sk,
            &responder_msg.ephemeral_ecdh_pk,
        );

        let payload2 = k2.decrypt_deserialize(&responder_msg.ciphertext, &responder_msg.aad);
        SessionState::new(
            &payload2,
            &responder_longterm_ecdh_pk,
            &initiator_longterm_ecdh_pk,
            responder_pq_pk,
            &k2,
            &tx2,
        )
    }
}

fn encrypt_inner_payload(
    initiator_longterm_ecdh_pk: &PublicKey,
    initiator_longterm_ecdh_sk: &PrivateKey,
    responder_pq_pk: Option<&libcrux_ml_kem::MlKemPublicKey<1184>>,
    responder_longterm_ecdh_pk: &PublicKey,
    aad: &[u8],
    rng: &mut impl CryptoRng,
    tx0: Transcript,
    k0: &AEADKey,
) -> (
    Option<libcrux_kem::MlKemCiphertext<1088>>,
    Transcript,
    AEADKey,
    Vec<u8>,
) {
    let pq_encaps_pair = responder_pq_pk.map(|pk| {
        let mut randomness = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
        rng.fill_bytes(&mut randomness);
        libcrux_ml_kem::mlkem768::encapsulate(pk, randomness)
    });

    let (pq_encaps, pq_shared_secret) = if let Some((pq_encaps, pq_shared_secret)) = pq_encaps_pair
    {
        (Some(pq_encaps), Some(pq_shared_secret))
    } else {
        (None, None)
    };

    let tx1 = tx1(
        &tx0,
        &initiator_longterm_ecdh_pk,
        responder_pq_pk,
        pq_encaps.as_ref(),
    );
    let k1 = derive_k1(
        k0,
        &initiator_longterm_ecdh_sk,
        responder_longterm_ecdh_pk,
        &pq_shared_secret,
        &tx0,
    );

    let ciphertext = k1.serialize_encrypt(&InitiatorInnerPayload {}, &aad);
    (pq_encaps, tx1, k1, ciphertext)
}
