use super::{
    ecdh::{KEMKeyPair, PrivateKey, PublicKey},
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
use tls_codec::{Size, TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

pub struct QueryInitiator<'keys> {
    responder_longterm_ecdh_pk: &'keys PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    tx0: Transcript,
    k0: AEADKey,
}

pub struct RegistrationInitiatorPre<'keys> {
    initiator_ephemeral_ecdh_sk: PrivateKey,
    initiator_longterm_ecdh_keys: &'keys KEMKeyPair,
    responder_longterm_ecdh_pk: &'keys PublicKey,
    responder_pq_pk: Option<&'keys MlKem768PublicKey>,
    tx1: Transcript,
    k1: AEADKey,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayload {
    Query,
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        pq_encaps: Option<MlKem768Ciphertext>,
        ciphertext: Vec<u8>,
        aad: Vec<u8>,
    },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct InitiatorInnerPayload {}

impl<'rkeys> QueryInitiator<'rkeys> {
    pub fn query(
        responder_longterm_ecdh_pk: &'rkeys PublicKey,
        ctx: &[u8],
        aad: &[u8],
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, Message), crate::Error> {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = initiator_ephemeral_ecdh_sk.to_public();

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let outer_payload = InitiatorOuterPayload::Query;
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len() + 16];

        k0.serialize_encrypt(&outer_payload, aad, &mut ciphertext)?;

        Ok((
            Self {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_sk,
                tx0,
                k0,
            },
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext,
                aad: aad.to_vec(),
            },
        ))
    }

    pub fn read_response(self, responder_msg: &Message) -> ResponderQueryPayload {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            tx0,
            k0,
        } = self;
        let tx2 = tx2(&tx0, &responder_msg.ephemeral_ecdh_pk);

        let k2 = derive_k2_query_initiator(
            &k0,
            &responder_msg.ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            responder_longterm_ecdh_pk,
            &tx2,
        );

        k2.decrypt_deserialize(&responder_msg.ciphertext, &responder_msg.aad)
    }
}

impl<'keys> RegistrationInitiatorPre<'keys> {
    pub fn registration_message(
        initiator_longterm_ecdh_keys: &'keys KEMKeyPair,
        responder_pq_pk: Option<&'keys MlKem768PublicKey>,
        responder_longterm_ecdh_pk: &'keys PublicKey,
        ctx: &[u8],
        aad_outer: &[u8],
        aad_inner: &[u8],
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, Message), crate::Error> {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = initiator_ephemeral_ecdh_sk.to_public();

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        let (pq_encaps, tx1, k1, ciphertext_inner) = encrypt_inner_payload(
            initiator_longterm_ecdh_keys,
            responder_pq_pk,
            responder_longterm_ecdh_pk,
            aad_inner,
            rng,
            tx0,
            &k0,
        )?;

        let payload0 = InitiatorOuterPayload::Registration {
            pq_encaps,
            aad: aad_inner.to_vec(),
            ciphertext: ciphertext_inner,
            initiator_longterm_ecdh_pk: initiator_longterm_ecdh_keys.pk.clone(),
        };

        let mut ciphertext_outer = vec![0u8; payload0.tls_serialized_len() + 16];
        k0.serialize_encrypt(&payload0, aad_outer, &mut ciphertext_outer)?;

        Ok((
            Self {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_sk,
                initiator_longterm_ecdh_keys,
                responder_pq_pk,
                tx1,
                k1,
            },
            Message {
                ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk,
                ciphertext: ciphertext_outer,
                aad: aad_outer.to_vec(),
            },
        ))
    }

    pub fn complete_registration(self, responder_msg: &'keys Message) -> SessionState<'keys> {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_longterm_ecdh_keys,
            responder_pq_pk,
            tx1,
            k1,
        } = self;
        let Message {
            ephemeral_ecdh_pk: responder_ephemeral_ecdh_pk,
            ciphertext,
            aad,
        } = responder_msg;
        let tx2 = tx2(&tx1, responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_initiator(
            &k1,
            &tx2,
            &initiator_longterm_ecdh_keys.sk,
            &initiator_ephemeral_ecdh_sk,
            responder_ephemeral_ecdh_pk,
        );

        let payload2 = k2.decrypt_deserialize(ciphertext, aad);
        SessionState::new(
            true,
            &payload2,
            responder_longterm_ecdh_pk,
            &initiator_longterm_ecdh_keys.pk,
            responder_pq_pk,
            &k2,
            &tx2,
        )
    }
}

fn encrypt_inner_payload(
    initiator_longterm_ecdh_keys: &KEMKeyPair,
    responder_pq_pk: Option<&libcrux_ml_kem::MlKemPublicKey<1184>>,
    responder_longterm_ecdh_pk: &PublicKey,
    aad: &[u8],
    rng: &mut impl CryptoRng,
    tx0: Transcript,
    k0: &AEADKey,
) -> Result<
    (
        Option<libcrux_kem::MlKemCiphertext<1088>>,
        Transcript,
        AEADKey,
        Vec<u8>,
    ),
    crate::Error,
> {
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
        &initiator_longterm_ecdh_keys.pk,
        responder_pq_pk,
        pq_encaps.as_ref(),
    );
    let k1 = derive_k1(
        k0,
        &initiator_longterm_ecdh_keys.sk,
        responder_longterm_ecdh_pk,
        &pq_shared_secret,
        &tx1,
    );

    let inner_payload = InitiatorInnerPayload {};
    let mut ciphertext = vec![0u8; inner_payload.tls_serialized_len() + 16];

    k1.serialize_encrypt(&inner_payload, aad, &mut ciphertext)?;
    Ok((pq_encaps, tx1, k1, ciphertext))
}
