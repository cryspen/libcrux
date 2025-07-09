use crate::Error;

use super::{
    ecdh::{KEMKeyPair, PublicKey},
    keys::{
        derive_k0, derive_k1, derive_k2_query_initiator, derive_k2_registration_initiator, AEADKey,
    },
    responder::ResponderQueryPayload,
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    InitiatorAppContext, Message,
};
use libcrux_ml_kem::mlkem768::MlKem768PublicKey;
use rand::CryptoRng;
use tls_codec::{Size, TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

pub struct QueryInitiator<'keys> {
    responder_keys: ResponderKeyPackage<'keys>,
    initiator_eph_keys: KEMKeyPair,
    tx0: Transcript,
    k0: AEADKey,
}

#[derive(Copy, Clone)]
pub struct ResponderKeyPackage<'keys> {
    pub kem_pk: &'keys PublicKey,
    pub pq_pk: Option<&'keys MlKem768PublicKey>,
}

pub struct RegistrationInitiatorPre<'keys> {
    responder_keys: ResponderKeyPackage<'keys>,
    initiator_keys: &'keys KEMKeyPair,
    initiator_eph_keys: KEMKeyPair,
    tx1: Transcript,
    k1: AEADKey,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayload {
    Query,
    Registration(Box<Message>),
}

impl InitiatorOuterPayload {
    pub fn as_query_msg(self) -> Option<()> {
        if let InitiatorOuterPayload::Query = self {
            Some(())
        } else {
            None
        }
    }

    pub fn as_registration_msg(self) -> Option<Message> {
        if let InitiatorOuterPayload::Registration(msg) = self {
            Some(*msg)
        } else {
            None
        }
    }
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct InitiatorInnerPayload {}

impl<'keys> QueryInitiator<'keys> {
    pub fn query(
        responder_keys: &ResponderKeyPackage<'keys>,
        initiator_context: &InitiatorAppContext,
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, Message), Error> {
        let initiator_eph_keys = KEMKeyPair::new(rng);

        let (tx0, k0) = derive_k0(
            responder_keys.kem_pk,
            &initiator_eph_keys,
            initiator_context.context,
            false,
        )?;

        let outer_payload = InitiatorOuterPayload::Query;
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len() + 16];

        k0.serialize_encrypt(&outer_payload, initiator_context.aad_outer, &mut ciphertext)?;

        Ok((
            Self {
                responder_keys: *responder_keys,
                initiator_eph_keys: initiator_eph_keys.clone(),
                tx0,
                k0,
            },
            Message {
                pk: initiator_eph_keys.pk,
                ciphertext,
                aad: initiator_context.aad_outer.map(|aad| aad.to_vec()),
                pq_encaps: None,
            },
        ))
    }

    pub fn read_response(self, responder_msg: Message) -> Result<ResponderQueryPayload, Error> {
        let tx2 = tx2(&self.tx0, &responder_msg.pk);

        let k2 = derive_k2_query_initiator(
            &self.k0,
            &responder_msg.pk,
            &self.initiator_eph_keys.sk,
            self.responder_keys.kem_pk,
            &tx2,
        )?;

        Ok(k2.decrypt_deserialize(&responder_msg.ciphertext, responder_msg.aad.as_ref()))
    }
}

impl<'keys, 'context> RegistrationInitiatorPre<'keys> {
    pub fn registration_message(
        initiator_keys: &'keys KEMKeyPair,
        responder_keys: &ResponderKeyPackage<'keys>,
        initiator_context: &InitiatorAppContext<'context>,
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, Message), Error> {
        let initiator_eph_keys = KEMKeyPair::new(rng);

        let (tx0, k0) = derive_k0(
            responder_keys.kem_pk,
            &initiator_eph_keys,
            initiator_context.context,
            false,
        )?;

        let (outer_payload, tx1, k1) = build_registration_payload(
            initiator_keys,
            responder_keys,
            initiator_context,
            &tx0,
            &k0,
            rng,
        )?;

        let mut outer_ciphertext = vec![0u8; outer_payload.tls_serialized_len() + 16];
        k0.serialize_encrypt(
            &outer_payload,
            initiator_context.aad_outer,
            &mut outer_ciphertext,
        )?;

        Ok((
            Self {
                responder_keys: *responder_keys,
                initiator_keys,
                initiator_eph_keys: initiator_eph_keys.clone(),
                tx1,
                k1,
            },
            Message {
                pk: initiator_eph_keys.pk,
                ciphertext: outer_ciphertext,
                aad: initiator_context.aad_outer.map(|aad| aad.to_vec()),
                pq_encaps: None,
            },
        ))
    }

    pub fn complete_registration(
        self,
        responder_msg: &'keys Message,
    ) -> Result<SessionState<'keys>, Error> {
        let tx2 = tx2(&self.tx1, &responder_msg.pk);
        let k2 = derive_k2_registration_initiator(
            &self.k1,
            &tx2,
            &self.initiator_keys.sk,
            &self.initiator_eph_keys.sk,
            &responder_msg.pk,
        )?;

        let payload2 =
            k2.decrypt_deserialize(&responder_msg.ciphertext, responder_msg.aad.as_ref());
        Ok(SessionState::new(
            true,
            &payload2,
            self.responder_keys.kem_pk,
            &self.initiator_keys.pk,
            self.responder_keys.pq_pk,
            &k2,
            &tx2,
        ))
    }
}

fn build_registration_payload<'context>(
    initiator_keys: &KEMKeyPair,
    responder_keys: &ResponderKeyPackage<'_>,
    initiator_context: &InitiatorAppContext<'context>,
    tx0: &Transcript,
    k0: &AEADKey,
    rng: &mut impl CryptoRng,
) -> Result<(InitiatorOuterPayload, Transcript, AEADKey), Error> {
    let pq_encaps_pair = responder_keys.pq_pk.map(|pk| {
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
        tx0,
        &initiator_keys.pk,
        responder_keys.pq_pk,
        pq_encaps.as_ref(),
    );
    let k1 = derive_k1(
        k0,
        &initiator_keys.sk,
        responder_keys.kem_pk,
        &pq_shared_secret,
        &tx1,
    )?;

    let inner_payload = InitiatorInnerPayload {};
    let mut ciphertext = vec![0u8; inner_payload.tls_serialized_len() + 16];

    k1.serialize_encrypt(&inner_payload, initiator_context.aad_inner, &mut ciphertext)?;

    let payload = InitiatorOuterPayload::Registration(Box::new(Message {
        pq_encaps,
        aad: initiator_context.aad_inner.map(|aad| aad.to_vec()),
        ciphertext,
        pk: initiator_keys.pk.clone(),
    }));

    Ok((payload, tx1, k1))
}
