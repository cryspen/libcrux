use crate::protocol::api::{Error, HandshakeState};
use crate::Error;
use std::io::Write;

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
use tls_codec::{
    DeserializeBytes, SerializeBytes, TlsDeserializeBytes, TlsSerializeBytes, TlsSize,
};

pub struct QueryInitiator<'a> {
    responder_longterm_ecdh_pk: &'a PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    initiator_ephemeral_ecdh_pk: PublicKey,
    tx0: Transcript,
    k0: AEADKey,
    aad: &'a [u8],
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
    Reserved,
    Query,
    Registration {
        initiator_longterm_ecdh_pk: PublicKey,
        pq_encaps: Option<MlKem768Ciphertext>,
        ciphertext: Vec<u8>,
        aad: Vec<u8>,
    },
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct InitiatorInnerPayload(pub Vec<u8>);

impl<'a> QueryInitiator<'a> {
    pub fn new(
        responder_longterm_ecdh_pk: &'a PublicKey,
        ctx: &[u8],
        aad: &'a [u8],
        rng: &mut impl CryptoRng,
    ) -> Self {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = PublicKey::from(&initiator_ephemeral_ecdh_sk);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        );

        Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_ephemeral_ecdh_pk,
            tx0,
            k0,
            aad,
        }
    }

    pub fn query(
        responder_longterm_ecdh_pk: &'a PublicKey,
        ctx: &[u8],
        aad: &'a [u8],
        rng: &mut impl CryptoRng,
    ) -> Result<(Self, Message), Error> {
        let initiator_eph_keys = KEMKeyPair::new(rng);

        let (tx0, k0) = derive_k0(
            responder_keys.kem_pk,
            &initiator_eph_keys,
            initiator_context.context,
            false,
        )?;

        let outer_payload = InitiatorOuterPayload::Query(query_payload.to_vec());
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len() + 16];

        k0.serialize_encrypt(&outer_payload, initiator_context.aad_outer, &mut ciphertext)?;

        Ok((
            Self {
                responder_longterm_ecdh_pk,
                initiator_ephemeral_ecdh_sk,
                initiator_ephemeral_ecdh_pk: initiator_ephemeral_ecdh_pk.clone(),
                tx0,
                k0,
                aad,
            },
            Message {
                pk: initiator_eph_keys.pk,
                ciphertext,
                aad: initiator_context.aad_outer.map(|aad| aad.to_vec()),
                pq_encaps: None,
            },
        ))
    }

    pub fn read_response(&self, responder_msg: &Message) -> ResponderQueryPayload {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_ephemeral_ecdh_pk: _,
            tx0,
            k0,
            aad: _,
        } = self;
        let tx2 = tx2(&tx0, &responder_msg.ephemeral_ecdh_pk);

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
        registration_payload: &[u8],
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
            registration_payload,
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
    registration_payload: &[u8],
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

    let inner_payload = InitiatorInnerPayload(registration_payload.to_vec());
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

impl<'keys> HandshakeState for QueryInitiator<'keys> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let ciphertext = self
            .k0
            .serialize_encrypt(&InitiatorOuterPayload::Query, self.aad);
        _ = payload;

        let msg = Message {
            // XXX: Message should not own this.
            ephemeral_ecdh_pk: self.initiator_ephemeral_ecdh_pk.clone(),
            ciphertext,
            aad: self.aad.to_vec(), // XXX: Message should not own this.
        };

        // XXX: This should write directly into `out`
        let serialized_msg = msg.tls_serialize().map_err(|e| Error::Serialize(e))?;
        let out_len = serialized_msg.len();
        out[0..out_len].copy_from_slice(&serialized_msg);
        Ok(out_len)
    }

    fn read_message(&mut self, message: &[u8], payload: &mut [u8]) -> Result<usize, Error> {
        let (msg, _remainder) =
            Message::tls_deserialize_bytes(message).map_err(|e| Error::Deserialize(e))?;
        let result = self.read_response(&msg);
        payload[0..result.0.len()].copy_from_slice(&result.0);

        Ok(message.len() - _remainder.len())
    }
}
