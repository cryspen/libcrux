use crate::protocol::api::{Error, HandshakeState};

use super::api::{IntoTransport, TransportState};
use super::responder::ResponderRegistrationPayload;
use super::{
    ecdh::{KEMKeyPair, PrivateKey, PublicKey},
    keys::{
        derive_k0, derive_k1, derive_k2_query_initiator, derive_k2_registration_initiator, AEADKey,
    },
    responder::ResponderQueryPayload,
    // session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message,
};
use libcrux_ml_kem::mlkem768::{MlKem768Ciphertext, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{
    DeserializeBytes, SerializeBytes, Size, TlsByteVecU32, TlsDeserialize, TlsDeserializeBytes,
    TlsSerialize, TlsSerializeBytes, TlsSize,
};

pub struct QueryInitiator<'a> {
    responder_longterm_ecdh_pk: &'a PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    initiator_ephemeral_ecdh_pk: PublicKey,
    tx0: Transcript,
    k0: AEADKey,
    outer_aad: &'a [u8],
}

pub struct RegistrationInitiator<'a, T: CryptoRng> {
    responder_longterm_ecdh_pk: &'a PublicKey,
    responder_longterm_pq_pk: Option<&'a MlKem768PublicKey>,
    initiator_longterm_ecdh_sk: &'a PrivateKey,
    initiator_longterm_ecdh_pk: &'a PublicKey,
    initiator_ephemeral_ecdh_sk: PrivateKey,
    initiator_ephemeral_ecdh_pk: PublicKey,
    tx0: Transcript,
    k0: AEADKey,
    tx1: Option<Transcript>,
    k1: Option<AEADKey>,
    inner_aad: &'a [u8],
    outer_aad: &'a [u8],
    registration_response: Option<Vec<u8>>,
    rng: &'a mut T,
}

#[derive(Copy, Clone)]
pub struct ResponderKeyPackage<'keys> {
    pub kem_pk: &'keys PublicKey,
    pub pq_pk: Option<&'keys MlKem768PublicKey>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayload {
    Reserved,
    Query(TlsByteVecU32), // XXX: SerializeBytes is not implemented for VLBytes
    Registration(Message),
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct InitiatorInnerPayload(pub TlsByteVecU32);

impl<'a> QueryInitiator<'a> {
    pub fn new(
        responder_longterm_ecdh_pk: &'a PublicKey,
        ctx: &[u8],
        outer_aad: &'a [u8],
        rng: &mut impl CryptoRng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = initiator_ephemeral_ecdh_sk.to_public();

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        )?;

        Ok(Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_ephemeral_ecdh_pk,
            tx0,
            k0,
            outer_aad,
        })
    }

    pub fn read_response(&self, responder_msg: &Message) -> Result<ResponderQueryPayload, Error> {
        let Self {
            responder_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_ephemeral_ecdh_pk: _,
            tx0,
            k0,
            outer_aad,
        } = self;
        let tx2 = tx2(&tx0, &responder_msg.pk);

        let k2 = derive_k2_query_initiator(
            &self.k0,
            &responder_msg.pk,
            &self.initiator_ephemeral_ecdh_sk,
            self.responder_longterm_ecdh_pk,
            &tx2,
        )?;

        Ok(k2.decrypt_deserialize(
            &responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )?)
    }
}

impl<'a, Rng: CryptoRng> RegistrationInitiator<'a, Rng> {
    pub fn new(
        responder_longterm_ecdh_pk: &'a PublicKey,
        initiator_longterm_ecdh_pk: &'a PublicKey,
        initiator_longterm_ecdh_sk: &'a PrivateKey,
        responder_longterm_pq_pk: Option<&'a MlKem768PublicKey>,
        ctx: &[u8],
        inner_aad: &'a [u8],
        outer_aad: &'a [u8],
        rng: &'a mut Rng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_ecdh_sk = PrivateKey::new(rng);
        let initiator_ephemeral_ecdh_pk = initiator_ephemeral_ecdh_sk.to_public();

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &initiator_ephemeral_ecdh_sk,
            ctx,
            false,
        )?;

        Ok(Self {
            responder_longterm_ecdh_pk,
            initiator_longterm_ecdh_pk,
            initiator_longterm_ecdh_sk,
            responder_longterm_pq_pk,
            initiator_ephemeral_ecdh_sk,
            initiator_ephemeral_ecdh_pk,
            tx0,
            k0,
            tx1: None,
            k1: None,
            inner_aad,
            outer_aad,
            rng,
            registration_response: None,
        })
    }

    fn build_registration_payload(
        &mut self,
        registration_payload: &[u8],
    ) -> Result<InitiatorOuterPayload, Error> {
        let pq_encaps_pair = self.responder_longterm_pq_pk.map(|pk| {
            let mut randomness = [0u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
            self.rng.fill_bytes(&mut randomness);
            libcrux_ml_kem::mlkem768::encapsulate(pk, randomness)
        });

        let (pq_encapsulation, pq_shared_secret) =
            if let Some((pq_encaps, pq_shared_secret)) = pq_encaps_pair {
                (Some(pq_encaps), Some(pq_shared_secret))
            } else {
                (None, None)
            };

        let tx1 = tx1(
            &self.tx0,
            &self.initiator_longterm_ecdh_pk,
            self.responder_longterm_pq_pk,
            pq_encapsulation.as_ref(),
        );

        let k1 = derive_k1(
            &self.k0,
            &self.initiator_longterm_ecdh_sk,
            &self.responder_longterm_ecdh_pk,
            &pq_shared_secret,
            &tx1,
        )?;

        let inner_payload =
            InitiatorInnerPayload(TlsByteVecU32::new(registration_payload.to_vec()));
        let mut ciphertext = vec![0u8; inner_payload.tls_serialized_len()];
        let mut tag = [0u8; 16];

        k1.serialize_encrypt(&inner_payload, &mut ciphertext, &mut tag, self.inner_aad)?;

        self.tx1 = Some(tx1);
        self.k1 = Some(k1);

        Ok(InitiatorOuterPayload::Registration(Message {
            pk: self.initiator_longterm_ecdh_pk.clone(),
            ciphertext: TlsByteVecU32::new(ciphertext),
            tag,
            aad: TlsByteVecU32::new(self.inner_aad.to_vec()),
            pq_encapsulation,
        }))
    }

    pub fn complete_registration(
        &mut self,
        responder_msg: &Message,
    ) -> Result<&Option<Vec<u8>>, Error> {
        let Some(tx1) = self.tx1 else {
            return Err(Error::OtherError);
        };

        let Some(k1) = &self.k1 else {
            return Err(Error::OtherError);
        };

        let tx2 = tx2(&tx1, &responder_msg.pk);
        let k2 = derive_k2_registration_initiator(
            k1,
            &tx2,
            &self.initiator_longterm_ecdh_sk,
            &self.initiator_ephemeral_ecdh_sk,
            &responder_msg.pk,
        )?;

        let registration_response: ResponderRegistrationPayload = k2.decrypt_deserialize(
            &responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )?;
        self.registration_response = Some(registration_response.0.into_vec());

        Ok(&self.registration_response)
    }
}

impl<'a> HandshakeState for QueryInitiator<'a> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let outer_payload = InitiatorOuterPayload::Query(TlsByteVecU32::new(payload.to_vec()));
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len()];
        let mut tag = [0u8; 16];

        self.k0
            .serialize_encrypt(&outer_payload, &mut ciphertext, &mut tag, self.outer_aad)?;

        let msg = Message {
            pk: self.initiator_ephemeral_ecdh_pk.clone(),
            ciphertext: TlsByteVecU32::new(ciphertext),
            tag,
            aad: TlsByteVecU32::new(self.outer_aad.to_vec()),
            pq_encapsulation: None,
        };

        let msg_buf = msg.tls_serialize().map_err(|e| Error::Serialize(e))?;
        out[..msg_buf.len()].copy_from_slice(&msg_buf);

        Ok(msg_buf.len())
    }

    fn read_message(
        &mut self,
        message: &[u8],
        payload: &mut [u8],
    ) -> Result<(usize, usize), Error> {
        let (msg, remainder) =
            Message::tls_deserialize_bytes(message).map_err(|e| Error::Deserialize(e))?;
        let result = self.read_response(&msg)?;
        payload[0..result.0.len()].copy_from_slice(&result.0.as_slice());

        Ok((message.len() - remainder.len(), result.0.len()))
    }
}

impl<'a, Rng: CryptoRng> HandshakeState for RegistrationInitiator<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let outer_payload = self.build_registration_payload(payload)?;
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len()];
        let mut tag = [0u8; 16];

        self.k0
            .serialize_encrypt(&outer_payload, &mut ciphertext, &mut tag, self.outer_aad)?;

        let msg = Message {
            pk: self.initiator_ephemeral_ecdh_pk.clone(),
            ciphertext: TlsByteVecU32::new(ciphertext),
            tag,
            aad: TlsByteVecU32::new(self.outer_aad.to_vec()),
            pq_encapsulation: None,
        };

        let msg_buf = msg.tls_serialize().map_err(|e| Error::Serialize(e))?;
        out[..msg_buf.len()].copy_from_slice(&msg_buf);

        Ok(msg_buf.len())
    }

    fn read_message(
        &mut self,
        message: &[u8],
        payload: &mut [u8],
    ) -> Result<(usize, usize), Error> {
        let (msg, remainder) =
            Message::tls_deserialize_bytes(message).map_err(|e| Error::Deserialize(e))?;
        let result = self.complete_registration(&msg)?;
        let result = result.as_ref().unwrap(); // XXX: Avoid this by doing proper state transition in initiator
        payload[0..result.len()].copy_from_slice(&result.as_slice());

        Ok((message.len() - remainder.len(), result.len()))
    }
}

impl<'a, Rng: CryptoRng> IntoTransport for RegistrationInitiator<'a, Rng> {
    fn into_transport_mode(self) -> TransportState {
        todo!()
    }
}
