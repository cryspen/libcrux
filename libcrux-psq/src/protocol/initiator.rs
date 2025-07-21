use std::{io::Cursor, mem::take};

use libcrux_ml_kem::mlkem768::{self, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{
    Deserialize, Serialize, Size, TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes,
};

use crate::protocol::MessageOut;

use super::{
    api::{Error, HandshakeState, IntoTransport, TransportState},
    ecdh::KEMKeyPair,
    ecdh::{PrivateKey, PublicKey},
    keys::{
        derive_k0, derive_k1, derive_k2_query_initiator, derive_k2_registration_initiator, AEADKey,
    },
    responder::ResponderQueryPayload,
    responder::ResponderRegistrationPayload,
    transcript::{tx1, tx2, Transcript},
    write_output, Message,
};

pub struct QueryInitiator<'a> {
    responder_longterm_ecdh_pk: &'a PublicKey,
    initiator_ephemeral_keys: KEMKeyPair,
    tx0: Transcript,
    k0: AEADKey,
    outer_aad: &'a [u8],
}

pub struct RegistrationInitiator<'a, Rng: CryptoRng> {
    responder_longterm_ecdh_pk: &'a PublicKey,
    responder_longterm_pq_pk: Option<&'a MlKem768PublicKey>,
    initiator_longterm_ecdh_keys: &'a KEMKeyPair,
    inner_aad: &'a [u8],
    outer_aad: &'a [u8],
    rng: Rng,
    state: RegistrationInitiatorState,
}

#[derive(TlsSerialize, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayloadOut<'a> {
    Query(VLByteSlice<'a>),
    Registration(MessageOut<'a>),
}

#[derive(TlsDeserialize, TlsSize)]
pub struct InitiatorInnerPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub struct InitiatorInnerPayloadOut<'a>(pub VLByteSlice<'a>);

pub struct InitialState {
    initiator_ephemeral_keys: KEMKeyPair,
    tx0: Transcript,
    k0: AEADKey,
}

pub struct WaitingState {
    initiator_ephemeral_ecdh_sk: PrivateKey,
    tx1: Transcript,
    k1: AEADKey,
}

pub struct ToTransportState {
    tx2: Transcript,
    k2: AEADKey,
}

#[derive(Default)]
pub enum RegistrationInitiatorState {
    #[default]
    InProgress, // A placeholder while computing the next state
    Initial(Box<InitialState>),
    Waiting(Box<WaitingState>),
    ToTransport(Box<ToTransportState>),
}

impl<'a> QueryInitiator<'a> {
    /// Create a new [`QueryInitiator`].
    pub(crate) fn new(
        responder_longterm_ecdh_pk: &'a PublicKey,
        ctx: &[u8],
        outer_aad: &'a [u8],
        mut rng: impl CryptoRng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_keys = KEMKeyPair::new(&mut rng);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_keys.pk,
            &initiator_ephemeral_keys.sk,
            ctx,
            false,
        )?;

        Ok(Self {
            responder_longterm_ecdh_pk,
            tx0,
            k0,
            outer_aad,
            initiator_ephemeral_keys,
        })
    }

    fn read_response(&self, responder_msg: &Message) -> Result<ResponderQueryPayload, Error> {
        let tx2 = tx2(&self.tx0, &responder_msg.pk)?;

        let k2 = derive_k2_query_initiator(
            &self.k0,
            &responder_msg.pk,
            &self.initiator_ephemeral_keys.sk,
            self.responder_longterm_ecdh_pk,
            &tx2,
        )?;

        k2.decrypt_deserialize(
            responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )
    }
}

impl<'a, Rng: CryptoRng> RegistrationInitiator<'a, Rng> {
    /// Create a new [`RegistrationInitiator`].
    pub(crate) fn new(
        initiator_longterm_ecdh_keys: &'a KEMKeyPair,
        responder_longterm_ecdh_pk: &'a PublicKey,
        responder_longterm_pq_pk: Option<&'a MlKem768PublicKey>,
        ctx: &[u8],
        inner_aad: &'a [u8],
        outer_aad: &'a [u8],
        mut rng: Rng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_keys = KEMKeyPair::new(&mut rng);

        let (tx0, k0) = derive_k0(
            responder_longterm_ecdh_pk,
            &initiator_ephemeral_keys.pk,
            &initiator_ephemeral_keys.sk,
            ctx,
            false,
        )?;

        let state = RegistrationInitiatorState::Initial(
            InitialState {
                tx0,
                k0,
                initiator_ephemeral_keys,
            }
            .into(),
        );

        Ok(Self {
            responder_longterm_ecdh_pk,
            responder_longterm_pq_pk,
            initiator_longterm_ecdh_keys,
            inner_aad,
            outer_aad,
            rng,
            state,
        })
    }
}

impl<'a> HandshakeState for QueryInitiator<'a> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let outer_payload = InitiatorOuterPayloadOut::Query(VLByteSlice(payload));
        let (ciphertext, tag) = self.k0.serialize_encrypt(&outer_payload, self.outer_aad)?;

        let msg = MessageOut {
            pk: &self.initiator_ephemeral_keys.pk,
            ciphertext: VLByteSlice(&ciphertext),
            tag,
            aad: VLByteSlice(self.outer_aad),
            pq_encapsulation: None,
        };

        msg.tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)
    }

    fn read_message(
        &mut self,
        message_bytes: &[u8],
        out: &mut [u8],
    ) -> Result<(usize, usize), Error> {
        let msg = Message::tls_deserialize(&mut Cursor::new(&message_bytes[..]))
            .map_err(Error::Deserialize)?;

        let result = self.read_response(&msg)?;
        let out_bytes_written = write_output(result.0.as_slice(), out)?;

        Ok((msg.tls_serialized_len(), out_bytes_written))
    }

    fn is_initiator(&self) -> bool {
        true
    }
}

impl<'a, Rng: CryptoRng> HandshakeState for RegistrationInitiator<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let out_bytes_written;

        let RegistrationInitiatorState::Initial(state) = take(&mut self.state) else {
            // If we're not in the initial state, we write nothing
            return Ok(0);
        };

        let pq_encaps_pair = self
            .responder_longterm_pq_pk
            .map(|pk| mlkem768::rand::encapsulate(pk, &mut self.rng));

        let (pq_encapsulation, pq_shared_secret) =
            if let Some((pq_encaps, pq_shared_secret)) = pq_encaps_pair {
                (Some(pq_encaps), Some(pq_shared_secret))
            } else {
                (None, None)
            };

        let tx1 = tx1(
            &state.tx0,
            &self.initiator_longterm_ecdh_keys.pk,
            self.responder_longterm_pq_pk,
            pq_encapsulation.as_ref(),
        )?;

        let k1 = derive_k1(
            &state.k0,
            &self.initiator_longterm_ecdh_keys.sk,
            self.responder_longterm_ecdh_pk,
            &pq_shared_secret,
            &tx1,
        )?;

        let inner_payload = InitiatorInnerPayloadOut(VLByteSlice(payload));
        let (inner_ciphertext, inner_tag) = k1.serialize_encrypt(&inner_payload, self.inner_aad)?;

        let outer_payload = InitiatorOuterPayloadOut::Registration(MessageOut {
            pk: &self.initiator_longterm_ecdh_keys.pk,
            ciphertext: VLByteSlice(&inner_ciphertext),
            tag: inner_tag,
            aad: VLByteSlice(self.inner_aad),
            pq_encapsulation: pq_encapsulation.as_ref(),
        });
        let (outer_ciphertext, outer_tag) =
            state.k0.serialize_encrypt(&outer_payload, self.outer_aad)?;

        let msg = MessageOut {
            pk: &state.initiator_ephemeral_keys.pk,
            ciphertext: VLByteSlice(&outer_ciphertext),
            tag: outer_tag,
            aad: VLByteSlice(self.outer_aad),
            pq_encapsulation: None,
        };

        out_bytes_written = msg
            .tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)?;

        self.state = RegistrationInitiatorState::Waiting(
            WaitingState {
                initiator_ephemeral_ecdh_sk: state.initiator_ephemeral_keys.sk,
                tx1,
                k1,
            }
            .into(),
        );

        Ok(out_bytes_written)
    }

    fn read_message(
        &mut self,
        message_bytes: &[u8],
        out: &mut [u8],
    ) -> Result<(usize, usize), Error> {
        let RegistrationInitiatorState::Waiting(state) = take(&mut self.state) else {
            // If we're not in the waiting state, we do nothing.
            return Ok((0, 0));
        };

        // Deserialize the message.
        let responder_msg = Message::tls_deserialize(&mut Cursor::new(&message_bytes))
            .map_err(Error::Deserialize)?;
        let bytes_deserialized = responder_msg.tls_serialized_len();

        // Derive K2
        let tx2 = tx2(&state.tx1, &responder_msg.pk)?;
        let k2 = derive_k2_registration_initiator(
            &state.k1,
            &tx2,
            &self.initiator_longterm_ecdh_keys.sk,
            &state.initiator_ephemeral_ecdh_sk,
            &responder_msg.pk,
        )?;

        // Decrypt Payload
        let registration_response: ResponderRegistrationPayload = k2.decrypt_deserialize(
            responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )?;

        let out_bytes_written = write_output(registration_response.0.as_slice(), out)?;

        self.state = RegistrationInitiatorState::ToTransport(ToTransportState { tx2, k2 }.into());

        Ok((bytes_deserialized, out_bytes_written))
    }

    fn is_initiator(&self) -> bool {
        true
    }
}

impl<'a, Rng: CryptoRng> IntoTransport for RegistrationInitiator<'a, Rng> {
    fn into_transport_mode(self) -> TransportState {
        todo!()
    }

    fn is_handshake_finished(&self) -> bool {
        todo!()
    }
}
