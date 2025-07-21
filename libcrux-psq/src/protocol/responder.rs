use std::{collections::VecDeque, io::Cursor, mem::take};

use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768KeyPair};
use rand::CryptoRng;
use tls_codec::{
    Deserialize, Serialize, Size, TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes,
};

use crate::protocol::MessageOut;

use super::{
    api::{Error, IntoTransport, Protocol, ToTransportState, Transport},
    ecdh::{KEMKeyPair, PrivateKey, PublicKey},
    initiator::InitiatorInnerPayload,
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    transcript::{tx1, tx2, Transcript},
    write_output, Message,
};

#[derive(TlsDeserialize, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayload {
    Query(VLBytes),
    Registration(Message),
}

#[derive(Debug)]
pub(crate) struct RespondQueryState {
    pub(crate) tx0: Transcript,
    pub(crate) k0: AEADKey,
    pub(crate) initiator_ephemeral_ecdh_pk: PublicKey,
}

#[derive(Debug)]
pub(crate) struct RespondRegistrationState {
    pub(crate) tx1: Transcript,
    pub(crate) k1: AEADKey,
    pub(crate) initiator_ephemeral_ecdh_pk: PublicKey,
    pub(crate) initiator_longterm_ecdh_pk: PublicKey,
}

#[derive(Default, Debug)]
pub(crate) enum ResponderState {
    #[default]
    InProgress, // A placeholder while computing the next state
    Initial,
    RespondQuery(Box<RespondQueryState>),
    RespondRegistration(Box<RespondRegistrationState>),
    ToTransport(Box<ToTransportState>),
}

pub struct Responder<'a, Rng: CryptoRng> {
    pub(crate) state: ResponderState,
    recent_keys: VecDeque<PublicKey>,
    recent_keys_upper_bound: usize,
    longterm_ecdh_keys: &'a KEMKeyPair,
    longterm_pq_keys: Option<&'a MlKem768KeyPair>,
    context: &'a [u8],
    aad: &'a [u8],
    rng: Rng,
}

#[derive(TlsDeserialize, TlsSize)]
pub struct ResponderQueryPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub struct ResponderQueryPayloadOut<'a>(VLByteSlice<'a>);

#[derive(TlsDeserialize, TlsSize)]
pub struct ResponderRegistrationPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub struct ResponderRegistrationPayloadOut<'a>(VLByteSlice<'a>);

impl<'a, Rng: CryptoRng> Responder<'a, Rng> {
    pub fn new(
        longterm_ecdh_keys: &'a KEMKeyPair,
        longterm_pq_keys: Option<&'a MlKem768KeyPair>,
        context: &'a [u8],
        aad: &'a [u8],
        recent_keys_upper_bound: usize,
        rng: Rng,
    ) -> Self {
        Self {
            state: ResponderState::Initial {},
            longterm_ecdh_keys,
            longterm_pq_keys,
            context,
            aad,
            rng,
            recent_keys: VecDeque::with_capacity(recent_keys_upper_bound),
            recent_keys_upper_bound,
        }
    }

    fn derive_query_key(
        &self,
        tx0: &Transcript,
        k0: &AEADKey,
        responder_ephemeral_ecdh_pk: &PublicKey,
        responder_ephemeral_ecdh_sk: &PrivateKey,
        initiator_ephemeral_ecdh_pk: &PublicKey,
    ) -> Result<(Transcript, AEADKey), Error> {
        let tx2 = tx2(tx0, responder_ephemeral_ecdh_pk)?;
        let k2 = derive_k2_query_responder(
            k0,
            initiator_ephemeral_ecdh_pk,
            responder_ephemeral_ecdh_sk,
            &self.longterm_ecdh_keys.sk,
            &tx2,
        )?;

        Ok((tx2, k2))
    }

    fn derive_registration_key(
        &self,
        tx1: &Transcript,
        k1: &AEADKey,
        responder_ephemeral_ecdh_pk: &PublicKey,
        responder_ephemeral_ecdh_sk: &PrivateKey,
        initiator_longterm_ecdh_pk: &PublicKey,
        initiator_ephemeral_ecdh_pk: &PublicKey,
    ) -> Result<(Transcript, AEADKey), Error> {
        let tx2 = tx2(tx1, responder_ephemeral_ecdh_pk)?;
        let k2 = derive_k2_registration_responder(
            k1,
            &tx2,
            initiator_longterm_ecdh_pk,
            initiator_ephemeral_ecdh_pk,
            responder_ephemeral_ecdh_sk,
        )?;

        Ok((tx2, k2))
    }

    fn decrypt_outer_message(
        &self,
        initiator_outer_message: &Message,
    ) -> Result<(InitiatorOuterPayload, Transcript, AEADKey), Error> {
        let (tx0, mut k0) = derive_k0(
            &initiator_outer_message.pk,
            &self.longterm_ecdh_keys.pk,
            &self.longterm_ecdh_keys.sk,
            self.context,
            true,
        )?;

        let initiator_payload: InitiatorOuterPayload = k0.decrypt_deserialize(
            initiator_outer_message.ciphertext.as_slice(),
            &initiator_outer_message.tag,
            initiator_outer_message.aad.as_slice(),
        )?;

        Ok((initiator_payload, tx0, k0))
    }

    fn decrypt_inner_message(
        &self,
        tx0: &Transcript,
        k0: &AEADKey,
        initiator_inner_message: &Message,
    ) -> Result<(InitiatorInnerPayload, Transcript, AEADKey), Error> {
        let pq_shared_secret = initiator_inner_message
            .pq_encapsulation
            .as_ref()
            .zip(self.longterm_pq_keys)
            .map(|(enc, longterm_pq_keys)| decapsulate(longterm_pq_keys.private_key(), enc));

        let responder_pq_pk_opt = self.longterm_pq_keys.map(|keys| keys.public_key());

        let tx1 = tx1(
            tx0,
            &initiator_inner_message.pk,
            responder_pq_pk_opt,
            initiator_inner_message.pq_encapsulation.as_ref(),
        )?;

        let mut k1 = derive_k1(
            k0,
            &self.longterm_ecdh_keys.sk,
            &initiator_inner_message.pk,
            &pq_shared_secret,
            &tx1,
        )?;

        let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(
            initiator_inner_message.ciphertext.as_slice(),
            &initiator_inner_message.tag,
            initiator_inner_message.aad.as_slice(),
        )?;

        Ok((inner_payload, tx1, k1))
    }

    fn registration(
        &mut self,
        payload: &[u8],
        out: &mut [u8],
        responder_ephemeral_ecdh_sk: PrivateKey,
        responder_ephemeral_ecdh_pk: PublicKey,
        state: Box<RespondRegistrationState>,
    ) -> Result<usize, Error> {
        let (tx2, mut k2) = self.derive_registration_key(
            &state.tx1,
            &state.k1,
            &responder_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
            &state.initiator_longterm_ecdh_pk,
            &state.initiator_ephemeral_ecdh_pk,
        )?;

        let outer_payload = ResponderRegistrationPayloadOut(VLByteSlice(payload));
        let (ciphertext, tag) = k2.serialize_encrypt(&outer_payload, self.aad)?;

        let out_msg = MessageOut {
            pk: &responder_ephemeral_ecdh_pk,
            ciphertext: VLByteSlice(&ciphertext),
            tag,
            aad: VLByteSlice(self.aad),
            pq_encapsulation: None,
        };

        let out_len = out_msg
            .tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)?;
        self.state = ResponderState::ToTransport(ToTransportState { tx2, k2 }.into());

        Ok(out_len)
    }

    fn query(
        &mut self,
        payload: &[u8],
        out: &mut [u8],
        responder_ephemeral_ecdh_sk: PrivateKey,
        responder_ephemeral_ecdh_pk: PublicKey,
        state: Box<RespondQueryState>,
    ) -> Result<usize, Error> {
        let (_tx2, mut k2) = self.derive_query_key(
            &state.tx0,
            &state.k0,
            &responder_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
            &state.initiator_ephemeral_ecdh_pk,
        )?;

        let outer_payload = ResponderQueryPayloadOut(VLByteSlice(payload));
        let (ciphertext, tag) = k2.serialize_encrypt(&outer_payload, self.aad)?;

        let out_msg = MessageOut {
            pk: &responder_ephemeral_ecdh_pk,
            ciphertext: VLByteSlice(&ciphertext),
            tag,
            aad: VLByteSlice(self.aad),
            pq_encapsulation: None,
        };

        out_msg
            .tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)?;
        self.state = ResponderState::Initial;

        Ok(out_msg.tls_serialized_len())
    }
}

impl<'a, Rng: CryptoRng> Protocol for Responder<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let mut out_bytes_written = 0;
        let responder_ephemeral_ecdh_sk = PrivateKey::new(&mut self.rng);
        let responder_ephemeral_ecdh_pk = responder_ephemeral_ecdh_sk.to_public();

        let state = take(&mut self.state);
        if let ResponderState::RespondQuery(state) = state {
            out_bytes_written = self.query(
                payload,
                out,
                responder_ephemeral_ecdh_sk,
                responder_ephemeral_ecdh_pk,
                state,
            )?;
        } else if let ResponderState::RespondRegistration(state) = state {
            out_bytes_written = self.registration(
                payload,
                out,
                responder_ephemeral_ecdh_sk,
                responder_ephemeral_ecdh_pk,
                state,
            )?;
        }

        Ok(out_bytes_written)
    }

    fn read_message(
        &mut self,
        message_bytes: &[u8],
        out: &mut [u8],
    ) -> Result<(usize, usize), Error> {
        if !matches!(self.state, ResponderState::Initial {}) {
            return Ok((0, 0));
        }

        // Deserialize the outer message.
        let initiator_outer_message = Message::tls_deserialize(&mut Cursor::new(&message_bytes))
            .map_err(Error::Deserialize)?;
        let bytes_deserialized = initiator_outer_message.tls_serialized_len();

        // Check that the ephemeral key was not in the most recent keys.
        if self.recent_keys.contains(&initiator_outer_message.pk) {
            return Ok((0, 0));
        } else {
            if self.recent_keys.len() == self.recent_keys_upper_bound {
                self.recent_keys.pop_back();
            }
            self.recent_keys
                .push_front(initiator_outer_message.pk.clone());
        }

        // Decrypt the outer message payload.
        let (initiator_outer_payload, tx0, k0) =
            self.decrypt_outer_message(&initiator_outer_message)?;

        match initiator_outer_payload {
            InitiatorOuterPayload::Query(initiator_query_payload) => {
                // We're ready to respond to the query message.
                self.state = ResponderState::RespondQuery(
                    RespondQueryState {
                        tx0,
                        k0,
                        initiator_ephemeral_ecdh_pk: initiator_outer_message.pk,
                    }
                    .into(),
                );
                let out_bytes_written = write_output(initiator_query_payload.as_slice(), out)?;
                Ok((bytes_deserialized, out_bytes_written))
            }

            InitiatorOuterPayload::Registration(initiator_inner_message) => {
                // Decrypt the inner message payload.
                let (initiator_inner_payload, tx1, k1) =
                    self.decrypt_inner_message(&tx0, &k0, &initiator_inner_message)?;
                // We're ready to respond to the registration message.
                self.state = ResponderState::RespondRegistration(
                    RespondRegistrationState {
                        tx1,
                        k1,
                        initiator_ephemeral_ecdh_pk: initiator_outer_message.pk,
                        initiator_longterm_ecdh_pk: initiator_inner_message.pk,
                    }
                    .into(),
                );
                let out_bytes_written = write_output(initiator_inner_payload.0.as_slice(), out)?;
                Ok((bytes_deserialized, out_bytes_written))
            }
        }
    }
}

impl<'a, Rng: CryptoRng> IntoTransport for Responder<'a, Rng> {
    fn into_transport_mode(mut self) -> Result<Transport, Error> {
        let ResponderState::ToTransport(state) = take(&mut self.state) else {
            return Err(Error::ResponderState);
        };

        Transport::new(state.tx2, state.k2)
    }

    fn is_handshake_finished(&self) -> bool {
        matches!(self.state, ResponderState::ToTransport { .. })
    }
}
