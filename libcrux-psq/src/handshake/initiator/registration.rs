use std::{io::Cursor, mem::take};

use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, Size, VLByteSlice};

use crate::{
    aead::AEADKey,
    handshake::{
        ciphersuite::{initiator::InitiatorCiphersuite, traits::CiphersuiteBase},
        derive_k0, derive_k1,
        dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey, DHSharedSecret},
        responder::ResponderRegistrationPayload,
        transcript::{tx1, tx2, Transcript},
        write_output, HandshakeError as Error, HandshakeMessage, HandshakeMessageOut,
        K2IkmRegistration, ToTransportState,
    },
    session::{Session, SessionError},
    traits::{Channel, IntoSession},
};

use super::{InitiatorInnerPayloadOut, InitiatorOuterPayloadOut};

pub struct RegistrationInitiator<'a, Rng: CryptoRng> {
    ciphersuite: InitiatorCiphersuite<'a>,
    inner_aad: &'a [u8],
    outer_aad: &'a [u8],
    rng: Rng,
    state: RegistrationInitiatorState,
}

pub(crate) struct InitialState {
    initiator_ephemeral_keys: DHKeyPair,
    tx0: Transcript,
    k0: AEADKey,
}

pub(crate) struct WaitingState {
    initiator_ephemeral_ecdh_sk: DHPrivateKey,
    tx1: Transcript,
    k1: AEADKey,
}

#[derive(Default)]
pub(crate) enum RegistrationInitiatorState {
    #[default]
    InProgress, // A placeholder while computing the next state
    Initial(Box<InitialState>),
    Waiting(Box<WaitingState>),
    ToTransport(Box<ToTransportState>),
}

impl<'a, Rng: CryptoRng> RegistrationInitiator<'a, Rng> {
    /// Create a new [`RegistrationInitiator`].
    pub(crate) fn new(
        ciphersuite: InitiatorCiphersuite<'a>,
        ctx: &[u8],
        inner_aad: &'a [u8],
        outer_aad: &'a [u8],
        mut rng: Rng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_keys = DHKeyPair::new(&mut rng);

        let tx0 = ciphersuite.tx0(ctx, ciphersuite.peer_ecdh_encapsulation_key())?;
        let k0 = ciphersuite.k0(tx0, ciphersuite.peer_ecdh_encapsulation_key());

        let state = RegistrationInitiatorState::Initial(
            InitialState {
                tx0,
                k0,
                initiator_ephemeral_keys,
            }
            .into(),
        );

        Ok(Self {
            ciphersuite,
            inner_aad,
            outer_aad,
            rng,
            state,
        })
    }
}

impl<'a, Rng: CryptoRng> Channel<Error> for RegistrationInitiator<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let RegistrationInitiatorState::Initial(mut state) = take(&mut self.state) else {
            // If we're not in the initial state, we write nothing
            return Ok(0);
        };

        let (pq_encapsulation, pq_shared_secret) =
            self.ciphersuite.pq_encapsulate(&mut self.rng)?;

        let pq_encapsulation_serialized = pq_encapsulation
            .tls_serialize_detached()
            .map_err(|_e| Error::OutputBufferShort)?;

        let tx1 = self.ciphersuite.tx1()?;
        // let tx1 = tx1(
        //     &state.tx0,
        //     self.ciphersuite.own_ecdh_encapsulation_key(),
        //     self.ciphersuite.peer_pq_encapsulation_key(),
        //     &pq_encapsulation_serialized,
        // )?;

        // let mut k1 = derive_k1(
        //     &state.k0,
        //     self.ciphersuite.own_ecdh_decapsulation_key(),
        //     self.ciphersuite.peer_ecdh_encapsulation_key(),
        //     pq_shared_secret,
        //     &tx1,
        // )?;

        let inner_payload = InitiatorInnerPayloadOut(VLByteSlice(payload));
        let (inner_ciphertext, inner_tag) = k1.serialize_encrypt(&inner_payload, self.inner_aad)?;

        let outer_payload = InitiatorOuterPayloadOut::Registration(HandshakeMessageOut {
            pk: self.ciphersuite.own_ecdh_encapsulation_key(),
            ciphertext: VLByteSlice(&inner_ciphertext),
            tag: inner_tag,
            aad: VLByteSlice(self.inner_aad),
            pq_encapsulation: VLByteSlice(&pq_encapsulation_serialized),
            ciphersuite: self.ciphersuite.name(),
        });
        let (outer_ciphertext, outer_tag) =
            state.k0.serialize_encrypt(&outer_payload, self.outer_aad)?;

        let msg = HandshakeMessageOut {
            pk: &state.initiator_ephemeral_keys.pk,
            ciphertext: VLByteSlice(&outer_ciphertext),
            tag: outer_tag,
            aad: VLByteSlice(self.outer_aad),
            pq_encapsulation: VLByteSlice(&[]),
            ciphersuite: self.ciphersuite.name(),
        };

        let out_bytes_written = msg
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
        let responder_msg = HandshakeMessage::tls_deserialize(&mut Cursor::new(&message_bytes))
            .map_err(Error::Deserialize)?;
        let bytes_deserialized = responder_msg.tls_serialized_len();

        // Derive K2
        let tx2 = self.ciphersuite.tx2()?;
        let k2 = self.ciphersuite.k2()?;
        // let tx2 = tx2(&state.tx1, &responder_msg.pk)?;
        // let mut k2 = derive_k2_registration_initiator(
        //     &state.k1,
        //     &tx2,
        //     self.ciphersuite.own_ecdh_decapsulation_key(),
        //     &state.initiator_ephemeral_ecdh_sk,
        //     &responder_msg.pk,
        // )?;

        // Decrypt Payload
        let registration_response: ResponderRegistrationPayload = k2.decrypt_deserialize(
            responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )?;

        let out_bytes_written = write_output(registration_response.0.as_slice(), out)?;

        self.state = RegistrationInitiatorState::ToTransport(
            ToTransportState {
                tx2,
                k2,
                initiator_ecdh_pk: None,
                pq: self.ciphersuite.is_pq(),
            }
            .into(),
        );

        Ok((bytes_deserialized, out_bytes_written))
    }
}

impl<'a, Rng: CryptoRng> IntoSession for RegistrationInitiator<'a, Rng> {
    fn into_session(self) -> Result<Session, SessionError> {
        let RegistrationInitiatorState::ToTransport(state) = self.state else {
            return Err(SessionError::IntoSession);
        };

        Session::new(
            state.tx2,
            state.k2,
            self.ciphersuite.client_authenticator(),
            self.ciphersuite.peer_ecdh_encapsulation_key(),
            self.ciphersuite.peer_pq_encapsulation_key(),
            true,
        )
    }

    fn is_handshake_finished(&self) -> bool {
        matches!(self.state, RegistrationInitiatorState::ToTransport(_))
    }
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_initiator(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_sk: &DHPrivateKey,
    initiator_ephemeral_sk: &DHPrivateKey,
    responder_ephemeral_pk: &DHPublicKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &DHSharedSecret::derive(initiator_longterm_sk, responder_ephemeral_pk)?,
        g_xy: &DHSharedSecret::derive(initiator_ephemeral_sk, responder_ephemeral_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2).map_err(|e| e.into())
}
