use std::{collections::VecDeque, io::Cursor, mem::take};

use rand::CryptoRng;
use tls_codec::{
    Deserialize, Serialize, Size, TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes,
};

use crate::{
    aead::AEADKey,
    handshake::ciphersuite::{
        responder::ResponderCiphersuite, traits::CiphersuiteBase, CiphersuiteName,
    },
    session::{Session, SessionError},
    traits::{Channel, IntoSession},
};

use super::{
    derive_k0, derive_k1,
    dhkem::{DHPrivateKey, DHPublicKey, DHSharedSecret},
    initiator::InitiatorInnerPayload,
    transcript::{tx1, tx2, Transcript},
    write_output, HandshakeError as Error, HandshakeMessage, HandshakeMessageOut, K2IkmQuery,
    K2IkmRegistration, ToTransportState,
};

#[derive(TlsDeserialize, TlsSize)]
#[repr(u8)]
pub(crate) enum InitiatorOuterPayload {
    Query(VLBytes),
    Registration(HandshakeMessage),
}

#[derive(Debug)]
pub(crate) struct RespondQueryState {
    pub(crate) tx0: Transcript,
    pub(crate) k0: AEADKey,
    pub(crate) initiator_ephemeral_ecdh_pk: DHPublicKey,
}

#[derive(Debug)]
pub(crate) struct RespondRegistrationState {
    pub(crate) tx1: Transcript,
    pub(crate) k1: AEADKey,
    pub(crate) initiator_ephemeral_ecdh_pk: DHPublicKey,
    pub(crate) initiator_longterm_ecdh_pk: DHPublicKey,
    pub(crate) pq: bool,
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
    ciphersuite: ResponderCiphersuite<'a>,
    working_ciphersuite: CiphersuiteName,
    recent_keys: VecDeque<DHPublicKey>,
    recent_keys_upper_bound: usize,
    context: &'a [u8],
    aad: &'a [u8],
    rng: Rng,
    error_on_ciphersuite_mismatch: bool,
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
        ciphersuite: ResponderCiphersuite<'a>,
        context: &'a [u8],
        aad: &'a [u8],
        recent_keys_upper_bound: usize,
        error_on_ciphersuite_mismatch: bool,
        rng: Rng,
    ) -> Self {
        Self {
            state: ResponderState::Initial {},
            ciphersuite,
            working_ciphersuite: CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256,
            context,
            aad,
            rng,
            recent_keys: VecDeque::with_capacity(recent_keys_upper_bound),
            recent_keys_upper_bound,
            error_on_ciphersuite_mismatch,
        }
    }

    fn derive_query_key(
        &self,
        tx0: &Transcript,
        k0: &AEADKey,
        responder_ephemeral_ecdh_pk: &DHPublicKey,
        responder_ephemeral_ecdh_sk: &DHPrivateKey,
        initiator_ephemeral_ecdh_pk: &DHPublicKey,
    ) -> Result<(Transcript, AEADKey), Error> {
        let tx2 = tx2(tx0, responder_ephemeral_ecdh_pk)?;
        let k2 = derive_k2_query_responder(
            k0,
            initiator_ephemeral_ecdh_pk,
            responder_ephemeral_ecdh_sk,
            self.ciphersuite.own_ecdh_decapsulation_key(),
            &tx2,
        )?;

        Ok((tx2, k2))
    }

    fn derive_registration_key(
        &self,
        tx1: &Transcript,
        k1: &AEADKey,
        responder_ephemeral_ecdh_pk: &DHPublicKey,
        responder_ephemeral_ecdh_sk: &DHPrivateKey,
        initiator_longterm_ecdh_pk: &DHPublicKey,
        initiator_ephemeral_ecdh_pk: &DHPublicKey,
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
        initiator_outer_message: &HandshakeMessage,
    ) -> Result<(InitiatorOuterPayload, Transcript, AEADKey), Error> {
        let (tx0, mut k0) = derive_k0(
            &initiator_outer_message.pk,
            self.ciphersuite.own_ecdh_encapsulation_key(),
            self.ciphersuite.own_ecdh_decapsulation_key(),
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
        initiator_inner_message: &HandshakeMessage,
    ) -> Result<(InitiatorInnerPayload, Transcript, AEADKey, bool), Error> {
        // Whether we attempt to do a decapsulation is decided by the working ciphersuite.
        let pq_encapsulation = self
            .working_ciphersuite
            .deserialize_encapsulation(initiator_inner_message.pq_encapsulation.as_ref())?;

        let pq_shared_secret = pq_encapsulation
            .as_ref()
            .and_then(|enc| Some(self.ciphersuite.pq_decapsulate(enc)))
            .transpose()?;

        let tx1 = tx1(
            tx0,
            &initiator_inner_message.pk,
            if pq_encapsulation.is_some() {
                self.ciphersuite.own_pq_encapsulation_key()
            } else {
                None
            },
            initiator_inner_message.pq_encapsulation.as_ref(),
        )?;

        let mut k1 = derive_k1(
            k0,
            self.ciphersuite.own_ecdh_decapsulation_key(),
            &initiator_inner_message.pk,
            pq_shared_secret,
            &tx1,
        )?;

        let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(
            initiator_inner_message.ciphertext.as_slice(),
            &initiator_inner_message.tag,
            initiator_inner_message.aad.as_slice(),
        )?;

        Ok((inner_payload, tx1, k1, pq_encapsulation.is_some()))
    }

    fn registration(
        &mut self,
        payload: &[u8],
        out: &mut [u8],
        responder_ephemeral_ecdh_sk: DHPrivateKey,
        responder_ephemeral_ecdh_pk: DHPublicKey,
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

        let out_msg = HandshakeMessageOut {
            pk: &responder_ephemeral_ecdh_pk,
            ciphertext: VLByteSlice(&ciphertext),
            tag,
            aad: VLByteSlice(self.aad),
            pq_encapsulation: VLByteSlice(&[]),
            ciphersuite: self.working_ciphersuite,
        };

        let out_len = out_msg
            .tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)?;

        self.state = ResponderState::ToTransport(
            ToTransportState {
                tx2,
                k2,
                initiator_ecdh_pk: Some(state.initiator_longterm_ecdh_pk),
                pq: state.pq,
            }
            .into(),
        );

        Ok(out_len)
    }

    fn query(
        &mut self,
        payload: &[u8],
        out: &mut [u8],
        responder_ephemeral_ecdh_sk: DHPrivateKey,
        responder_ephemeral_ecdh_pk: DHPublicKey,
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

        let out_msg = HandshakeMessageOut {
            pk: &responder_ephemeral_ecdh_pk,
            ciphertext: VLByteSlice(&ciphertext),
            tag,
            aad: VLByteSlice(self.aad),
            pq_encapsulation: VLByteSlice(&[]),
            ciphersuite: CiphersuiteName::X25519_NONE_CHACHA20POLY1305_HKDFSHA256,
        };

        out_msg
            .tls_serialize(&mut &mut out[..])
            .map_err(Error::Serialize)?;
        self.state = ResponderState::Initial;

        Ok(out_msg.tls_serialized_len())
    }

    fn ciphersuite_mismatch(&mut self, bytes_deserialized: usize) -> Result<(usize, usize), Error> {
        if self.error_on_ciphersuite_mismatch {
            Err(Error::UnsupportedCiphersuite)
        } else {
            self.state = ResponderState::Initial;
            Ok((bytes_deserialized, 0))
        }
    }
}

impl<'a, Rng: CryptoRng> Channel<Error> for Responder<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let mut out_bytes_written = 0;
        let responder_ephemeral_ecdh_sk = DHPrivateKey::new(&mut self.rng);
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
        if !matches!(self.state, ResponderState::Initial) {
            return Ok((0, 0));
        }

        // Deserialize the outer message.
        let initiator_outer_message =
            HandshakeMessage::tls_deserialize(&mut Cursor::new(&message_bytes))
                .map_err(Error::Deserialize)?;
        let bytes_deserialized = initiator_outer_message.tls_serialized_len();

        // Set the working ciphersuite for this handshake.
        self.working_ciphersuite = if let Some(ciphersuite) = initiator_outer_message
            .ciphersuite
            .coerce_compatible(&self.ciphersuite)
        {
            ciphersuite
        } else {
            return self.ciphersuite_mismatch(bytes_deserialized);
        };

        // Check that the ephemeral key was not in the most recent keys.
        if self.recent_keys.contains(&initiator_outer_message.pk) {
            return Ok((bytes_deserialized, 0));
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
                if initiator_inner_message.ciphersuite != initiator_outer_message.ciphersuite {
                    // The inner and outer ciphersuites must agree.
                    return Err(Error::InvalidMessage);
                }
                // Decrypt the inner message payload.
                match self.decrypt_inner_message(&tx0, &k0, &initiator_inner_message) {
                    Ok((initiator_inner_payload, tx1, k1, pq)) => {
                        // We're ready to respond to the registration message.
                        self.state = ResponderState::RespondRegistration(
                            RespondRegistrationState {
                                tx1,
                                k1,
                                initiator_ephemeral_ecdh_pk: initiator_outer_message.pk,
                                initiator_longterm_ecdh_pk: initiator_inner_message.pk,
                                pq,
                            }
                            .into(),
                        );
                        let out_bytes_written =
                            write_output(initiator_inner_payload.0.as_slice(), out)?;
                        Ok((bytes_deserialized, out_bytes_written))
                    }
                    Err(Error::UnsupportedCiphersuite) => {
                        self.ciphersuite_mismatch(bytes_deserialized)
                    }
                    Err(e) => Err(e),
                }
            }
        }
    }
}

impl<'a, Rng: CryptoRng> IntoSession for Responder<'a, Rng> {
    fn into_session(self) -> Result<Session, SessionError> {
        let ResponderState::ToTransport(mut state) = self.state else {
            return Err(SessionError::IntoSession);
        };

        let Some(initiator_ecdh_pk) = take(&mut state.initiator_ecdh_pk) else {
            return Err(SessionError::IntoSession);
        };

        Session::new(
            state.tx2,
            state.k2,
            &initiator_ecdh_pk,
            self.ciphersuite.own_ecdh_encapsulation_key(),
            if state.pq {
                self.ciphersuite.own_pq_encapsulation_key()
            } else {
                None
            },
            false,
        )
    }

    fn is_handshake_finished(&self) -> bool {
        matches!(self.state, ResponderState::ToTransport { .. })
    }
}

// K2 = KDF(K1 | g^cy | g^xy, tx2)
pub(super) fn derive_k2_registration_responder(
    k1: &AEADKey,
    tx2: &Transcript,
    initiator_longterm_pk: &DHPublicKey,
    initiator_ephemeral_pk: &DHPublicKey,
    responder_ephemeral_sk: &DHPrivateKey,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmRegistration {
        k1,
        g_cy: &DHSharedSecret::derive(responder_ephemeral_sk, initiator_longterm_pk)?,
        g_xy: &DHSharedSecret::derive(responder_ephemeral_sk, initiator_ephemeral_pk)?,
    };

    Ok(AEADKey::new(&responder_ikm, tx2)?)
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
pub(super) fn derive_k2_query_responder(
    k0: &AEADKey,
    initiator_ephemeral_ecdh_pk: &DHPublicKey,
    responder_ephemeral_ecdh_sk: &DHPrivateKey,
    responder_longterm_ecdh_sk: &DHPrivateKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let responder_ikm = K2IkmQuery {
        k0,
        g_xs: &DHSharedSecret::derive(responder_longterm_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
        g_xy: &DHSharedSecret::derive(responder_ephemeral_ecdh_sk, initiator_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&responder_ikm, tx2).map_err(|e| e.into())
}
