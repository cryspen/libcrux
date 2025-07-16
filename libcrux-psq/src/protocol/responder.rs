use std::io::Write;
use std::{
    collections::HashMap,
    time::{Duration, SystemTime},
};

use libcrux_ml_kem::mlkem768::{decapsulate, MlKem768PrivateKey, MlKem768PublicKey};
use rand::CryptoRng;
use tls_codec::{
    DeserializeBytes, SerializeBytes, Size, TlsByteVecU32, TlsDeserializeBytes, TlsSerializeBytes,
    TlsSize,
};

use crate::protocol::api::{Error, HandshakeState};

use super::api::{IntoTransport, TransportState};
use super::{
    ecdh::{KEMKeyPair, PrivateKey, PublicKey},
    initiator::{InitiatorInnerPayload, InitiatorOuterPayload},
    keys::{
        derive_k0, derive_k1, derive_k2_query_responder, derive_k2_registration_responder, AEADKey,
    },
    session::SessionState,
    transcript::{tx1, tx2, Transcript},
    Message, TTL_THRESHOLD,
};

pub(crate) enum ResponderState<'a, T: CryptoRng> {
    Initial {
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        longterm_pq_pk: &'a MlKem768PublicKey,
        longterm_pq_sk: &'a MlKem768PrivateKey,
        context: &'a [u8],
        aad: &'a [u8],
        rng: &'a mut T,
    },
    QueryReceived {
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        longterm_pq_pk: &'a MlKem768PublicKey,
        longterm_pq_sk: &'a MlKem768PrivateKey,
        context: &'a [u8],
        aad: &'a [u8],
        rng: &'a mut T,
        tx0: Transcript,
        k0: AEADKey,
        initiator_ephemeral_ecdh_pk: PublicKey,
        initiator_query_payload: Vec<u8>,
    },
    RegistrationReceived {
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        longterm_pq_pk: &'a MlKem768PublicKey,
        longterm_pq_sk: &'a MlKem768PrivateKey,
        context: &'a [u8],
        aad: &'a [u8],
        rng: &'a mut T,
        tx0: Transcript,
        k0: AEADKey,
        initiator_ephemeral_ecdh_pk: PublicKey,
        initiator_inner_message: Message,
    },
    RegistrationProcessed {
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        longterm_pq_pk: &'a MlKem768PublicKey,
        longterm_pq_sk: &'a MlKem768PrivateKey,
        context: &'a [u8],
        aad: &'a [u8],
        rng: &'a mut T,
        tx0: Transcript,
        k0: AEADKey,
        tx1: Transcript,
        k1: AEADKey,
        initiator_ephemeral_ecdh_pk: PublicKey,
        initiator_longterm_ecdh_pk: PublicKey,
        initiator_registration_payload: Vec<u8>,
    },
    RegistrationDone {},
}

pub struct Responder<'a, T: CryptoRng> {
    pub(crate) state: ResponderState<'a, T>,
}

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize, Default)]
pub struct ResponderQueryPayload(pub TlsByteVecU32);

#[derive(TlsSerializeBytes, TlsDeserializeBytes, TlsSize)]
pub struct ResponderRegistrationPayload(pub TlsByteVecU32);

impl<'a, Rng: CryptoRng> Responder<'a, Rng> {
    pub fn new(
        longterm_ecdh_pk: &'a PublicKey,
        longterm_ecdh_sk: &'a PrivateKey,
        longterm_pq_pk: &'a MlKem768PublicKey,
        longterm_pq_sk: &'a MlKem768PrivateKey,
        context: &'a [u8],
        aad: &'a [u8],
        rng: &'a mut Rng,
    ) -> Self {
        Self {
            state: ResponderState::Initial {
                longterm_ecdh_pk,
                longterm_ecdh_sk,
                longterm_pq_pk,
                longterm_pq_sk,
                context,
                aad,
                rng,
            },
        }
    }

    fn respond_query_self(mut self, payload: &[u8]) -> Result<Message, Error> {
        match self.state {
            ResponderState::QueryReceived {
                longterm_ecdh_pk,
                longterm_ecdh_sk,
                longterm_pq_pk,
                longterm_pq_sk,
                context,
                aad,
                rng,
                tx0,
                k0,
                initiator_ephemeral_ecdh_pk,
                initiator_query_payload,
            } => {
                let responder_ephemeral_ecdh_sk = PrivateKey::new(rng);
                let responder_ephemeral_ecdh_pk = responder_ephemeral_ecdh_sk.to_public();

                let tx2 = tx2(&tx0, &responder_ephemeral_ecdh_pk);
                let k2 = derive_k2_query_responder(
                    &k0,
                    &initiator_ephemeral_ecdh_pk,
                    &responder_ephemeral_ecdh_sk,
                    longterm_ecdh_sk,
                    &tx2,
                )?;

                let outer_payload = ResponderQueryPayload(TlsByteVecU32::new(payload.to_vec()));
                let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len()];
                let mut tag = [0u8; 16];

                // XXX: Don't copy `payload`
                k2.serialize_encrypt(&outer_payload, &mut ciphertext, &mut tag, aad)?;

                // Reset to initial state
                self.state = ResponderState::Initial {
                    longterm_ecdh_pk,
                    longterm_ecdh_sk,
                    longterm_pq_pk,
                    longterm_pq_sk,
                    context,
                    aad,
                    rng,
                };

                Ok(Message {
                    pk: responder_ephemeral_ecdh_pk,
                    ciphertext: TlsByteVecU32::new(ciphertext),
                    tag,
                    aad: TlsByteVecU32::new(aad.to_vec()),
                    pq_encapsulation: None,
                })
            }
            _ => Err(Error::ResponderState),
        }
    }

    pub fn respond_registration(&mut self, payload: &[u8]) -> Result<Message, Error> {
        let ResponderState::RegistrationProcessed {
            ref longterm_ecdh_pk,
            ref longterm_ecdh_sk,
            ref longterm_pq_pk,
            ref longterm_pq_sk,
            ref context,
            ref aad,
            ref rng,
            ref tx0,
            ref k0,
            ref tx1,
            ref k1,
            ref initiator_ephemeral_ecdh_pk,
            ref initiator_longterm_ecdh_pk,
            ref initiator_registration_payload,
        } = self.state
        else {
            return Err(Error::ResponderState);
        };

        let responder_ephemeral_ecdh_sk = PrivateKey::new(*rng);
        let responder_ephemeral_ecdh_pk = responder_ephemeral_ecdh_sk.to_public();

        let tx2 = tx2(&tx1, &responder_ephemeral_ecdh_pk);
        let k2 = derive_k2_registration_responder(
            &k1,
            &tx2,
            &initiator_longterm_ecdh_pk,
            &initiator_ephemeral_ecdh_pk,
            &responder_ephemeral_ecdh_sk,
        )?;

        let outer_payload = ResponderRegistrationPayload(TlsByteVecU32::new(payload.to_vec()));
        let mut ciphertext = vec![0u8; outer_payload.tls_serialized_len()];
        let mut tag = [0u8; 16];

        k2.serialize_encrypt(&outer_payload, &mut ciphertext, &mut tag, aad)?;

        self.state = ResponderState::RegistrationDone {};

        Ok(Message {
            pk: responder_ephemeral_ecdh_pk,
            ciphertext: TlsByteVecU32::new(ciphertext),
            tag,
            aad: TlsByteVecU32::new(aad.to_vec()),
            pq_encapsulation: None,
        })
    }

    pub fn decrypt_inner(&self) -> Result<(), Error> {
        let ResponderState::RegistrationReceived {
            longterm_ecdh_pk,
            longterm_ecdh_sk,
            longterm_pq_pk,
            longterm_pq_sk,
            context,
            aad,
            rng,
            tx0,
            k0,
            initiator_ephemeral_ecdh_pk,
            initiator_inner_message,
        } = self.state
        else {
            return Err(Error::ResponderState);
        };

        let pq_shared_secret = initiator_inner_message
            .pq_encapsulation
            .as_ref()
            .map(|enc| decapsulate(longterm_pq_sk, enc));
        let responder_pq_pk_opt = initiator_inner_message
            .pq_encapsulation
            .as_ref()
            .map(|_| longterm_pq_pk);

        let tx1 = tx1(
            &tx0,
            &initiator_inner_message.pk,
            responder_pq_pk_opt,
            initiator_inner_message.pq_encapsulation.as_ref(),
        );

        let k1 = derive_k1(
            &k0,
            &longterm_ecdh_sk,
            &initiator_inner_message.pk,
            &pq_shared_secret,
            &tx1,
        )?;

        let inner_payload: InitiatorInnerPayload = k1.decrypt_deserialize(
            initiator_inner_message.ciphertext.as_slice(),
            &initiator_inner_message.tag,
            initiator_inner_message.aad.as_slice(),
        )?;

        self.state = ResponderState::RegistrationProcessed {
            longterm_ecdh_pk,
            longterm_ecdh_sk,
            longterm_pq_pk,
            longterm_pq_sk,
            context,
            aad,
            rng,
            tx0,
            k0,
            tx1,
            k1,
            initiator_registration_payload: inner_payload.0.into_vec(),
            initiator_ephemeral_ecdh_pk,
            initiator_longterm_ecdh_pk: initiator_inner_message.pk,
        };

        Ok(())
    }

    fn decrypt_outer_msg(&mut self, initiator_msg: Message) -> Result<(), Error> {
        let ResponderState::Initial {
            longterm_ecdh_pk,
            longterm_ecdh_sk,
            longterm_pq_pk,
            longterm_pq_sk,
            context,
            aad,
            rng,
        } = self.state
        else {
            return Err(Error::ResponderState);
        };

        let (tx0, k0) = derive_k0(
            &initiator_msg.pk,
            longterm_ecdh_pk,
            longterm_ecdh_sk,
            context,
            true,
        )?;

        let initiator_payload: InitiatorOuterPayload = k0.decrypt_deserialize(
            &initiator_msg.ciphertext.as_slice(),
            &initiator_msg.tag,
            &initiator_msg.aad.as_slice(),
        )?;

        match initiator_payload {
            InitiatorOuterPayload::Query(tls_byte_vec_u32) => {
                self.state = ResponderState::QueryReceived {
                    longterm_ecdh_pk,
                    longterm_ecdh_sk,
                    longterm_pq_pk,
                    longterm_pq_sk,
                    context,
                    aad,
                    rng,
                    tx0,
                    k0,
                    initiator_ephemeral_ecdh_pk: initiator_msg.pk,
                    initiator_query_payload: tls_byte_vec_u32.into_vec(),
                };
                Ok(())
            }
            InitiatorOuterPayload::Registration(message) => {
                self.state = ResponderState::RegistrationReceived {
                    longterm_ecdh_pk,
                    longterm_ecdh_sk,
                    longterm_pq_pk,
                    longterm_pq_sk,
                    context,
                    aad,
                    rng,
                    tx0,
                    k0,
                    initiator_ephemeral_ecdh_pk: initiator_msg.pk,
                    initiator_inner_message: message,
                };
                Ok(())
            }
            InitiatorOuterPayload::Reserved => panic!(),
        }
    }
}

impl<'a, Rng: CryptoRng> HandshakeState for Responder<'a, Rng> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        match &self.state {
            ResponderState::QueryReceived { .. } => {
                let msg = self.respond_query_self(payload)?;
                let msg_out = msg.tls_serialize().map_err(|e| Error::Serialize(e))?;
                let msg_out_len = msg_out.len();
                if out.len() < msg_out_len {
                    return Err(Error::OutputBufferShort);
                }
                out[0..msg_out_len].copy_from_slice(&msg_out);
                Ok(msg_out_len)
            }
            ResponderState::RegistrationProcessed {
                longterm_ecdh_pk,
                longterm_ecdh_sk,
                longterm_pq_pk,
                longterm_pq_sk,
                context,
                aad,
                rng,
                tx0,
                k0,
                tx1,
                k1,
                initiator_ephemeral_ecdh_pk,
                initiator_registration_payload,
                initiator_longterm_ecdh_pk,
            } => todo!(),
            _ => Ok(0), // If we're in any other state, we don't write anything
        }
    }

    fn read_message(&mut self, message: &[u8], out: &mut [u8]) -> Result<(usize, usize), Error> {
        // If the responder is not in initial state we do nothing.
        if !matches!(self.state, ResponderState::Initial { .. }) {
            return Ok((0, 0));
        };

        // Deserialize the message.
        let (msg, remainder) =
            Message::tls_deserialize_bytes(message).map_err(|e| Error::Deserialize(e))?;

        // Decrypt the message payload.
        self.decrypt_outer_msg(msg)?;

        match self.state {
            ResponderState::QueryReceived {
                initiator_query_payload,
                ..
            } => {
                // If the message payload was a query payload, we can write that out.
                let payload_len = initiator_query_payload.len();
                if out.len() < payload_len {
                    return Err(Error::OutputBufferShort);
                }
                out[..payload_len].copy_from_slice(&initiator_query_payload);
                Ok((message.len() - remainder.len(), payload_len))
            }
            ResponderState::RegistrationReceived { .. } => {
                // If the message payload was a registration payload we have to process the inner message.
                self.decrypt_inner();

                let ResponderState::RegistrationProcessed {
                    initiator_registration_payload,
                    ..
                } = self.state
                else {
                    return Err(Error::ResponderState);
                };

                let payload_len = initiator_registration_payload.len();
                if out.len() < payload_len {
                    return Err(Error::OutputBufferShort);
                }
                out[..payload_len].copy_from_slice(&initiator_registration_payload);
                Ok((message.len() - remainder.len(), payload_len))
            }
            _ => Err(Error::ResponderState),
        }
    }
}

impl<'a, Rng: CryptoRng> IntoTransport for Responder<'a, Rng> {
    fn into_transport_mode(self) -> TransportState {
        match self.state {
            ResponderState::RegistrationDone {} => todo!(),
        }
    }
}
