use std::io::Cursor;

use rand::CryptoRng;
use tls_codec::{Deserialize, Serialize, Size, VLByteSlice};

use crate::{
    aead::AEADKey,
    handshake::{
        ciphersuite::InitiatorX25519ChachaPolyHkdfSha256,
        derive_k0,
        dhkem::{DHKeyPair, DHPrivateKey, DHPublicKey, DHSharedSecret},
        responder::ResponderQueryPayload,
        transcript::{tx2, Transcript},
        write_output, HandshakeError as Error, HandshakeMessage, HandshakeMessageOut, K2IkmQuery,
    },
    traits::Channel,
};

use super::InitiatorOuterPayloadOut;

pub struct QueryInitiator<'a> {
    responder_longterm_ecdh_pk: &'a DHPublicKey,
    initiator_ephemeral_keys: DHKeyPair,
    tx0: Transcript,
    k0: AEADKey,
    outer_aad: &'a [u8],
}

// K2 = KDF(K0 | g^xs | g^xy, tx2)
fn derive_k2_query_initiator(
    k0: &AEADKey,
    responder_ephemeral_ecdh_pk: &DHPublicKey,
    initiator_ephemeral_ecdh_sk: &DHPrivateKey,
    responder_longterm_ecdh_pk: &DHPublicKey,
    tx2: &Transcript,
) -> Result<AEADKey, Error> {
    let initiator_ikm = K2IkmQuery {
        k0,
        g_xs: &DHSharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_longterm_ecdh_pk)?,
        g_xy: &DHSharedSecret::derive(initiator_ephemeral_ecdh_sk, responder_ephemeral_ecdh_pk)?,
    };

    AEADKey::new(&initiator_ikm, tx2).map_err(|e| e.into())
}

impl<'a> QueryInitiator<'a> {
    /// Create a new [`QueryInitiator`].
    pub(crate) fn new(
        responder_longterm_ecdh_pk: &'a DHPublicKey,
        ctx: &[u8],
        outer_aad: &'a [u8],
        mut rng: impl CryptoRng,
    ) -> Result<Self, Error> {
        let initiator_ephemeral_keys = DHKeyPair::new(&mut rng);

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

    fn read_response(
        &self,
        responder_msg: &HandshakeMessage<InitiatorX25519ChachaPolyHkdfSha256>,
    ) -> Result<ResponderQueryPayload, Error> {
        let tx2 = tx2(&self.tx0, &responder_msg.pk)?;

        let mut k2 = derive_k2_query_initiator(
            &self.k0,
            &responder_msg.pk,
            &self.initiator_ephemeral_keys.sk,
            self.responder_longterm_ecdh_pk,
            &tx2,
        )?;

        k2.decrypt_deserialize::<ResponderQueryPayload>(
            responder_msg.ciphertext.as_slice(),
            &responder_msg.tag,
            responder_msg.aad.as_slice(),
        )
        .map_err(|e| e.into())
    }
}

impl<'a> Channel<Error> for QueryInitiator<'a> {
    fn write_message(&mut self, payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
        let outer_payload = InitiatorOuterPayloadOut::<InitiatorX25519ChachaPolyHkdfSha256>::Query(VLByteSlice(payload));
        let (ciphertext, tag) = self.k0.serialize_encrypt(&outer_payload, self.outer_aad)?;

        let msg = HandshakeMessageOut::<InitiatorX25519ChachaPolyHkdfSha256> {
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
        let msg = HandshakeMessage::<InitiatorX25519ChachaPolyHkdfSha256>::tls_deserialize(
            &mut Cursor::new(message_bytes),
        )
        .map_err(Error::Deserialize)?;

        let result = self.read_response(&msg)?;
        let out_bytes_written = write_output(result.0.as_slice(), out)?;

        Ok((msg.tls_serialized_len(), out_bytes_written))
    }
}
