use tls_codec::{Serialize, SerializeBytes, TlsSerialize, TlsSerializeBytes, TlsSize};

pub const TX0_DOMAIN_SEP: u8 = 0;
pub const TX1_DOMAIN_SEP: u8 = 1;
pub const TX2_DOMAIN_SEP: u8 = 2;

use super::{dhkem::DHPublicKey, pqkem::PQPublicKey};
use crate::handshake::{pqkem::PQCiphertext, HandshakeError as Error};
use libcrux_sha2::{Digest, SHA256_LENGTH};

/// The initial transcript hash.
#[derive(Debug, Default, Clone, Copy, TlsSerializeBytes, TlsSize)]
pub struct Transcript([u8; SHA256_LENGTH]);

impl Transcript {
    fn new(initial_input: &impl Serialize) -> Result<Self, Error> {
        Self::add_hash::<TX0_DOMAIN_SEP>(None, initial_input)
    }

    fn add_hash<const DOMAIN_SEPARATOR: u8>(
        old_transcript: Option<&Transcript>,
        input: &impl Serialize,
    ) -> Result<Transcript, Error> {
        let mut hasher = libcrux_sha2::Sha256::new();
        hasher.update(&[DOMAIN_SEPARATOR]);
        hasher.update(
            old_transcript
                .tls_serialize()
                .map_err(|e| Error::Serialize(e))?
                .as_slice(),
        );
        hasher.update(
            input
                .tls_serialize_detached()
                .map_err(|e| Error::Serialize(e))?
                .as_slice(),
        );

        let mut digest = [0u8; 32];
        hasher.finish(&mut digest);
        Ok(Transcript(digest))
    }
}

impl AsRef<[u8]> for Transcript {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

// tx0 = hash(0 | ctx | g^s | g^x)
pub(crate) fn tx0(
    context: &[u8],
    responder_pk: &DHPublicKey,
    initiator_pk: &DHPublicKey,
) -> Result<Transcript, Error> {
    #[derive(TlsSerialize, TlsSize)]
    struct Transcript0Inputs<'a, 'b, 'c> {
        context: &'a [u8],
        responder_pk: &'b DHPublicKey,
        initiator_pk: &'c DHPublicKey,
    }

    Transcript::new(&Transcript0Inputs {
        context,
        responder_pk,
        initiator_pk,
    })
}

// tx1 = hash(1 | tx0 | g^c | pkS | encap(pkS, SS))
pub(crate) fn tx1(
    tx0: &Transcript,
    initiator_longterm_pk: &DHPublicKey,
    responder_pq_pk: Option<&PQPublicKey<'_>>,
    pq_encaps: Option<&PQCiphertext>,
) -> Result<Transcript, Error> {
    #[derive(TlsSerialize, TlsSize)]
    struct Transcript1Inputs<'a> {
        initiator_longterm_pk: &'a DHPublicKey,
        responder_pq_pk: Option<&'a PQPublicKey<'a>>,
        pq_encaps: Option<&'a PQCiphertext>,
    }

    Transcript::add_hash::<TX1_DOMAIN_SEP>(
        Some(tx0),
        &Transcript1Inputs {
            initiator_longterm_pk,
            pq_encaps,
            responder_pq_pk,
        },
    )
}

// Registration Mode: tx2 = hash(2 | tx1 | g^y)
// Query Mode:        tx2 = hash(2 | tx0 | g^y)
pub(crate) fn tx2(
    prev_tx: &Transcript,
    responder_ephemeral_pk: &DHPublicKey,
) -> Result<Transcript, Error> {
    Transcript::add_hash::<TX2_DOMAIN_SEP>(Some(prev_tx), responder_ephemeral_pk)
}
