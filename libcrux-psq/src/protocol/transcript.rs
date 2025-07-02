use tls_codec::{SerializeBytes, TlsSerializeBytes, TlsSize};

pub const TX0_DOMAIN_SEP: u8 = 0;
pub const TX1_DOMAIN_SEP: u8 = 1;
pub const TX2_DOMAIN_SEP: u8 = 2;

use super::ecdh::PublicKey;
use libcrux_sha2::SHA256_LENGTH;

/// The initial transcript hash.
#[derive(Debug, Clone, Copy, TlsSerializeBytes, TlsSize)]
pub(crate) struct Transcript([u8; SHA256_LENGTH]);

impl Transcript {
    fn new(initial_input: &impl SerializeBytes) -> Self {
        Self::add_hash::<TX0_DOMAIN_SEP>(None, initial_input)
    }

    fn add_hash<const DOMAIN_SEPARATOR: u8>(
        old_transcript: Option<Transcript>,
        input: &impl SerializeBytes,
    ) -> Transcript {
        let mut domain_separated_input = vec![DOMAIN_SEPARATOR];
        domain_separated_input
            .extend_from_slice(old_transcript.tls_serialize().unwrap().as_slice());
        domain_separated_input.extend_from_slice(input.tls_serialize().unwrap().as_slice());

        Transcript(libcrux_sha2::sha256(&domain_separated_input))
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
    responder_pk: &PublicKey,
    initiator_pk: &PublicKey,
) -> Transcript {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct Transcript0Inputs {
        context: Vec<u8>,
        responder_pk: PublicKey,
        initiator_pk: PublicKey,
    }

    Transcript::new(&Transcript0Inputs {
        context: context.to_vec(),
        responder_pk: responder_pk.clone(),
        initiator_pk: initiator_pk.clone(),
    })
}

// Registration Mode: tx2 = hash(2 | tx1 | g^y)
// Query Mode:        tx2 = hash(2 | tx0 | g^y)
pub(crate) fn tx2(prev_tx: &Transcript, responder_ephemeral_pk: &PublicKey) -> Transcript {
    Transcript::add_hash::<TX2_DOMAIN_SEP>(Some(*prev_tx), responder_ephemeral_pk)
}
