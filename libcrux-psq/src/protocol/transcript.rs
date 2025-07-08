use tls_codec::{SerializeBytes, TlsSerializeBytes, TlsSize};

pub const TX0_DOMAIN_SEP: u8 = 0;
pub const TX1_DOMAIN_SEP: u8 = 1;
pub const TX2_DOMAIN_SEP: u8 = 2;

use super::ecdh::PublicKey;
use libcrux_sha2::SHA256_LENGTH;

/// The initial transcript hash.
#[derive(Debug, Clone, Copy, TlsSerializeBytes, TlsSize)]
pub struct Transcript([u8; SHA256_LENGTH]);

impl Transcript {
    fn new(initial_input: &impl SerializeBytes) -> Self {
        Self::add_hash::<TX0_DOMAIN_SEP>(None, initial_input)
    }

    fn add_hash<const DOMAIN_SEPARATOR: u8>(
        old_transcript: Option<&Transcript>,
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
    struct Transcript0Inputs<'a, 'b, 'c> {
        context: &'a [u8],
        responder_pk: &'b PublicKey,
        initiator_pk: &'c PublicKey,
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
    initiator_longterm_pk: &PublicKey,
    responder_pq_pk: Option<&libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
    pq_encaps: Option<&libcrux_ml_kem::mlkem768::MlKem768Ciphertext>,
) -> Transcript {
    #[derive(TlsSerializeBytes, TlsSize)]
    struct Transcript1Inputs<'a, 'b, 'c> {
        initiator_longterm_pk: &'a PublicKey,
        responder_pq_pk: Option<&'b libcrux_ml_kem::mlkem768::MlKem768PublicKey>,
        pq_encaps: Option<&'c libcrux_ml_kem::mlkem768::MlKem768Ciphertext>,
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
pub(crate) fn tx2(prev_tx: &Transcript, responder_ephemeral_pk: &PublicKey) -> Transcript {
    Transcript::add_hash::<TX2_DOMAIN_SEP>(Some(prev_tx), responder_ephemeral_pk)
}
