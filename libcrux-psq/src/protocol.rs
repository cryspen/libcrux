//! The PSQ registration protocol
#![allow(missing_docs)]

use api::Error;
use dhkem::DHPublicKey;
use pqkem::PQCiphertext;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

pub mod dhkem;
pub mod initiator;
mod keys;
pub mod pqkem;
pub mod responder;
pub mod session;
mod transcript;

pub mod api;

#[derive(TlsDeserialize, TlsSize)]
pub struct Message {
    pk: DHPublicKey,
    ciphertext: VLBytes,
    tag: [u8; 16],
    aad: VLBytes,
    pq_encapsulation: Option<PQCiphertext>,
}

#[derive(TlsSerialize, TlsSize)]
pub struct MessageOut<'a> {
    pk: &'a DHPublicKey,
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16], // XXX: implement Serialize for &[T; N]
    aad: VLByteSlice<'a>,
    pq_encapsulation: Option<&'a PQCiphertext>,
}

pub(crate) fn write_output(payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    let payload_len = payload.len();
    if out.len() < payload_len {
        return Err(Error::OutputBufferShort);
    }
    out[..payload_len].copy_from_slice(payload);
    Ok(payload_len)
}
