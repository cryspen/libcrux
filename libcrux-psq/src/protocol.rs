//! The PSQ registration protocol
#![allow(missing_docs)]

use api::Error;
use ecdh::PublicKey;
use libcrux_ml_kem::mlkem768::MlKem768Ciphertext;
use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

pub mod ecdh;
pub mod initiator;
mod keys;
pub mod responder;
pub mod session;
mod transcript;

pub mod api;

#[derive(TlsDeserialize, TlsSize)]
pub struct Message {
    pk: PublicKey,
    ciphertext: VLBytes,
    tag: [u8; 16],
    aad: VLBytes,
    pq_encapsulation: Option<MlKem768Ciphertext>,
}

#[derive(TlsSerialize, TlsSize)]
pub struct MessageOut<'a> {
    pk: &'a PublicKey,
    ciphertext: VLByteSlice<'a>,
    tag: [u8; 16], // XXX: implement Serialize for &[T; N]
    aad: VLByteSlice<'a>,
    pq_encapsulation: Option<&'a MlKem768Ciphertext>,
}

pub(crate) fn write_output(payload: &[u8], out: &mut [u8]) -> Result<usize, Error> {
    let payload_len = payload.len();
    if out.len() < payload_len {
        return Err(Error::OutputBufferShort);
    }
    out[..payload_len].copy_from_slice(payload);
    Ok(payload_len)
}
