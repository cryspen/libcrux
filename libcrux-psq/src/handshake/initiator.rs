use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

use super::HandshakeMessageOut;

pub mod query;
pub mod registration;

#[derive(TlsSerialize, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayloadOut<'a> {
    Query(VLByteSlice<'a>),
    Registration(HandshakeMessageOut<'a>),
}

#[derive(TlsDeserialize, TlsSize)]
pub(crate) struct InitiatorInnerPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub(crate) struct InitiatorInnerPayloadOut<'a>(pub VLByteSlice<'a>);
