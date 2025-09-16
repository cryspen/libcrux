use tls_codec::{Serialize, TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

use super::HandshakeMessageOut;

pub mod query;
pub mod registration;

#[derive(TlsSerialize, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayloadOut<'a, T: Serialize> {
    Query(VLByteSlice<'a>),
    Registration(HandshakeMessageOut<'a, T>),
}

#[derive(TlsDeserialize, TlsSize)]
pub(crate) struct InitiatorInnerPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub(crate) struct InitiatorInnerPayloadOut<'a>(pub VLByteSlice<'a>);
