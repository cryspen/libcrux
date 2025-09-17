use tls_codec::{TlsDeserialize, TlsSerialize, TlsSize, VLByteSlice, VLBytes};

use crate::handshake::ciphersuite::CiphersuiteBase;

use super::HandshakeMessageOut;

pub mod query;
pub mod registration;

#[derive(TlsSerialize, TlsSize)]
#[repr(u8)]
pub enum InitiatorOuterPayloadOut<'a, Ciphersuite: CiphersuiteBase> {
    Query(VLByteSlice<'a>),
    Registration(HandshakeMessageOut<'a, Ciphersuite>),
}

#[derive(TlsDeserialize, TlsSize)]
pub(crate) struct InitiatorInnerPayload(pub VLBytes);

#[derive(TlsSerialize, TlsSize)]
pub(crate) struct InitiatorInnerPayloadOut<'a>(pub VLByteSlice<'a>);
