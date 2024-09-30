use crate::hash_functions::shake128::Xof;

pub(crate) type PreHashOID = [u8; 11];
pub(crate) const PRE_HASH_OID_LEN: usize = 11;

pub(crate) trait PreHash<const DIGEST_LEN: usize> {
    fn to_oid() -> PreHashOID;
    fn hash(message: &[u8]) -> [u8; DIGEST_LEN];
}

#[allow(non_camel_case_types)]
pub(crate) struct SHAKE128_PH();

impl PreHash<256> for SHAKE128_PH {
    fn to_oid() -> PreHashOID {
        [
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b,
        ]
    }

    fn hash(message: &[u8]) -> [u8; 256] {
        let mut output = [0u8; 256];
        crate::hash_functions::portable::Shake128::shake128(message, &mut output);

        output
    }
}
