use alloc::vec::Vec;

use hpke_rs_crypto::{error::Error, types::KdfAlgorithm, HpkeCrypto};

use crate::util::concat;

const HPKE_VERSION: &[u8] = b"HPKE-v1";

pub(crate) fn labeled_extract<Crypto: HpkeCrypto>(
    alg: KdfAlgorithm,
    salt: &[u8],
    suite_id: &[u8],
    label: &str,
    ikm: &[u8],
) -> Vec<u8> {
    let labeled_ikm = concat(&[HPKE_VERSION, suite_id, label.as_bytes(), ikm]);
    Crypto::kdf_extract(alg, salt, &labeled_ikm)
}

pub(crate) fn labeled_expand<Crypto: HpkeCrypto>(
    alg: KdfAlgorithm,
    prk: &[u8],
    suite_id: &[u8],
    label: &'static str,
    info: &[u8],
    len: usize,
) -> Result<Vec<u8>, Error> {
    debug_assert!(len < 256);
    let len_bytes = (len as u16).to_be_bytes();
    let labeled_info = concat(&[&len_bytes, HPKE_VERSION, suite_id, label.as_bytes(), info]);
    Crypto::kdf_expand(alg, prk, &labeled_info, len)
}
