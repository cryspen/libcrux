use std::convert::TryInto;

use crate::hkdf;
use crate::util::*;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Mode {
    HkdfSha256 = 0x0001,
    HkdfSha384 = 0x0002,
    HkdfSha512 = 0x0003,
}

pub(crate) trait KdfTrait {
    // const HASH_LEN: usize;
    fn new() -> Self
    where
        Self: Sized;
    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8>;
    fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8>;
    fn digest_length(&self) -> usize;
}

pub struct Kdf {
    mode: Mode,
    hash_len: usize,
    kdf: Box<dyn KdfTrait>,
}

impl Kdf {
    pub fn new(mode: Mode) -> Self {
        let kdf = get_kdf_object(mode);
        Self {
            mode: mode,
            hash_len: kdf.digest_length(),
            kdf: kdf,
        }
    }

    pub fn get_nh(&self) -> usize {
        self.kdf.digest_length()
    }

    pub(crate) fn labeled_extract(&self, salt: &[u8], label: &'static str, ikm: &[u8]) -> Vec<u8> {
        let labeled_ikm = concat(&[&"RFCXXXX ".as_bytes(), &label.as_bytes(), ikm]);
        self.kdf.extract(salt, &labeled_ikm)
    }

    pub(crate) fn labeled_expand(
        &self,
        prk: &[u8],
        label: &'static str,
        info: &[u8],
        len: usize,
    ) -> Vec<u8> {
        let len_bytes = len.to_be_bytes();
        assert!(len < 256);
        let labeled_info = concat(&[
            &len_bytes[len_bytes.len() - 2..],
            &"RFCXXXX ".as_bytes(),
            &label.as_bytes(),
            info,
        ]);
        self.kdf.expand(prk, &labeled_info, len)
    }

    pub fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        self.kdf.extract(salt, ikm)
    }

    pub fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8> {
        self.kdf.expand(prk, info, output_size)
    }
}

fn get_kdf_object(mode: Mode) -> Box<dyn KdfTrait> {
    match mode {
        Mode::HkdfSha256 => Box::new(hkdf::HkdfSha256::new()),
        Mode::HkdfSha384 => Box::new(hkdf::HkdfSha384::new()),
        Mode::HkdfSha512 => Box::new(hkdf::HkdfSha512::new()),
    }
}
