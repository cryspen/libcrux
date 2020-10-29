use crate::hkdf;
use crate::util::concat;

use std::fmt::Debug;

#[derive(PartialEq, Copy, Clone, Debug)]
#[repr(u16)]
pub enum Mode {
    HkdfSha256 = 0x0001,
    HkdfSha384 = 0x0002,
    HkdfSha512 = 0x0003,
}

impl From<u16> for Mode {
    fn from(x: u16) -> Mode {
        match x {
            0x0001 => Mode::HkdfSha256,
            0x0002 => Mode::HkdfSha384,
            0x0003 => Mode::HkdfSha512,
            _ => panic!("Unknown KDF Mode {}", x),
        }
    }
}

pub(crate) trait KdfTrait: Debug {
    fn new() -> Self
    where
        Self: Sized;
    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8>;
    fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8>;
    fn digest_length(&self) -> usize;
}

#[derive(Debug)]
pub struct Kdf {
    kdf: Box<dyn KdfTrait>,
}

impl Kdf {
    pub(crate) fn new(mode: Mode) -> Self {
        Self {
            kdf: get_kdf_object(mode),
        }
    }

    pub(crate) fn get_nh(&self) -> usize {
        self.kdf.digest_length()
    }

    pub(crate) fn labeled_extract(
        &self,
        salt: &[u8],
        suite_id: &[u8],
        label: &str,
        ikm: &[u8],
    ) -> Vec<u8> {
        let labeled_ikm = concat(&[b"HPKE-06", suite_id, &label.as_bytes(), ikm]);
        self.kdf.extract(salt, &labeled_ikm)
    }

    pub(crate) fn labeled_expand(
        &self,
        prk: &[u8],
        suite_id: &[u8],
        label: &'static str,
        info: &[u8],
        len: usize,
    ) -> Vec<u8> {
        assert!(len < 256);
        let len_bytes = (len as u16).to_be_bytes();
        let labeled_info = concat(&[&len_bytes, b"HPKE-06", suite_id, &label.as_bytes(), info]);
        self.kdf.expand(prk, &labeled_info, len)
    }

    #[cfg(test)]
    pub(crate) fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        self.kdf.extract(salt, ikm)
    }

    #[cfg(test)]
    pub(crate) fn expand(&self, prk: &[u8], info: &[u8], output_size: usize) -> Vec<u8> {
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
