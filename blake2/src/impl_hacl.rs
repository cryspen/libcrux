use crate::hacl::hash_blake2b::{blake2_params, index, params_and_key};

use crate::hacl::hash_blake2b::{
    digest as blake2b_digest, malloc_raw as blake2b_malloc_raw, reset as blake2b_reset,
    reset_with_key as blake2b_reset_with_key, state_t as blake2b_state_t,
    update0 as blake2b_update0,
};

use crate::hacl::hash_blake2s::{
    digest as blake2s_digest, malloc_raw as blake2s_malloc_raw, reset as blake2s_reset,
    reset_with_key as blake2s_reset_with_key, state_t as blake2s_state_t,
    update0 as blake2s_update0,
};

extern crate alloc;

use alloc::boxed::Box;
use libcrux_hacl_rs::streaming_types::error_code;

const BLAKE2B_PARAM_LEN: usize = 16;
const BLAKE2S_PARAM_LEN: usize = 8;

const BLAKE2B_MAX_LEN: usize = 64;
const BLAKE2S_MAX_LEN: usize = 32;

/// Indicates an error has occurred
#[derive(Debug)]
pub enum Error {
    /// The used key length is invalid.
    InvalidKeyLength,
    /// The used digest length is invalid.
    InvalidDigestLength,
    ///The maximum input length is exceeded.
    MaximumLengthExceeded,
    /// The maximum chunk length is exceeded.
    InvalidChunkLength,
    /// An unexpected error has occurred.
    Unexpected,
}

impl alloc::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            Error::InvalidKeyLength => "The used key length is invalid.",
            Error::InvalidDigestLength => "The used digest length is invalid.",
            Error::MaximumLengthExceeded => "The maximum input length is exceeded.",
            Error::InvalidChunkLength => "The maximum chunk length is exceeded.",
            Error::Unexpected => "An unexpected error has occurred.",
        };

        write!(f, "{text}")
    }
}

impl core::error::Error for Error {}

/// A builder for [`Blake2b`]. `KEY_LEN`` must be in the range `0..=64``, `OUT_LEN`` must be in the
/// range `1..=64`.
pub struct Blake2bBuilder<'a, const KEY_LEN: usize, const OUT_LEN: usize> {
    key: &'a [u8; KEY_LEN],
    personal: &'a [u8; BLAKE2B_PARAM_LEN],
    salt: &'a [u8; BLAKE2B_PARAM_LEN],
}

impl<const OUT_LEN: usize> Blake2bBuilder<'_, 0, OUT_LEN> {
    /// Creates the builder for an unkeyed hasher and returns an error if the digest length
    /// `OUT_LEN` is not in the allowed range.
    pub fn new_unkeyed() -> Result<Self, Error> {
        if OUT_LEN < 1 || OUT_LEN > BLAKE2B_MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        Ok(Self {
            key: &[],
            personal: &[0; BLAKE2B_PARAM_LEN],
            salt: &[0; BLAKE2B_PARAM_LEN],
        })
    }
}
impl<'a, const KEY_LEN: usize, const OUT_LEN: usize> Blake2bBuilder<'a, KEY_LEN, OUT_LEN> {
    /// Creates the builder and returns an error if the lengths `KEY_LEN` or `OUT_LEN` are not in
    /// the allowed range.
    pub fn new() -> Result<Self, Error> {
        if KEY_LEN > BLAKE2B_MAX_LEN {
            return Err(Error::InvalidKeyLength);
        }

        if OUT_LEN < 1 || OUT_LEN > BLAKE2B_MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }
        Ok(Self {
            key: &[0; KEY_LEN],
            personal: &[0; BLAKE2B_PARAM_LEN],
            salt: &[0; BLAKE2B_PARAM_LEN],
        })
    }

    /// Sets the key to be used in the hasher.
    pub fn with_key(self, key: &'a [u8; KEY_LEN]) -> Self {
        Self { key, ..self }
    }

    /// Sets the personalization bytes to be used in the hasher.
    pub fn with_personalization(self, personal: &'a [u8; BLAKE2B_PARAM_LEN]) -> Self {
        Self { personal, ..self }
    }

    /// Sets the salt to be used in the hasher.
    pub fn with_salt(self, salt: &'a [u8; BLAKE2B_PARAM_LEN]) -> Self {
        Self { salt, ..self }
    }

    /// Constructs the [`Blake2b`] hasher.
    pub fn build(self) -> Blake2b<KEY_LEN, OUT_LEN> {
        // these are safe because they bot are at most 64
        let key_length = KEY_LEN as u8;
        let digest_length = OUT_LEN as u8;

        // NOTE: I am not entirely sure that this is the correct value. From reading the spec I
        // think it should be `true`, but when comparing with other implementations I only get the
        // same values when using `false`.
        let last_node = false;

        let kk = index {
            key_length,
            digest_length,
            last_node,
        };

        let params = blake2_params {
            digest_length,
            key_length,
            fanout: 1,
            depth: 1,
            leaf_length: 0,
            node_offset: 0,
            node_depth: 0,
            inner_length: 0,
            salt: self.salt,
            personal: self.personal,
        };

        let key = params_and_key {
            fst: &[params],
            snd: self.key,
        };

        Blake2b {
            state: blake2b_malloc_raw(kk, key),
        }
    }
}

/// A builder for [`Blake2s`]. `KEY_LEN`` must be in the range `0..=64``, `OUT_LEN`` must be in the
/// range `1..=64`.
pub struct Blake2sBuilder<'a, const KEY_LEN: usize, const OUT_LEN: usize> {
    key: &'a [u8; KEY_LEN],
    personal: &'a [u8; BLAKE2S_PARAM_LEN],
    salt: &'a [u8; BLAKE2S_PARAM_LEN],
}

impl<const OUT_LEN: usize> Blake2sBuilder<'_, 0, OUT_LEN> {
    /// Creates the builder for an unkeyed hasher and returns an error if the digest length
    /// `OUT_LEN` is not in the allowed range.
    pub fn new_unkeyed() -> Result<Self, Error> {
        if OUT_LEN < 1 || OUT_LEN > 64 {
            return Err(Error::InvalidDigestLength);
        }

        Ok(Self {
            key: &[],
            personal: &[0; BLAKE2S_PARAM_LEN],
            salt: &[0; BLAKE2S_PARAM_LEN],
        })
    }
}
impl<'a, const KEY_LEN: usize, const OUT_LEN: usize> Blake2sBuilder<'a, KEY_LEN, OUT_LEN> {
    /// Creates the builder and returns an error if the lengths `KEY_LEN` or `OUT_LEN` are not in
    /// the allowed range.
    pub fn new() -> Result<Self, Error> {
        if KEY_LEN > BLAKE2S_MAX_LEN {
            return Err(Error::InvalidKeyLength);
        }

        if OUT_LEN < 1 || OUT_LEN > BLAKE2S_MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }
        Ok(Self {
            key: &[0; KEY_LEN],
            personal: &[0; BLAKE2S_PARAM_LEN],
            salt: &[0; BLAKE2S_PARAM_LEN],
        })
    }

    /// Sets the key to be used in the hasher.
    pub fn with_key(self, key: &'a [u8; KEY_LEN]) -> Self {
        Self { key, ..self }
    }

    /// Sets the personalization bytes to be used in the hasher.
    pub fn with_personalization(self, personal: &'a [u8; BLAKE2S_PARAM_LEN]) -> Self {
        Self { personal, ..self }
    }

    /// Sets the salt to be used in the hasher.
    pub fn with_salt(self, salt: &'a [u8; BLAKE2S_PARAM_LEN]) -> Self {
        Self { salt, ..self }
    }

    /// Constructs the [`Blake2s`] hasher.
    pub fn build(self) -> Blake2s<KEY_LEN, OUT_LEN> {
        // these are safe because they bot are at most 32
        let key_length = KEY_LEN as u8;
        let digest_length = OUT_LEN as u8;

        // NOTE: I am not entirely sure that this is the correct value. From reading the spec I
        // think it should be `true`, but when comparing with other implementations I only get the
        // same values when using `false`.
        let last_node = false;

        let kk = index {
            key_length,
            digest_length,
            last_node,
        };

        let params = blake2_params {
            digest_length,
            key_length,
            fanout: 1,
            depth: 1,
            leaf_length: 0,
            node_offset: 0,
            node_depth: 0,
            inner_length: 0,
            salt: self.salt,
            personal: self.personal,
        };

        let key = params_and_key {
            fst: &[params],
            snd: self.key,
        };

        Blake2s {
            state: blake2s_malloc_raw(kk, key),
        }
    }
}

/// A hasher struct for the Blake2b (optionally keyed) hash function.
pub struct Blake2b<const KEY_LEN: usize, const OUT_LEN: usize> {
    state: Box<[blake2b_state_t]>,
}

impl<const KEY_LEN: usize, const OUT_LEN: usize> Blake2b<KEY_LEN, OUT_LEN> {
    /// Updates the hash state by adding the bytes from `chunk` to the hashed data.
    pub fn update(&mut self, chunk: &[u8]) -> Result<(), Error> {
        if chunk.len() > (u32::MAX as usize) {
            return Err(Error::InvalidChunkLength);
        }

        match blake2b_update0(self.state.as_mut(), chunk, chunk.len() as u32) {
            error_code::Success => Ok(()),
            error_code::MaximumLengthExceeded => Err(Error::MaximumLengthExceeded),
            _ => Err(Error::Unexpected),
        }
    }

    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8; OUT_LEN]) {
        blake2b_digest(&self.state, dst);
    }

    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8; KEY_LEN]) {
        blake2b_reset_with_key(&mut self.state, key);
    }
}

impl<const OUT_LEN: usize> Blake2b<0, OUT_LEN> {
    /// Reset the hash state.
    pub fn reset(&mut self) {
        blake2b_reset(&mut self.state)
    }
}

/// A hasher struct for the Blake2s (optionally keyed) hash function.
pub struct Blake2s<const KEY_LEN: usize, const OUT_LEN: usize> {
    state: Box<[blake2s_state_t]>,
}

impl<const KEY_LEN: usize, const OUT_LEN: usize> Blake2s<KEY_LEN, OUT_LEN> {
    /// Updates the hash state by adding the bytes from `chunk` to the hashed data.
    pub fn update(&mut self, chunk: &[u8]) -> Result<(), Error> {
        if chunk.len() > (u32::MAX as usize) {
            return Err(Error::InvalidChunkLength);
        }

        match blake2s_update0(self.state.as_mut(), chunk, chunk.len() as u32) {
            error_code::Success => Ok(()),
            error_code::MaximumLengthExceeded => Err(Error::MaximumLengthExceeded),
            _ => Err(Error::Unexpected),
        }
    }

    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8; OUT_LEN]) {
        blake2s_digest(&self.state, dst);
    }

    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8; KEY_LEN]) {
        blake2s_reset_with_key(&mut self.state, key);
    }
}

impl<const OUT_LEN: usize> Blake2s<0, OUT_LEN> {
    /// Reset the hash state.
    pub fn reset(&mut self) {
        blake2s_reset(&mut self.state)
    }
}

#[cfg(test)]
mod test {
    use super::{Blake2b, Blake2bBuilder};

    #[test]
    fn test_hash() {
        let mut got_hash = [0; 32];
        let mut hasher: Blake2b<0, 32> = Blake2bBuilder::new().unwrap().build();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);
        let expected_hash = b"\xe9\xed\x14\x1d\xf1\xce\xbf\xc8\x9e\x46\x6c\xe0\x89\xee\xdd\x4f\x12\x5a\xa7\x57\x15\x01\xa0\xaf\x87\x1f\xab\x60\x59\x71\x17\xb7";

        assert_eq!(&got_hash, expected_hash);

        let mut got_hash = [0; 64];
        let mut hasher: Blake2b<0, 64> = Blake2bBuilder::new().unwrap().build();
        hasher.update(b"this is a test").unwrap();
        hasher.finalize(&mut got_hash);
        let expected_hash = b"\x61\xa5\x48\xf2\xde\x1c\x31\x8b\xa9\x1d\x52\x07\x00\x78\x61\x01\x0f\x69\xa4\x3e\xc6\x63\xfe\x48\x7d\x84\x03\x28\x2c\x93\x4e\xa7\x25\xdc\x0b\xb1\x72\x25\x6a\xc9\x96\x25\xad\x64\xcc\xa6\xa2\xc4\xd6\x1c\x65\x0a\x35\xaf\xab\x47\x87\xdc\x67\x8e\x19\x07\x1e\xf9";

        assert_eq!(&got_hash, expected_hash);
    }
}
