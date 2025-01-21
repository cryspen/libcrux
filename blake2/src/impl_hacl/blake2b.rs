use libcrux_hacl_rs::streaming_types::error_code;

use crate::hacl::hash_blake2b::{
    blake2_params, digest, index, malloc_raw, params_and_key, reset, reset_with_key, state_t,
    update0,
};

use crate::impl_hacl::Error;

const PARAM_LEN: usize = 16;
const MAX_LEN: usize = 64;

/// A builder for [`Blake2b`]. `KEY_LEN`` must be in the range `0..=64``, `OUT_LEN`` must be in the
/// range `1..=64`.
pub struct Blake2bBuilder<'a, const KEY_LEN: usize, const OUT_LEN: usize> {
    key: &'a [u8; KEY_LEN],
    personal: &'a [u8; PARAM_LEN],
    salt: &'a [u8; PARAM_LEN],
}

impl<const OUT_LEN: usize> Blake2bBuilder<'_, 0, OUT_LEN> {
    /// Creates the builder for an unkeyed hasher and returns an error if the digest length
    /// `OUT_LEN` is not in the allowed range.
    pub fn new_unkeyed() -> Result<Self, Error> {
        if OUT_LEN < 1 || OUT_LEN > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        Ok(Self {
            key: &[],
            personal: &[0; PARAM_LEN],
            salt: &[0; PARAM_LEN],
        })
    }
}
impl<'a, const KEY_LEN: usize, const OUT_LEN: usize> Blake2bBuilder<'a, KEY_LEN, OUT_LEN> {
    /// Creates the builder and returns an error if the lengths `KEY_LEN` or `OUT_LEN` are not in
    /// the allowed range.
    pub fn new() -> Result<Self, Error> {
        if KEY_LEN > MAX_LEN {
            return Err(Error::InvalidKeyLength);
        }

        if OUT_LEN < 1 || OUT_LEN > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }
        Ok(Self {
            key: &[0; KEY_LEN],
            personal: &[0; PARAM_LEN],
            salt: &[0; PARAM_LEN],
        })
    }

    /// Sets the key to be used in the hasher.
    pub fn with_key(self, key: &'a [u8; KEY_LEN]) -> Self {
        Self { key, ..self }
    }

    /// Sets the personalization bytes to be used in the hasher.
    pub fn with_personalization(self, personal: &'a [u8; PARAM_LEN]) -> Self {
        Self { personal, ..self }
    }

    /// Sets the salt to be used in the hasher.
    pub fn with_salt(self, salt: &'a [u8; PARAM_LEN]) -> Self {
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
            state: malloc_raw(kk, key),
        }
    }
}

/// A hasher struct for the Blake2b (optionally keyed) hash function.
pub struct Blake2b<const KEY_LEN: usize, const OUT_LEN: usize> {
    state: Box<[state_t]>,
}

impl<const KEY_LEN: usize, const OUT_LEN: usize> Blake2b<KEY_LEN, OUT_LEN> {
    /// Updates the hash state by adding the bytes from `chunk` to the hashed data.
    pub fn update(&mut self, chunk: &[u8]) -> Result<(), Error> {
        if chunk.len() > (u32::MAX as usize) {
            return Err(Error::InvalidChunkLength);
        }

        match update0(self.state.as_mut(), chunk, chunk.len() as u32) {
            error_code::Success => Ok(()),
            error_code::MaximumLengthExceeded => Err(Error::MaximumLengthExceeded),
            _ => Err(Error::Unexpected),
        }
    }

    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8; OUT_LEN]) {
        digest(&self.state, dst);
    }

    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8; KEY_LEN]) {
        reset_with_key(&mut self.state, key);
    }
}

impl<const OUT_LEN: usize> Blake2b<0, OUT_LEN> {
    /// Reset the hash state.
    pub fn reset(&mut self) {
        reset(&mut self.state)
    }
}
