use std::marker::PhantomData;

use crate::hacl::hash_blake2b::{blake2_params, index, params_and_key};
use crate::hacl::hash_blake2s::{digest, malloc_raw, reset, reset_with_key, state_t, update0};

const PARAM_LEN: usize = 8;
const MAX_LEN: usize = 32;

use super::*;

/// A builder for [`Blake2s`]. `KEY_LEN`` must be in the range `0..=x61\xa5\x48\xf2\xde\x1c\x31\x8b\xa9\x1d\x52\x07\x00\x78\x61\x01\x0f\x69\xa4\x3e\xc6\x63\xfe\x48\x7d\x84\x03\x28\x2c\x93\x4e\xa7\x25\xdc\x0b\xb1\x72\x25\x6a\xc9\x96\x25\xad\x64\xcc\xa6\xa2\xc4\xd6\x1c\x65\x0a\x35\xaf\xab\x47\x87\xdc\x67\x8e\x19\x07\x1e\xf9``, `OUT_LEN`` must be in the
/// range `1..=32`.
pub struct Blake2sBuilder<'a, T> {
    key: T,
    personal: &'a [u8; PARAM_LEN],
    salt: &'a [u8; PARAM_LEN],
}

impl<'a> Blake2sBuilder<'a, &'a ()> {
    /// Creates the builder for an unkeyed hasher.
    pub fn new_unkeyed() -> Result<Self, Error> {
        Ok(Self {
            key: &(),
            personal: &[0; PARAM_LEN],
            salt: &[0; PARAM_LEN],
        })
    }

    /// Constructs the [`Blake2s`] hasher for unkeyed hashes and dynamic digest length.
    pub fn build(self, digest_length: u8) -> Result<Blake2s<Blake2sStaticKey<0>>, Error> {
        if digest_length < 1 || digest_length as usize > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        let key_length = 0;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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
            snd: &[],
        };

        Ok(Blake2s {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }

    /// Constructs the [`Blake2s`] hasher for unkeyed hashes and static digest length.
    pub fn build_static<const OUT_LEN: usize>(
        self,
    ) -> Result<Blake2s<Blake2sStaticKeyStaticOut<0, OUT_LEN>>, Error> {
        if OUT_LEN < 1 || OUT_LEN > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        let key_length = 0;

        // This is safe because it's at most 32, enforced at the start of the function.
        let digest_length = OUT_LEN as u8;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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
            snd: &[],
        };

        Ok(Blake2s {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }
}

impl<'a, const KEY_LEN: usize> Blake2sBuilder<'a, &'a [u8; KEY_LEN]> {
    /// Creates the builder for an keyed hasher for keys where the length is known at compile
    /// time.
    pub fn new_keyed_static(key: &'a [u8; KEY_LEN]) -> Result<Self, Error> {
        if KEY_LEN > MAX_LEN {
            return Err(Error::InvalidKeyLength);
        }

        Ok(Self {
            key,
            personal: &[0; PARAM_LEN],
            salt: &[0; PARAM_LEN],
        })
    }

    /// Constructs the [`Blake2s`] hasher for hashes with static key length and dynamic digest length.
    pub fn build(self, digest_length: u8) -> Result<Blake2s<Blake2sStaticKey<KEY_LEN>>, Error> {
        if digest_length < 1 || digest_length as usize > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        // This is safe because it's at most 32, enforced in the constructor.
        let key_length = KEY_LEN as u8;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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

        Ok(Blake2s::<Blake2sDynamic> {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }

    /// Constructs the [`Blake2s`] hasher for hashes with static key length and static digest length.
    pub fn build_static<const OUT_LEN: usize>(
        self,
    ) -> Result<Blake2s<Blake2sStaticKeyStaticOut<KEY_LEN, OUT_LEN>>, Error> {
        if OUT_LEN < 1 || OUT_LEN > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        // These are safe because they both are at most 32, enforced either above or in the
        // constructor.
        let key_length = KEY_LEN as u8;
        let digest_length = OUT_LEN as u8;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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

        Ok(Blake2s::<Blake2sStaticKeyStaticOut<KEY_LEN, OUT_LEN>> {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }
}

impl<'a> Blake2sBuilder<'a, &'a [u8]> {
    /// Creates the builder for an keyed hasher for keys where the length is not known at compile
    /// time.
    pub fn new_keyed_dynamic(key: &'a [u8]) -> Result<Self, Error> {
        if key.len() > MAX_LEN {
            return Err(Error::InvalidKeyLength);
        }

        Ok(Self {
            key,
            personal: &[0; PARAM_LEN],
            salt: &[0; PARAM_LEN],
        })
    }

    /// Constructs the fully dynamic [`Blake2s`] hasher.
    pub fn build(self, digest_length: u8) -> Result<Blake2s<Blake2sDynamic>, Error> {
        if digest_length < 1 || digest_length as usize > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        // This is safe because it's at most 32, enforced in the constructor.
        let key_length = self.key.len() as u8;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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

        Ok(Blake2s {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }

    /// Constructs the [`Blake2s`] hasher with dynamic key length and static digest length.
    pub fn build_static<const OUT_LEN: usize>(
        self,
    ) -> Result<Blake2s<Blake2sStaticOut<OUT_LEN>>, Error> {
        if OUT_LEN < 1 || OUT_LEN > MAX_LEN {
            return Err(Error::InvalidDigestLength);
        }

        // these are safe because they both are at most 32
        let key_length = self.key.len() as u8;
        let digest_length = OUT_LEN as u8;

        let kk = index {
            key_length,
            digest_length,
            last_node: false,
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

        Ok(Blake2s {
            state: malloc_raw(kk, key),
            _phantom: PhantomData,
        })
    }
}

impl<'a, T> Blake2sBuilder<'a, T> {
    /// Sets the personalization bytes to be used in the hasher.
    pub fn with_personalization(self, personal: &'a [u8; PARAM_LEN]) -> Self {
        Self { personal, ..self }
    }

    /// Sets the salt to be used in the hasher.
    pub fn with_salt(self, salt: &'a [u8; PARAM_LEN]) -> Self {
        Self { salt, ..self }
    }
}

pub struct Blake2sStaticKeyStaticOut<const KEY_LEN: usize, const OUT_LEN: usize>;
pub struct Blake2sStaticKey<const KEY_LEN: usize>;
pub struct Blake2sStaticOut<const OUT_LEN: usize>;
pub struct Blake2sDynamic;

/// A hasher struct for the Blake2s (optionally keyed) hash function.
pub struct Blake2s<T> {
    state: Box<[state_t]>,
    _phantom: PhantomData<T>,
}

impl<T> Blake2s<T> {
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
}

impl<const KEY_LEN: usize> Blake2s<Blake2sStaticKey<KEY_LEN>> {
    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8]) -> Result<usize, Error> {
        let digest_len = self.state[0].block_state.snd;
        if dst.len() < digest_len as usize {
            return Err(Error::InvalidDigestLength);
        }

        Ok(digest(&self.state, dst) as usize)
    }
}

impl Blake2s<Blake2sDynamic> {
    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8]) -> Result<usize, Error> {
        let digest_len = self.state[0].block_state.snd;
        if dst.len() < digest_len as usize {
            return Err(Error::InvalidDigestLength);
        }

        Ok(digest(&self.state, dst) as usize)
    }
}

impl<const KEY_LEN: usize, const OUT_LEN: usize>
    Blake2s<Blake2sStaticKeyStaticOut<KEY_LEN, OUT_LEN>>
{
    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8; OUT_LEN]) {
        digest(&self.state, dst);
    }
}

impl<const OUT_LEN: usize> Blake2s<Blake2sStaticOut<OUT_LEN>> {
    /// Compute the hash for the current hash state and write it to `dst`.
    pub fn finalize(&self, dst: &mut [u8; OUT_LEN]) {
        digest(&self.state, dst);
    }
}

impl<const KEY_LEN: usize, const OUT_LEN: usize>
    Blake2s<Blake2sStaticKeyStaticOut<KEY_LEN, OUT_LEN>>
{
    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8; KEY_LEN]) {
        reset_with_key(&mut self.state, key);
    }
}

impl<const KEY_LEN: usize> Blake2s<Blake2sStaticKey<KEY_LEN>> {
    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8; KEY_LEN]) {
        reset_with_key(&mut self.state, key);
    }
}

impl<const OUT_LEN: usize> Blake2s<Blake2sStaticOut<OUT_LEN>> {
    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8]) -> Result<(), Error> {
        // check that the key length matches
        if self.state.as_ref()[0].block_state.fst as usize != key.len() {
            return Err(Error::InvalidKeyLength);
        }

        reset_with_key(&mut self.state, key);
        Ok(())
    }
}

impl Blake2s<Blake2sDynamic> {
    /// Reset the hash state and update the key to the contents of `key`.
    pub fn reset_with_key(&mut self, key: &[u8]) -> Result<(), Error> {
        // check that the key length matches
        if self.state[0].block_state.fst as usize != key.len() {
            return Err(Error::InvalidKeyLength);
        }

        reset_with_key(&mut self.state, key);
        Ok(())
    }
}

impl Blake2s<Blake2sStaticKey<0>> {
    /// Reset the hash state.
    pub fn reset(&mut self) {
        reset(&mut self.state)
    }
}

impl<const OUT_LEN: usize> Blake2s<Blake2sStaticKeyStaticOut<0, OUT_LEN>> {
    /// Reset the hash state.
    pub fn reset(&mut self) {
        reset(&mut self.state)
    }
}

impl<const OUT_LEN: usize> Blake2s<Blake2sStaticOut<OUT_LEN>> {
    /// Reset the hash state.
    pub fn reset(&mut self) -> Result<(), Error> {
        // check that the key length matches
        if self.state.as_ref()[0].block_state.fst != 0 {
            return Err(Error::InvalidKeyLength);
        }

        reset(&mut self.state);
        Ok(())
    }
}

impl Blake2s<Blake2sDynamic> {
    /// Reset the hash state.
    pub fn reset(&mut self) -> Result<(), Error> {
        // check that the key length matches
        if self.state.as_ref()[0].block_state.fst != 0 {
            return Err(Error::InvalidKeyLength);
        }

        reset(&mut self.state);
        Ok(())
    }
}
