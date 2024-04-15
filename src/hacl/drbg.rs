use libcrux_hacl::{
    Hacl_HMAC_DRBG_create_in, Hacl_HMAC_DRBG_free, Hacl_HMAC_DRBG_generate,
    Hacl_HMAC_DRBG_instantiate, Hacl_HMAC_DRBG_reseed, Hacl_HMAC_DRBG_state,
    Spec_Hash_Definitions_SHA1, Spec_Hash_Definitions_SHA2_256, Spec_Hash_Definitions_SHA2_384,
    Spec_Hash_Definitions_SHA2_512,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Algorithm {
    Sha1 = Spec_Hash_Definitions_SHA1 as u8,
    Sha2_256 = Spec_Hash_Definitions_SHA2_256 as u8,
    Sha2_384 = Spec_Hash_Definitions_SHA2_384 as u8,
    Sha2_512 = Spec_Hash_Definitions_SHA2_512 as u8,
}

pub enum Error {
    /// Invalid input, e.g. input values are too large.
    InvalidInput,

    /// Unable to generate the requested randomness.
    UnableToGenerate,
}

pub struct Drbg {
    state: Hacl_HMAC_DRBG_state,
    alg: Algorithm,
}

impl Drbg {
    /// Create a new DRBG state with the given hash function.
    /// This also initializes the DRBG state with the given entropy, nonce and
    /// personalization string.
    pub fn new(
        alg: Algorithm,
        entropy: &[u8],
        nonce: &[u8],
        personalization: &str,
    ) -> Result<Self, Error> {
        let state = unsafe { Hacl_HMAC_DRBG_create_in(alg as u8) };
        unsafe {
            Hacl_HMAC_DRBG_instantiate(
                alg as u8,
                state,
                entropy.len().try_into().map_err(|_| Error::InvalidInput)?,
                entropy.as_ptr() as _,
                nonce.len().try_into().map_err(|_| Error::InvalidInput)?,
                nonce.as_ptr() as _,
                personalization
                    .len()
                    .try_into()
                    .map_err(|_| Error::InvalidInput)?,
                personalization.as_bytes().as_ptr() as _,
            );
        }
        Ok(Self { state, alg })
    }

    /// Reseed the DRBG state.
    pub fn reseed(&mut self, entropy: &[u8], additional_input: &[u8]) -> Result<(), Error> {
        unsafe {
            Hacl_HMAC_DRBG_reseed(
                self.alg as u8,
                self.state,
                entropy.len().try_into().map_err(|_| Error::InvalidInput)?,
                entropy.as_ptr() as _,
                additional_input
                    .len()
                    .try_into()
                    .map_err(|_| Error::InvalidInput)?,
                additional_input.as_ptr() as _,
            );
        }

        Ok(())
    }

    /// Generate random bytes.
    ///
    /// Note that you will need to reseed after at most 1024 invocations.
    pub fn generate(&mut self, output: &mut [u8], additional_input: &[u8]) -> Result<(), Error> {
        let out_len = output.len().try_into().map_err(|_| Error::InvalidInput)?;
        let aad = additional_input
            .len()
            .try_into()
            .map_err(|_| Error::InvalidInput)?;
        if unsafe {
            Hacl_HMAC_DRBG_generate(
                self.alg as u8,
                output.as_mut_ptr(),
                self.state,
                out_len,
                aad,
                additional_input.as_ptr() as _,
            )
        } {
            Ok(())
        } else {
            Err(Error::UnableToGenerate)
        }
    }
}

impl Drop for Drbg {
    fn drop(&mut self) {
        unsafe { Hacl_HMAC_DRBG_free(self.alg as u8, self.state) };
    }
}

unsafe impl Send for Drbg {}
