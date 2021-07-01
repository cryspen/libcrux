use evercrypt::prelude::*;

use crate::kdf;
use crate::kem::*;
use crate::util::*;

#[derive(Debug)]
pub(crate) struct DhKem {
    encoded_pk_len: usize,
    sk_len: usize,
    kdf: kdf::Kdf,
    dh_id: ecdh::Mode,
    #[cfg(feature = "deterministic")]
    randomness: Vec<u8>,
}

impl DhKem {
    pub fn init(kdf_id: kdf::Mode, dh_id: ecdh::Mode) -> Self {
        Self {
            sk_len: 32,
            encoded_pk_len: match dh_id {
                ecdh::Mode::X25519 => 32,
                ecdh::Mode::P256 => 64,
            },
            kdf: kdf::Kdf::new(kdf_id),
            dh_id,
            #[cfg(feature = "deterministic")]
            randomness: Vec::new(),
        }
    }
    fn dh(&self, sk: &[u8], pk: &[u8]) -> Result<Vec<u8>, Error> {
        let dh = ecdh_derive(self.dh_id, pk, sk)?;

        match self.dh_id {
            ecdh::Mode::X25519 => Ok(dh),
            ecdh::Mode::P256 => {
                if dh.len() <= 32 {
                    return Err(Error::CryptoError);
                }
                Ok(dh[0..32].to_vec())
            }
        }
    }

    /// Prepend 0x04 for uncompressed NIST curve points.
    #[inline(always)]
    fn nist_format_uncompressed(mut pk: Vec<u8>) -> Vec<u8> {
        let mut tmp = Vec::with_capacity(pk.len() + 1);
        tmp.push(0x04);
        tmp.append(&mut pk);
        tmp
    }

    fn dh_base(&self, sk: &[u8]) -> Result<Vec<u8>, Error> {
        let out = ecdh_derive_base(self.dh_id, sk)?;
        match self.dh_id {
            ecdh::Mode::X25519 => Ok(out),
            ecdh::Mode::P256 => Ok(Self::nist_format_uncompressed(out)),
        }
    }

    fn extract_and_expand(&self, pk: PublicKey, kem_context: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let prk = self.kdf.labeled_extract(&[], suite_id, "eae_prk", &pk);
        self.kdf.labeled_expand(
            &prk,
            suite_id,
            "shared_secret",
            kem_context,
            self.secret_len(),
        )
    }

    /// Serialize public key.
    /// This is an identity function for X25519.
    /// Because P256 public keys are already encoded before it is the identity
    /// function here as well.
    fn serialize(&self, pk: &[u8]) -> Vec<u8> {
        pk.to_vec()
    }

    fn deserialize(&self, enc: &[u8]) -> Vec<u8> {
        enc.to_vec()
    }

    #[cfg(feature = "deterministic")]
    fn random(&self) -> Vec<u8> {
        if self.randomness.len() == self.secret_len() {
            self.randomness.clone()
        } else {
            // In this case the randomness wasn't set. Just use real randomness.
            random(self.secret_len())
        }
    }

    #[cfg(not(feature = "deterministic"))]
    fn random(&self) -> Vec<u8> {
        random(self.secret_len())
    }
}

impl KemTrait for DhKem {
    fn secret_len(&self) -> usize {
        self.sk_len
    }
    fn encoded_pk_len(&self) -> usize {
        self.encoded_pk_len
    }

    fn new(_kdf_id: kdf::Mode) -> Self {
        panic!("Don't use this please");
    }

    fn key_gen(&self) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let sk = ecdh::key_gen(self.dh_id)?;
        let pk = self.dh_base(&sk)?;
        Ok((sk, pk))
    }

    fn derive_key_pair(
        &self,
        suite_id: &[u8],
        ikm: &[u8],
    ) -> Result<(PublicKey, PrivateKey), Error> {
        let dkp_prk = self.kdf.labeled_extract(&[], suite_id, "dkp_prk", ikm);

        let sk = match self.dh_id {
            ecdh::Mode::X25519 => {
                self.kdf
                    .labeled_expand(&dkp_prk, suite_id, "sk", &[], self.sk_len)
            }
            ecdh::Mode::P256 => {
                let mut ctr = 0u8;
                // Do rejection sampling trying to find a valid key.
                // It is expected that there aren't too many iteration and that
                // the loop will always terminate.
                loop {
                    let candidate = self.kdf.labeled_expand(
                        &dkp_prk,
                        suite_id,
                        "candidate",
                        &ctr.to_be_bytes(),
                        self.sk_len,
                    );
                    if let Ok(sk) = p256_validate_sk(&candidate) {
                        break sk.to_vec();
                    }
                    if ctr == u8::MAX {
                        // If we get here we lost. This should never happen.
                        return Err(Error::KeyGenerationError);
                    }
                    ctr += 1;
                }
            }
        };
        Ok((self.dh_base(&sk)?, sk))
    }

    fn encaps(&self, pk_r: &[u8], suite_id: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let (pk_e, sk_e) = self.derive_key_pair(suite_id, &self.random())?;
        let dh_pk = self.dh(&sk_e, pk_r)?;
        let enc = self.serialize(&pk_e);

        let pk_rm = self.serialize(pk_r);
        let kem_context = concat(&[&enc, &pk_rm]);

        let zz = self.extract_and_expand(dh_pk, &kem_context, suite_id);
        Ok((zz, enc))
    }

    fn decaps(&self, enc: &[u8], sk_r: &[u8], suite_id: &[u8]) -> Result<Vec<u8>, Error> {
        let pk_e = self.deserialize(enc);
        let dh_pk = self.dh(sk_r, &pk_e)?;

        let pk_rm = self.serialize(&self.dh_base(sk_r)?);
        let kem_context = concat(&[enc, &pk_rm]);

        Ok(self.extract_and_expand(dh_pk, &kem_context, suite_id))
    }
    fn auth_encaps(
        &self,
        pk_r: &[u8],
        sk_s: &[u8],
        suite_id: &[u8],
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let (pk_e, sk_e) = self.derive_key_pair(suite_id, &self.random())?;
        let dh_pk = concat(&[&self.dh(&sk_e, pk_r)?, &self.dh(sk_s, pk_r)?]);

        let enc = self.serialize(&pk_e);
        let pk_rm = self.serialize(pk_r);
        let pk_sm = self.serialize(&self.dh_base(sk_s)?);

        let kem_context = concat(&[&enc, &pk_rm, &pk_sm]);

        let zz = self.extract_and_expand(dh_pk, &kem_context, suite_id);
        Ok((zz, enc))
    }
    fn auth_decaps(
        &self,
        enc: &[u8],
        sk_r: &[u8],
        pk_s: &[u8],
        suite_id: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let pk_e = self.deserialize(enc);
        let dh_pk = concat(&[&self.dh(sk_r, &pk_e)?, &self.dh(sk_r, pk_s)?]);

        let pk_rm = self.serialize(&self.dh_base(sk_r)?);
        let pk_sm = self.serialize(pk_s);
        let kem_context = concat(&[enc, &pk_rm, &pk_sm]);

        Ok(self.extract_and_expand(dh_pk, &kem_context, suite_id))
    }

    #[cfg(feature = "deterministic")]
    fn set_random(&mut self, r: &[u8]) {
        self.randomness = r.to_vec();
    }
}

impl From<EcdhError> for Error {
    fn from(e: EcdhError) -> Self {
        match e {
            EcdhError::UnknownAlgorithm => Self::UnknownMode,
            _ => Self::CryptoError,
        }
    }
}
