// Allow dead code for now.
// The libjade code here isn't verified yet and thus isn't used.
#![allow(dead_code)]

use libjade_sys::{
    jade_kem_kyber_kyber768_amd64_ref_dec, jade_kem_kyber_kyber768_amd64_ref_enc_derand,
    jade_kem_kyber_kyber768_amd64_ref_keypair_derand,
};

type Kyber768KeypairSeed = [u8; 64];

type Kyber768PublicKey = [u8; 1184];
type Kyber768SecretKey = [u8; 2400];

type Kyber768EncapsulateSeed = [u8; 32];

type Kyber768Ciphertext = [u8; 1088];
type Kyber768SharedSecret = [u8; 32];

fn kyber768_keypair_derand_ref(
    seed: Kyber768KeypairSeed,
) -> Result<(Kyber768PublicKey, Kyber768SecretKey), &'static str> {
    let mut public_key: Kyber768PublicKey = [0; 1184];
    let mut secret_key: Kyber768SecretKey = [0; 2400];

    let r = unsafe {
        jade_kem_kyber_kyber768_amd64_ref_keypair_derand(
            public_key.as_mut_ptr(),
            secret_key.as_mut_ptr(),
            seed.as_ptr() as _,
        )
    };

    if r != 0 {
        Err("Error while generating kyber768 keypair.")
    } else {
        Ok((public_key, secret_key))
    }
}

fn kyber768_enc_derand_ref(
    public_key: Kyber768PublicKey,
    seed: Kyber768EncapsulateSeed,
) -> Result<(Kyber768Ciphertext, Kyber768SharedSecret), &'static str> {
    let mut ciphertext: Kyber768Ciphertext = [0; 1088];
    let mut shared_secret = Kyber768SharedSecret::default();

    let r = unsafe {
        jade_kem_kyber_kyber768_amd64_ref_enc_derand(
            ciphertext.as_mut_ptr(),
            shared_secret.as_mut_ptr(),
            public_key.as_ptr() as _,
            seed.as_ptr() as _,
        )
    };

    if r != 0 {
        Err("Error while running kyber768 derandomized encapsulated.")
    } else {
        Ok((ciphertext, shared_secret))
    }
}

fn kyber768_dec_ref(
    ciphertext: Kyber768Ciphertext,
    secret_key: Kyber768SecretKey,
) -> Result<Kyber768SharedSecret, &'static str> {
    let mut shared_secret = Kyber768SharedSecret::default();

    let r = unsafe {
        jade_kem_kyber_kyber768_amd64_ref_dec(
            shared_secret.as_mut_ptr(),
            ciphertext.as_ptr() as _,
            secret_key.as_ptr() as _,
        )
    };

    if r != 0 {
        Err("Error while running kyber768 decapsulate.")
    } else {
        Ok(shared_secret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consistency_test() {
        let _ = pretty_env_logger::try_init();

        let keypair_seed = [0u8; 64];
        let enc_seed = [0u8; 32];

        let (public_key, secret_key) = kyber768_keypair_derand_ref(keypair_seed).unwrap();

        let (ciphertext, shared_secret) = kyber768_enc_derand_ref(public_key, enc_seed).unwrap();

        let shared_secret_decapsulated = kyber768_dec_ref(ciphertext, secret_key).unwrap();

        assert_eq!(shared_secret_decapsulated, shared_secret);
    }
}
