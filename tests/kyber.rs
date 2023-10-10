use libcrux::{
    digest::{self, sha3_256, shake256},
    kem::{self, Algorithm, Ct, PrivateKey},
};

use rand::{CryptoRng, Rng};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::{OsRng, RngCore};

const SHARED_SECRET_SIZE: usize = 32;

macro_rules! impl_consistency {
    ($name:ident, $alg:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            #[cfg(not(target_arch = "wasm32"))]
            let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
            #[cfg(target_arch = "wasm32")]
            let mut rng = OsRng;

            if let Ok((secret_key, public_key)) = kem::key_gen($alg, &mut rng) {
                if let Ok((shared_secret, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
                    let shared_secret_decapsulated =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();
                    assert_eq!(shared_secret.encode(), shared_secret_decapsulated.encode());
                }
            }

            // If the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

fn modify_ciphertext(alg: Algorithm, rng: &mut (impl CryptoRng + Rng), ciphertext: Ct) -> Ct {
    let mut raw_ciphertext = ciphertext.encode();

    let mut random_u32: usize = rng.next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = random_u32 % raw_ciphertext.len();
    raw_ciphertext[position] ^= random_byte;

    Ct::decode(alg, &raw_ciphertext).unwrap()
}
macro_rules! impl_modified_ciphertext {
    ($name:ident, $alg:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            #[cfg(not(target_arch = "wasm32"))]
            let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
            #[cfg(target_arch = "wasm32")]
            let mut rng = OsRng;

            if let Ok((secret_key, public_key)) = kem::key_gen($alg, &mut rng) {
                if let Ok((shared_secret, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
                    let ciphertext = modify_ciphertext($alg, &mut rng, ciphertext);
                    let shared_secret_decapsulated =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();

                    assert_ne!(shared_secret.encode(), shared_secret_decapsulated.encode());
                }
            }
            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

fn modify_secret_key(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
    secret_key: PrivateKey,
    modify_implicit_rejection_value: bool,
) -> PrivateKey {
    let mut raw_secret_key = secret_key.encode();

    let mut random_u32: usize = rng.next_u32().try_into().unwrap();

    let mut random_byte: u8 = (random_u32 & 0xFF) as u8;
    if random_byte == 0 {
        random_byte += 1;
    }
    random_u32 >>= 8;

    let position = if modify_implicit_rejection_value {
        (raw_secret_key.len() - SHARED_SECRET_SIZE) + (random_u32 % SHARED_SECRET_SIZE)
    } else {
        random_u32 % raw_secret_key.len()
    };

    raw_secret_key[position] ^= random_byte;

    PrivateKey::decode(alg, &raw_secret_key).unwrap()
}
fn compute_implicit_rejection_shared_secret(
    ciphertext: Ct,
    secret_key: PrivateKey,
) -> [u8; SHARED_SECRET_SIZE] {
    let raw_secret_key = secret_key.encode();

    let mut to_hash = [0u8; SHARED_SECRET_SIZE + digest::digest_size(digest::Algorithm::Sha3_256)];

    to_hash[0..SHARED_SECRET_SIZE]
        .copy_from_slice(&raw_secret_key[raw_secret_key.len() - SHARED_SECRET_SIZE..]);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&sha3_256(&ciphertext.encode()));

    shake256(&to_hash)
}
macro_rules! impl_modified_secret_key {
    ($name:ident, $alg:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            #[cfg(not(target_arch = "wasm32"))]
            let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
            #[cfg(target_arch = "wasm32")]
            let mut rng = OsRng;

            if let Ok((secret_key, public_key)) = kem::key_gen($alg, &mut rng) {
                if let Ok((shared_secret, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
                    let secret_key = modify_secret_key($alg, &mut rng, secret_key, false);
                    let shared_secret_decapsulated =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();
                    assert_ne!(shared_secret.encode(), shared_secret_decapsulated.encode());

                    let secret_key = modify_secret_key($alg, &mut rng, secret_key, true);
                    let shared_secret_decapsulated =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();

                    assert_eq!(
                        shared_secret_decapsulated.encode(),
                        compute_implicit_rejection_shared_secret(ciphertext, secret_key)
                    );
                }
            }

            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

macro_rules! impl_modified_ciphertext_and_implicit_rejection_value {
    ($name:ident, $alg:expr) => {
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
        #[test]
        fn $name() {
            #[cfg(not(target_arch = "wasm32"))]
            let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
            #[cfg(target_arch = "wasm32")]
            let mut rng = OsRng;

            if let Ok((secret_key, public_key)) = kem::key_gen($alg, &mut rng) {
                if let Ok((_, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
                    let ciphertext = modify_ciphertext($alg, &mut rng, ciphertext);
                    let shared_secret_decapsulated =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();

                    let secret_key = modify_secret_key($alg, &mut rng, secret_key, true);
                    let shared_secret_decapsulated_1 =
                        kem::decapsulate(&ciphertext, &secret_key).unwrap();

                    assert_ne!(
                        shared_secret_decapsulated.encode(),
                        shared_secret_decapsulated_1.encode()
                    );

                    assert_eq!(
                        shared_secret_decapsulated_1.encode(),
                        compute_implicit_rejection_shared_secret(ciphertext, secret_key)
                    );
                }
            }

            // if the randomness was not enough for the rejection sampling step
            // in key-generation and encapsulation, simply return without
            // failing.
        }
    };
}

impl_consistency!(consistency_512, Algorithm::Kyber512);
impl_consistency!(consistency_768, Algorithm::Kyber768);
impl_consistency!(consistency_1024, Algorithm::Kyber1024);

impl_modified_ciphertext!(modified_ciphertext_512, Algorithm::Kyber512);
impl_modified_ciphertext!(modified_ciphertext_768, Algorithm::Kyber768);
impl_modified_ciphertext!(modified_ciphertext_1024, Algorithm::Kyber1024);

impl_modified_secret_key!(modified_secret_key_512, Algorithm::Kyber512);
impl_modified_secret_key!(modified_secret_key_768, Algorithm::Kyber768);
impl_modified_secret_key!(modified_secret_key_1024, Algorithm::Kyber1024);

impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_512,
    Algorithm::Kyber512
);
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_768,
    Algorithm::Kyber768
);
impl_modified_ciphertext_and_implicit_rejection_value!(
    modified_ciphertext_and_implicit_rejection_value_1024,
    Algorithm::Kyber1024
);
