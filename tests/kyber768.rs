use libcrux::{
    digest::{self, sha3_256, shake256},
    kem::{self, Algorithm},
};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg::{self, RngCore};
#[cfg(target_arch = "wasm32")]
use rand_core::{OsRng, RngCore};

const SHARED_SECRET_SIZE: usize = 32;
const SECRET_KEY_SIZE: usize = 2400;
const CIPHERTEXT_SIZE: u32 = 1088;

const SECRET_KEY_REJECTION_VALUE_POSITION: usize = SECRET_KEY_SIZE - SHARED_SECRET_SIZE;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn consistency() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((shared_secret, ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, public_key, &mut rng)
        {
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();
            assert_eq!(shared_secret, shared_secret_decapsulated);
        }
    }

    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn modified_ciphertext() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let random_u32 = rng.next_u32();
    let mut random_byte: u8 = (random_u32 & 0xFF).try_into().unwrap();
    if random_byte == 0 {
        random_byte += 1;
    }

    let ciphertext_position: usize = (random_u32 % CIPHERTEXT_SIZE).try_into().unwrap();

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((shared_secret, mut ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut rng)
        {
            ciphertext[ciphertext_position] ^= random_byte;
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret, shared_secret_decapsulated);
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

fn compute_implicit_rejection_shared_secret(
    ciphertext: [u8; CIPHERTEXT_SIZE as usize],
    implicit_rejection_value: [u8; SHARED_SECRET_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    let mut to_hash = [0u8; SHARED_SECRET_SIZE + digest::digest_size(digest::Algorithm::Sha3_256)];

    to_hash[0..SHARED_SECRET_SIZE].copy_from_slice(&implicit_rejection_value);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&sha3_256(&ciphertext));

    shake256(&to_hash)
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn modified_secret_key() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let random_u32 = rng.next_u32();

    let mut random_byte: u8 = (random_u32 & 0xFF).try_into().unwrap();
    if random_byte == 0 {
        random_byte += 1;
    }

    let secret_key_position: usize = ((random_u32 >> 8) % (SECRET_KEY_SIZE as u32 - 32)) as usize;

    if let Ok((mut secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((shared_secret, ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut rng)
        {
            secret_key[secret_key_position] ^= random_byte;
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret, shared_secret_decapsulated);

            let implicit_rejection_shared_secret = compute_implicit_rejection_shared_secret(
                ciphertext.try_into().unwrap(),
                secret_key[(SECRET_KEY_SIZE - SHARED_SECRET_SIZE)..]
                    .try_into()
                    .unwrap(),
            );

            assert_eq!(shared_secret_decapsulated, implicit_rejection_shared_secret);
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn modified_ciphertext_and_implicit_rejection_value() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let random_u32 = rng.next_u32();

    let mut random_byte_for_ciphertext: u8 = (random_u32 & 0xFF).try_into().unwrap();
    if random_byte_for_ciphertext == 0 {
        random_byte_for_ciphertext += 1;
    }

    let ciphertext_position: usize = ((random_u32 >> 8) % CIPHERTEXT_SIZE).try_into().unwrap();

    let random_u32 = rng.next_u32();

    let mut random_byte_for_secret_key: u8 = (random_u32 & 0xFF).try_into().unwrap();
    if random_byte_for_secret_key == 0 {
        random_byte_for_secret_key += 1;
    }

    let rejection_value_position: usize = ((random_u32 >> 8) % SHARED_SECRET_SIZE as u32)
        .try_into()
        .unwrap();

    if let Ok((mut secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((_, mut ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut rng)
        {
            ciphertext[ciphertext_position] ^= random_byte_for_ciphertext;
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            secret_key[SECRET_KEY_REJECTION_VALUE_POSITION + rejection_value_position] ^=
                random_byte_for_secret_key;
            let shared_secret_decapsulated_1 =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret_decapsulated, shared_secret_decapsulated_1);

            let implicit_rejection_shared_secret = compute_implicit_rejection_shared_secret(
                ciphertext.try_into().unwrap(),
                secret_key[SECRET_KEY_REJECTION_VALUE_POSITION..]
                    .try_into()
                    .unwrap(),
            );
            assert_eq!(
                shared_secret_decapsulated_1,
                implicit_rejection_shared_secret
            );
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}
