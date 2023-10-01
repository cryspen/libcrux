use libcrux::{
    digest::{self, sha3_256, shake256},
    kem::{self, Algorithm, Ct, PrivateKey},
};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg::{self, RngCore};
#[cfg(target_arch = "wasm32")]
use rand_core::{OsRng, RngCore};

const SHARED_SECRET_SIZE: usize = 32;
const SECRET_KEY_SIZE: usize = 2400;
const CIPHERTEXT_SIZE: u32 = 1088;

const SECRET_KEY_REJECTION_VALUE_POSITION: usize = SECRET_KEY_SIZE - SHARED_SECRET_SIZE;

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

impl_consistency!(consistency_512, Algorithm::Kyber512);
impl_consistency!(consistency_768, Algorithm::Kyber768);

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
        if let Ok((shared_secret, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
            let ciphertext = modify_ct(ciphertext, ciphertext_position, random_byte);
            let shared_secret_decapsulated = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret.encode(), shared_secret_decapsulated.encode());
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

fn modify_ct(ciphertext: Ct, ciphertext_position: usize, random_byte: u8) -> Ct {
    let mut encoded_ct = ciphertext.encode();
    encoded_ct[ciphertext_position] ^= random_byte;
    let ciphertext = Ct::decode(Algorithm::Kyber768, &encoded_ct).unwrap();
    ciphertext
}

fn compute_implicit_rejection_shared_secret(
    ciphertext: &[u8; CIPHERTEXT_SIZE as usize],
    implicit_rejection_value: [u8; SHARED_SECRET_SIZE],
) -> [u8; SHARED_SECRET_SIZE] {
    let mut to_hash = [0u8; SHARED_SECRET_SIZE + digest::digest_size(digest::Algorithm::Sha3_256)];

    to_hash[0..SHARED_SECRET_SIZE].copy_from_slice(&implicit_rejection_value);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&sha3_256(ciphertext));

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

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((shared_secret, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
            let secret_key = modify_sk(secret_key, secret_key_position, random_byte);
            let shared_secret_decapsulated = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret.encode(), shared_secret_decapsulated.encode());

            let ciphertext = raw_ct(ciphertext);
            let implicit_rejection_shared_secret = compute_implicit_rejection_shared_secret(
                &ciphertext,
                raw_sk(secret_key)[(SECRET_KEY_SIZE - SHARED_SECRET_SIZE)..]
                    .try_into()
                    .unwrap(),
            );

            assert_eq!(
                &shared_secret_decapsulated.encode(),
                &implicit_rejection_shared_secret
            );
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

fn raw_ct(ciphertext: Ct) -> [u8; 1088] {
    if let Ct::Kyber768(ct) = ciphertext {
        ct.into()
    } else {
        unreachable!()
    }
}

fn modify_sk(secret_key: PrivateKey, secret_key_position: usize, random_byte: u8) -> PrivateKey {
    let mut secret_key = raw_sk(secret_key);
    secret_key[secret_key_position] ^= random_byte;
    PrivateKey::Kyber768(secret_key.into())
}

fn raw_sk(secret_key: PrivateKey) -> [u8; 2400] {
    if let PrivateKey::Kyber768(ksk) = secret_key {
        ksk.into()
    } else {
        unreachable!();
    }
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

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut rng) {
        if let Ok((_, ciphertext)) = kem::encapsulate(&public_key, &mut rng) {
            let ciphertext = modify_ct(ciphertext, ciphertext_position, random_byte_for_ciphertext);
            let shared_secret_decapsulated = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            let secret_key = modify_sk(
                secret_key,
                SECRET_KEY_REJECTION_VALUE_POSITION + rejection_value_position,
                random_byte_for_secret_key,
            );
            let shared_secret_decapsulated_1 = kem::decapsulate(&ciphertext, &secret_key).unwrap();

            assert_ne!(
                shared_secret_decapsulated.encode(),
                shared_secret_decapsulated_1.encode()
            );

            let implicit_rejection_shared_secret = compute_implicit_rejection_shared_secret(
                &raw_ct(ciphertext),
                raw_sk(secret_key)[SECRET_KEY_REJECTION_VALUE_POSITION..]
                    .try_into()
                    .unwrap(),
            );
            assert_eq!(
                &shared_secret_decapsulated_1.encode(),
                &implicit_rejection_shared_secret
            );
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}
