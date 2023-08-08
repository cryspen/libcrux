use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::drbg::RngCore;
use libcrux::kem::{self, Algorithm};

#[test]
fn consistency() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut drbg) {
        if let Ok((shared_secret, ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg)
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

#[test]
fn modified_ciphertext() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    let random_u32 = drbg.next_u32();
    let random_byte: u8 = (random_u32 & 0xFF).try_into().unwrap();

    let ciphertext_position: usize = (random_u32 % 1088).try_into().unwrap();

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut drbg) {
        if let Ok((shared_secret, mut ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg)
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

#[test]
fn modified_secret_key() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    let random_u32 = drbg.next_u32();

    let random_byte: u8 = (random_u32 & 0xFF).try_into().unwrap();

    let secret_key_position: usize = ((random_u32 >> 8) % (2400 - 32)).try_into().unwrap();

    if let Ok((mut secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut drbg) {
        if let Ok((shared_secret, ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg)
        {
            secret_key[secret_key_position] ^= random_byte;
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret, shared_secret_decapsulated);
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

#[test]
fn modified_ciphertext_and_implicit_rejection_value() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    let random_u32 = drbg.next_u32();
    let random_byte_for_ciphertext: u8 = (random_u32 & 0xFF).try_into().unwrap();
    let ciphertext_position: usize = ((random_u32 >> 8) % 1088).try_into().unwrap();

    let random_u32 = drbg.next_u32();
    let random_byte_for_secret_key: u8 = (random_u32 & 0xFF).try_into().unwrap();
    let secret_key_position: usize = ((random_u32 >> 8) % 32).try_into().unwrap();

    if let Ok((mut secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut drbg) {
        if let Ok((_, mut ciphertext)) =
            kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg)
        {
            ciphertext[ciphertext_position] ^= random_byte_for_ciphertext;
            let shared_secret_decapsulated =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            secret_key[(2400 - 32) + secret_key_position] ^= random_byte_for_secret_key;
            let shared_secret_decapsulated_1 =
                kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();

            assert_ne!(shared_secret_decapsulated, shared_secret_decapsulated_1);
        }
    }
    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}
