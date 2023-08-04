use libcrux::kem::{self, Algorithm};
use libcrux::drbg::Drbg;
use libcrux::digest;

#[test]
fn consistency() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::Kyber768, &mut drbg) {
        if let Ok((shared_secret, ciphertext)) = kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg) {

            let shared_secret_decapsulated = kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key).unwrap();
            assert_eq!(shared_secret, shared_secret_decapsulated);
        }
    }

    // If the randomness was not enough for the rejection sampling step
    // in key-generation and encapsulation, simply return without
    // failing.
}

