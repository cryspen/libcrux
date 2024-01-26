#![no_main]
use libfuzzer_sys::fuzz_target;

use libcrux::kem::{self, Algorithm};

mod fuzz_rng;
use fuzz_rng::FuzzRng;

mod implicit_rejection_util;
use implicit_rejection_util::*;

fuzz_target!(|data: &[u8]| {
    let mut rng = FuzzRng::new(data);

    if let Ok((secret_key, public_key)) = kem::key_gen(Algorithm::MlKem1024, &mut rng) {
        if let Ok((_, ciphertext)) = public_key.encapsulate(&mut rng) {
            let ciphertext = modify_ciphertext(Algorithm::MlKem1024, &mut rng, ciphertext);
            let shared_secret_decapsulated = ciphertext.decapsulate(&secret_key).unwrap();

            let secret_key = modify_secret_key(Algorithm::MlKem1024, &mut rng, secret_key, true);
            let shared_secret_decapsulated_1 = ciphertext.decapsulate(&secret_key).unwrap();

            assert_ne!(
                shared_secret_decapsulated.encode(),
                shared_secret_decapsulated_1.encode()
            );

            assert_eq!(
                shared_secret_decapsulated_1.encode(),
                compute_implicit_rejection_shared_secret(ciphertext, secret_key)
            );
        } else {
            unreachable!("Error encapsulating")
        }
    } else {
        unreachable!("Error in key generation")
    }
});
