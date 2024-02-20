#![no_main]

use libcrux::kem::{self, Algorithm, PublicKey};
use libfuzzer_sys::fuzz_target;

mod fuzz_rng;
use fuzz_rng::FuzzRng;

fuzz_target!(|data: &[u8]| {
    let mut rng = FuzzRng::new(data);

    if let Ok((_, public_key)) = kem::key_gen(Algorithm::MlKem768, &mut rng) {
        let encoded = public_key.encode();
        let _ = PublicKey::decode(Algorithm::MlKem768, &encoded).unwrap();
    } else {
        eprintln!("Error in key generation {:x?}", data);
    }
});
