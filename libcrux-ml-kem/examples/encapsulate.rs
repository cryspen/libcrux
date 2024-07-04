use libcrux_ml_kem::{mlkem768, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
use rand::{rngs::OsRng, RngCore};

fn main() {
    let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut randomness);

    let key_pair = mlkem768::generate_key_pair(randomness);

    let mut randomness = [0u8; ENCAPS_SEED_SIZE];
    for _ in 0..100_000 {
        OsRng.fill_bytes(&mut randomness);
        let _ = mlkem768::encapsulate(key_pair.public_key(), randomness);
    }
}
