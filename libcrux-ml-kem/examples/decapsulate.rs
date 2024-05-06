use libcrux_ml_kem::{kyber768, ENCAPS_SEED_SIZE, KEY_GENERATION_SEED_SIZE};
use rand::{rngs::OsRng, RngCore};

fn main() {
    let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
    OsRng.fill_bytes(&mut randomness);

    let key_pair = kyber768::generate_key_pair(randomness);
    let mut randomness = [0u8; ENCAPS_SEED_SIZE];
    OsRng.fill_bytes(&mut randomness);
    let (ct, _ss) = kyber768::encapsulate(key_pair.public_key(), randomness);

    for _ in 0..100_000 {
        let _ = kyber768::decapsulate(key_pair.private_key(), &ct);
    }
}
