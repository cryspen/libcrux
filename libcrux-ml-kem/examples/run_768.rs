use libcrux_ml_kem::{mlkem768, KEY_GENERATION_SEED_SIZE};
use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

fn main() {
    let key_generation_randomness = random_array();
    let encaps_randomness = random_array();

    let key_pair = mlkem768::generate_key_pair(key_generation_randomness);
    let (ciphertext, shared_secret_a) =
        mlkem768::encapsulate(key_pair.public_key(), encaps_randomness);
    let shared_secret_b = mlkem768::decapsulate(key_pair.private_key(), &ciphertext);

    assert_eq!(shared_secret_a, shared_secret_b)
}
