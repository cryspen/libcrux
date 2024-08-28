use libcrux_ml_kem::{mlkem512, KEY_GENERATION_SEED_SIZE};
use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[inline(never)]
fn keygen(randomness: [u8; 64]) -> mlkem512::MlKem512KeyPair {
    mlkem512::generate_key_pair(randomness)
}

#[inline(never)]
fn encaps(
    public_key: &mlkem512::MlKem512PublicKey,
    randomness: [u8; 32],
) -> (
    mlkem512::MlKem512Ciphertext,
    libcrux_ml_kem::MlKemSharedSecret,
) {
    mlkem512::encapsulate(public_key, randomness)
}

#[inline(never)]
fn decaps(
    private_key: &mlkem512::MlKem512PrivateKey,
    ciphertext: &mlkem512::MlKem512Ciphertext,
) -> libcrux_ml_kem::MlKemSharedSecret {
    mlkem512::decapsulate(private_key, ciphertext)
}
fn main() {
    let key_generation_randomness = random_array();
    let encaps_randomness = random_array();

    let key_pair = keygen(key_generation_randomness);
    let (ciphertext, shared_secret_a) = encaps(key_pair.public_key(), encaps_randomness);
    let shared_secret_b = decaps(key_pair.private_key(), &ciphertext);

    assert_eq!(shared_secret_a, shared_secret_b)
}
