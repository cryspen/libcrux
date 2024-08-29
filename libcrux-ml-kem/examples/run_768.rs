use libcrux_ml_kem::mlkem768;
use rand::{rngs::OsRng, RngCore as _};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[inline(never)]
fn keygen(randomness: [u8; 64]) -> mlkem768::MlKem768KeyPair {
    mlkem768::generate_key_pair(randomness)
}

#[inline(never)]
fn encaps(
    public_key: &mlkem768::MlKem768PublicKey,
    randomness: [u8; 32],
) -> (
    mlkem768::MlKem768Ciphertext,
    libcrux_ml_kem::MlKemSharedSecret,
) {
    mlkem768::encapsulate(public_key, randomness)
}

#[inline(never)]
fn decaps(
    private_key: &mlkem768::MlKem768PrivateKey,
    ciphertext: &mlkem768::MlKem768Ciphertext,
) -> libcrux_ml_kem::MlKemSharedSecret {
    mlkem768::decapsulate(private_key, ciphertext)
}

fn main() {
    let key_generation_randomness = random_array();
    let encaps_randomness = random_array();

    let key_pair = keygen(key_generation_randomness);
    let (ciphertext, shared_secret_a) = encaps(key_pair.public_key(), encaps_randomness);
    let shared_secret_b = decaps(key_pair.private_key(), &ciphertext);

    assert_eq!(shared_secret_a, shared_secret_b)
}
