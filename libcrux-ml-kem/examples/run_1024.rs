use libcrux_ml_kem::mlkem1024;
use rand::{rngs::OsRng, RngCore as _};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[inline(never)]
// fn keygen(randomness: [u8; 64]) -> libcrux_ml_kem::MlKemKeyPair<3168, 1568> { // <- this works
fn keygen(randomness: [u8; 64]) -> mlkem1024::MlKem1024KeyPair {
    mlkem1024::generate_key_pair(randomness)
}

#[inline(never)]
fn encaps(
    public_key: &mlkem1024::MlKem1024PublicKey,
    randomness: [u8; 32],
) -> (
    mlkem1024::MlKem1024Ciphertext,
    libcrux_ml_kem::MlKemSharedSecret,
) {
    mlkem1024::encapsulate(public_key, randomness)
}

#[inline(never)]
fn decaps(
    private_key: &mlkem1024::MlKem1024PrivateKey,
    ciphertext: &mlkem1024::MlKem1024Ciphertext,
) -> libcrux_ml_kem::MlKemSharedSecret {
    mlkem1024::decapsulate(private_key, ciphertext)
}

fn main() {
    let key_generation_randomness = random_array();
    let encaps_randomness = random_array();

    let key_pair = mlkem1024::generate_key_pair(key_generation_randomness);
    let (ciphertext, shared_secret_a) =
        mlkem1024::encapsulate(key_pair.public_key(), encaps_randomness);
    let shared_secret_b = mlkem1024::decapsulate(key_pair.private_key(), &ciphertext);

    assert_eq!(shared_secret_a, shared_secret_b)
}
