use libcrux_ml_dsa::ml_dsa_44;
use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[inline(never)]
fn keygen(seed: [u8; 32]) -> ml_dsa_44::MLDSA44KeyPair {
    ml_dsa_44::generate_key_pair(seed)
}

#[inline(never)]
fn sign(
    signing_key: &ml_dsa_44::MLDSA44SigningKey,
    message: &[u8],
    randomness: [u8; 32],
) -> ml_dsa_44::MLDSA44Signature {
    ml_dsa_44::sign(signing_key, message, randomness)
}

#[inline(never)]
fn verify(
    verification_key: &ml_dsa_44::MLDSA44VerificationKey,
    message: &[u8],
    signature: &ml_dsa_44::MLDSA44Signature,
) -> Result<(), libcrux_ml_dsa::VerificationError> {
    ml_dsa_44::verify(verification_key, message, signature)
}

fn main() -> Result<(), libcrux_ml_dsa::VerificationError> {
    let key_generation_seed = random_array();
    let signing_randomness = random_array();
    let message = b"the quick brown fox jumps over the lazy dog";

    let key_pair = keygen(key_generation_seed);
    let signature = sign(&key_pair.signing_key, message, signing_randomness);

    verify(&key_pair.verification_key, message, &signature)
}
