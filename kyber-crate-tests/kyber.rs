use libcrux_kyber::kyber768::*;
use rand::rngs::OsRng;
use rand::RngCore;

#[test]
fn consistency_768() {
    let mut rng = OsRng;
    let mut randomness = [0u8; 64];
    rng.fill_bytes(&mut randomness);

    let kp = generate_key_pair(randomness);
    let mut randomness = [0u8; 32];
    rng.fill_bytes(&mut randomness);

    let ct = encapsulate(kp.public_key(), randomness);
    let shared_secret_decapsulated = decapsulate(kp.private_key(), &ct.0);

    assert_eq!(shared_secret_decapsulated, ct.1);
}
