use libcrux::{
    drbg,
    ecdh::{self, key_gen},
};

#[test]
fn derive() {
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();

    let (private_a, public_a) = key_gen(ecdh::Algorithm::P256, &mut rng).unwrap();
    let (private_b, public_b) = key_gen(ecdh::Algorithm::P256, &mut rng).unwrap();

    let shared_a = ecdh::derive(ecdh::Algorithm::P256, &public_b, &private_a).unwrap();
    let shared_b = ecdh::derive(ecdh::Algorithm::P256, &public_a, &private_b).unwrap();
    assert_eq!(shared_a, shared_b);
}
