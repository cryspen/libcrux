#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
use libcrux::ecdh::{self, key_gen};
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn derive_rand() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let (private_a, public_a) = key_gen(ecdh::Algorithm::P256, &mut rng).unwrap();
    let (private_b, public_b) = key_gen(ecdh::Algorithm::P256, &mut rng).unwrap();

    let shared_a = ecdh::derive(ecdh::Algorithm::P256, &public_b, &private_a).unwrap();
    let shared_b = ecdh::derive(ecdh::Algorithm::P256, &public_a, &private_b).unwrap();
    eprintln!("a = {}", hex::encode(&private_a));
    eprintln!("A = {}", hex::encode(&public_a));
    eprintln!("b = {}", hex::encode(&private_b));
    eprintln!("B = {}", hex::encode(&public_b));
    eprintln!("shared a = {}", hex::encode(&shared_a));
    eprintln!("shared b = {}", hex::encode(&shared_b));
    assert_eq!(shared_a, shared_b);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn derive() {
    let private_a =
        hex::decode("0d5fb987f5d937379bd350a25e2903785f0750de4226bc7af06a9f6341ad1569").unwrap();
    let public_a = hex::decode("03f4b6536e2a4cb571df5a294d18e628fc69bf0db031af2681f2786e9aab993c93255f58e1aaa6664269622df89d621cc1a5c4848fe8b237b08a391b0b761a6d").unwrap();
    let private_b =
        hex::decode("17e1ebef41df589d0483aa0ec4302abbe2dcc3da2e87211e09f36eb40131f304").unwrap();
    let public_b = hex::decode("de9d41b163a0804b968b37ba21caec240e8191977ddf4d0594d656289a6cf96b260caee19e0e3b03bfa11361c9f02027c625a9f1ad4c832e0eb4684a8b32237b").unwrap();

    let public_a_comp = ecdh::secret_to_public(ecdh::Algorithm::P256, &private_a).unwrap();
    assert_eq!(public_a, public_a_comp);
    let public_b_comp = ecdh::secret_to_public(ecdh::Algorithm::P256, &private_b).unwrap();
    assert_eq!(public_b, public_b_comp);

    let expected_shared = hex::decode("9839a5cf9b295e385e274dad44a3acf9d285bfc7ba8cfbe36c132f1c6967ab081ce2d1405f436ba09810a9c89b6a407ca3aec13519dec058d487e89520d3ac5e").unwrap();

    let shared_a = ecdh::derive(ecdh::Algorithm::P256, &public_b, &private_a).unwrap();
    let shared_b = ecdh::derive(ecdh::Algorithm::P256, &public_a, &private_b).unwrap();
    eprintln!("a = {}", hex::encode(&private_a));
    eprintln!("A = {}", hex::encode(&public_a));
    eprintln!("b = {}", hex::encode(&private_b));
    eprintln!("B = {}", hex::encode(&public_b));
    eprintln!("shared a = {}", hex::encode(&shared_a));
    eprintln!("shared b = {}", hex::encode(&shared_b));
    assert_eq!(shared_a, shared_b);
    assert_eq!(expected_shared, shared_b);
}
