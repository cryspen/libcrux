mod test_util;

use libcrux::kem::{self, Algorithm};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xkyber_selftest() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let (skr, pkr) = kem::key_gen(Algorithm::X25519MlKem768Draft00, &mut rng).unwrap();

    let (ss, ct) = pkr.encapsulate(&mut rng).unwrap();
    let rss = ct.decapsulate(&skr).unwrap();

    assert_eq!(rss.encode(), ss.encode());
}
