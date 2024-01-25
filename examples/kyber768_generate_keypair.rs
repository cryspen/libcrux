use libcrux::kem;

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;

fn main() {
    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    for _i in 0..100000 {
        let (_secret_key, _public_key) = kem::key_gen(kem::Algorithm::MlKem768, &mut rng).unwrap();
    }
}
