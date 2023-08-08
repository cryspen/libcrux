use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::kem;

fn main() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();

    for _i in 0..100000 {
        let (_secret_key, _public_key) = kem::key_gen(kem::Algorithm::Kyber768, &mut drbg).unwrap();
    }
}
