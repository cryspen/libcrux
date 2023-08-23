use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::kem;

fn main() {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
    let (_secret_key, public_key) = kem::key_gen(kem::Algorithm::Kyber768, &mut drbg).unwrap();

    for _i in 0..100000 {
        let (_shared_secret, _ciphertext) =
            kem::encapsulate(kem::Algorithm::Kyber768, &public_key, &mut drbg).unwrap();
    }
}
