use std::convert::TryInto;

use x25519_dalek;

use hpke::kem;

mod test_util;
use test_util::*;

#[test]
fn test_x25519_kem_self() {
    let kem = kem::Kem::new(kem::Mode::DhKem25519);
    let sk_r = random(32);
    let pk_r = x25519_dalek::x25519(
        sk_r[..]
            .try_into()
            .expect("secret key has incorrect length"),
        x25519_dalek::X25519_BASEPOINT_BYTES,
    );
    let (s1, enc) = kem.encaps(&pk_r);
    let s2 = kem.decaps(&enc, &sk_r);
    assert_eq!(s1, s2);
}
