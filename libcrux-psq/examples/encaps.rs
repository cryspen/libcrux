use std::time::Duration;

use libcrux_psq::{
    ecdh_binder::send_ecdh_bound_psq,
    psq::{generate_key_pair, Algorithm},
};
use rand::thread_rng;

fn main() {
    let mut rng = thread_rng();
    let mlkem_keypair = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
    let (_receiver_dh_sk, receiver_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
    let (initiator_dh_sk, _initiator_dh_pk) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();

    for _ in 0..100_000 {
        let _ = core::hint::black_box(send_ecdh_bound_psq(
            &mlkem_keypair.1,
            &receiver_dh_pk,
            &initiator_dh_sk,
            Duration::from_secs(3600),
            b"example context",
            &mut rng,
        ));
    }
}
