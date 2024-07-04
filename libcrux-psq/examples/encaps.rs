use std::time::Duration;

use libcrux_psq::{generate_key_pair, Algorithm};
use rand::thread_rng;

fn main() {
    let mut rng = thread_rng();
    let mlkem_keypair = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();

    for _ in 0..100_000 {
        let _ = core::hint::black_box(mlkem_keypair.1.send_psk(
            b"size context",
            Duration::from_secs(3600),
            &mut rng,
        ));
    }
}
