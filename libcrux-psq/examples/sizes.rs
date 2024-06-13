use chrono::Duration;
use libcrux_psq::*;
use rand::{self, thread_rng};

fn main() {
    let mut rng = thread_rng();
    let mlkem_keypair = generate_key_pair(Algorithm::MlKem768, &mut rng).unwrap();
    let x25519_keypair = generate_key_pair(Algorithm::X25519, &mut rng).unwrap();
    let xwing_keypair = generate_key_pair(Algorithm::XWingKemDraft02, &mut rng).unwrap();
    let classic_mceliece_keypair = generate_key_pair(Algorithm::ClassicMcEliece, &mut rng).unwrap();

    let mlkem_message = mlkem_keypair
        .1
        .send_psk(b"size context", Duration::hours(1), &mut rng)
        .unwrap();
    let x25519_message = x25519_keypair
        .1
        .send_psk(b"size context", Duration::hours(1), &mut rng)
        .unwrap();
    let xwing_message = xwing_keypair
        .1
        .send_psk(b"size context", Duration::hours(1), &mut rng)
        .unwrap();
    let classic_mceliece_message = classic_mceliece_keypair
        .1
        .send_psk(b"size context", Duration::hours(1), &mut rng)
        .unwrap();

    println!("ML-KEM-768:");
    println!("  Public key size (bytes): {}", mlkem_keypair.1.size());
    println!("  Message size (bytes): {}", mlkem_message.1.size());
    println!(
        "  including ciphertext size (bytes): {}",
        mlkem_message.1.ct_size()
    );

    println!("X25519:");
    println!("  Public key size (bytes): {}", x25519_keypair.1.size());
    println!("  Message size (bytes): {}", x25519_message.1.size());
    println!(
        "  including ciphertext size (bytes): {}",
        x25519_message.1.ct_size()
    );

    println!("XWingKemDraft02:");
    println!("  Public key size (bytes): {}", xwing_keypair.1.size());
    println!("  Message size (bytes): {}", xwing_message.1.size());
    println!(
        "  including ciphertext size (bytes): {}",
        xwing_message.1.ct_size()
    );

    println!("Classic McEliece:");
    println!(
        "  Public key size (bytes): {}",
        classic_mceliece_keypair.1.size()
    );
    println!(
        "  Message size (bytes): {}",
        classic_mceliece_message.1.size()
    );
    println!(
        "  including ciphertext size (bytes): {}",
        classic_mceliece_message.1.ct_size()
    );
}
