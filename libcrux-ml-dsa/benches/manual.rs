use std::time::{Duration, Instant};

use libcrux_ml_dsa::{
    ml_dsa_44::{self, MLDSA44KeyPair, MLDSA44Signature},
    ml_dsa_65::{self, MLDSA65KeyPair, MLDSA65Signature},
    ml_dsa_87::{self, MLDSA87KeyPair, MLDSA87Signature},
    KEY_GENERATION_RANDOMNESS_SIZE, SIGNING_RANDOMNESS_SIZE,
};
use rand::{rngs::OsRng, RngCore};

fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

fn print_time(label: &str, d: Duration) {
    let micros = d.as_micros();
    let time = if micros < (1_000 * ITERATIONS as u128) {
        format!("{} μs", micros / ITERATIONS as u128)
    } else if micros < (1_000_000 * ITERATIONS as u128) {
        format!(
            "{:.2} ms",
            (micros as f64 / (1_000_f64 * ITERATIONS as f64))
        )
    } else {
        format!(
            "{:.2}s",
            (micros as f64 / (1_000_000_f64 * ITERATIONS as f64))
        )
    };
    let space = if label.len() < 6 {
        "\t\t".to_string()
    } else {
        "\t".to_string()
    };

    println!("{label}:{space}{time}");
}

const ITERATIONS: usize = 100_000;
const WARMUP_ITERATIONS: usize = 1_000;

// A benchmarking macro to avoid copying memory and skewing the results.
macro_rules! bench {
    ($label:literal, $variant:literal, $input:expr, $setup:expr, $routine:expr) => {{
        let mut time = Duration::ZERO;

        // Warmup
        for _ in 0..WARMUP_ITERATIONS {
            let input = $setup($input);
            $routine(input);
        }

        // Benchmark
        for _ in 0..ITERATIONS {
            let input = $setup($input);

            let start = Instant::now();
            core::hint::black_box($routine(input));
            let end = Instant::now();

            time += end.duration_since(start);
        }
        print_time(concat!($label, " ", $variant), time);
    }};
}

macro_rules! bench_group {
    ($variant:literal, $mod:ident, $keypair_t:ident, $signature_t:ident) => {{
        bench!(
            "KeyGen",
            $variant,
            (),
            |()| {
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = random_array();
                key_generation_seed
            },
            |key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE]| {
                $mod::generate_key_pair(key_generation_seed)
            }
        );
        bench!(
            "Sign",
            $variant,
            (),
            |()| {
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = random_array();
                let signing_randomness: [u8; SIGNING_RANDOMNESS_SIZE] = random_array();
                let message = random_array::<1023>();
                let keypair = $mod::generate_key_pair(key_generation_seed);

                (keypair, message, signing_randomness)
            },
            |(keypair, message, signing_randomness): (
                $keypair_t,
                [u8; 1023],
                [u8; SIGNING_RANDOMNESS_SIZE]
            )| { $mod::sign(&keypair.signing_key, &message, signing_randomness) }
        );

        bench!(
            "Verify",
            $variant,
            (),
            |()| {
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = random_array();
                let signing_randomness: [u8; SIGNING_RANDOMNESS_SIZE] = random_array();
                let message = random_array::<1023>();
                let keypair = $mod::generate_key_pair(key_generation_seed);
                let signature = $mod::sign(&keypair.signing_key, &message, signing_randomness);
                (keypair, message, signature)
            },
            |(keypair, message, signature): ($keypair_t, [u8; 1023], $signature_t)| {
                $mod::verify(&keypair.verification_key, &message, &signature).unwrap()
            }
        );

        println!("");
    }};
}

fn main() {
    bench_group!("44", ml_dsa_44, MLDSA44KeyPair, MLDSA44Signature);
    bench_group!("65", ml_dsa_65, MLDSA65KeyPair, MLDSA65Signature);
    bench_group!("87", ml_dsa_87, MLDSA87KeyPair, MLDSA87Signature);
}
