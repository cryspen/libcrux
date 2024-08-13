use std::time::{Duration, Instant};

use libcrux_ml_dsa::ml_dsa_65::{self, MLDSA65KeyPair};
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
    ($input:expr, $setup:expr, $routine:expr) => {{
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

        time
    }};
}

fn main() {
    let time = bench!(
        (),
        |()| {
            // FIXME: expose the constants
            let key_generation_seed: [u8; 32] = random_array();
            let signing_randomness: [u8; 32] = random_array();
            let message = random_array::<1023>();
            let keypair = ml_dsa_65::generate_key_pair(key_generation_seed);

            (keypair, message, signing_randomness)
        },
        |(keypair, message, signing_randomness): (MLDSA65KeyPair, [u8; 1023], [u8; 32])| {
            ml_dsa_65::sign(&keypair.signing_key, &message, signing_randomness)
        }
    );
    print_time("Sign 65", time);
}
