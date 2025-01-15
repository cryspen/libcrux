use libcrux_secrets::*;
use libcrux_sha3::*;
use rand::RngCore;

#[allow(unused)]
pub(crate) fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = rand::rngs::OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[allow(unused)]
pub(crate) fn random_vec<const L: usize>() -> Vec<u8> {
    let mut rng = rand::rngs::OsRng;
    let mut seed = vec![0x13; L];
    // rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[allow(unused)]
pub(crate) fn print_time(label: &str, d: std::time::Duration) {
    let micros = d.as_micros();
    let time = if micros < MILLI_PER_ITERATION_THRESHOLD {
        format!("{} μs", micros / ITERATIONS as u128)
    } else if micros < SECOND_PER_ITERATION_THRESHOLD {
        format!(
            "{:.2} ms",
            (micros as f64 / (MICROS_PER_MILLI * ITERATIONS as f64))
        )
    } else {
        format!(
            "{:.2}s",
            (micros as f64 / (MICROS_PER_SECOND * ITERATIONS as f64))
        )
    };
    let space = if label.len() < 6 {
        "\t\t".to_string()
    } else {
        "\t".to_string()
    };

    println!("{label}:{space}{time}");
}

pub(crate) const ITERATIONS: usize = 1_000;
#[allow(unused)]
pub(crate) const WARMUP_ITERATIONS: usize = 1_000;

pub(crate) const MICROS_PER_MILLI: f64 = 1_000.0;
pub(crate) const MICROS_PER_SECOND: f64 = 1_000_000.0;
pub(crate) const MILLI_PER_ITERATION_THRESHOLD: u128 = 1_000 * ITERATIONS as u128;
pub(crate) const SECOND_PER_ITERATION_THRESHOLD: u128 = 1_000_000 * ITERATIONS as u128;

// A benchmarking macro to avoid copying memory and skewing the results.
#[macro_export]
macro_rules! bench {
    ($label:literal, $variant:literal, $input:expr, $setup:expr, $routine:expr) => {{
        let mut time = std::time::Duration::ZERO;

        // Warmup
        for _ in 0..WARMUP_ITERATIONS {
            let input = $setup($input);
            let _ = $routine(input);
        }

        // Benchmark
        for _ in 0..ITERATIONS {
            let input = $setup($input);

            let start = std::time::Instant::now();
            let _ = core::hint::black_box($routine(input));
            let end = std::time::Instant::now();

            time += end.duration_since(start);
        }
        print_time(concat!($label, " ", $variant), time);
    }};
}

pub fn fmt(x: usize) -> String {
    let base = (x as f64).log(1024f64).floor() as usize;
    let suffix = ["", "KB", "MB", "GB"];
    format!("{} {}", x >> (10 * base), suffix[base])
}

fn main() {
    bench!(
        "Sha3",
        256,
        (),
        |()| { random_vec::<{ 1024 * 1024 * 10 }>() },
        |data: Vec<u8>| {
            let _d: Sha3_256Digest = hash(Algorithm::Sha256, (&data).as_secret());
        }
    );
}
