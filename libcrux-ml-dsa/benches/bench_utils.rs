use rand::RngCore;

#[allow(unused)]
pub(crate) fn random_array<const L: usize>() -> [u8; L] {
    let mut rng = rand::rngs::OsRng;
    let mut seed = [0; L];
    rng.try_fill_bytes(&mut seed).unwrap();
    seed
}

#[allow(unused)]
pub(crate) fn print_time(label: &str, d: std::time::Duration) {
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

#[allow(unused)]
pub(crate) const ITERATIONS: usize = 100_000;
#[allow(unused)]
pub(crate) const WARMUP_ITERATIONS: usize = 1_000;

// A benchmarking macro to avoid copying memory and skewing the results.
#[macro_export]
macro_rules! bench {
    ($label:literal, $variant:literal, $input:expr, $setup:expr, $routine:expr) => {{
        let mut time = std::time::Duration::ZERO;

        // Warmup
        for _ in 0..bench_utils::WARMUP_ITERATIONS {
            let input = $setup($input);
            $routine(input);
        }

        // Benchmark
        for _ in 0..bench_utils::ITERATIONS {
            let input = $setup($input);

            let start = std::time::Instant::now();
            core::hint::black_box($routine(input));
            let end = std::time::Instant::now();

            time += end.duration_since(start);
        }
        bench_utils::print_time(concat!($label, " ", $variant), time);
    }};
}

#[macro_export]
macro_rules! bench_group {
    ($variant:literal, $mod:ident, $keypair_t:ident, $signature_t:ident) => {{
        bench!(
            "KeyGen",
            $variant,
            (),
            |()| {
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = bench_utils::random_array();
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
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = bench_utils::random_array();
                let signing_randomness: [u8; SIGNING_RANDOMNESS_SIZE] = bench_utils::random_array();
                let message = bench_utils::random_array::<1023>();
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
                let key_generation_seed: [u8; KEY_GENERATION_RANDOMNESS_SIZE] = bench_utils::random_array();
                let signing_randomness: [u8; SIGNING_RANDOMNESS_SIZE] = bench_utils::random_array();
                let message = bench_utils::random_array::<1023>();
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




