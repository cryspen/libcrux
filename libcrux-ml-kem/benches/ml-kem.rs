use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand::{rngs::OsRng, RngCore};

use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768};

macro_rules! init {
    ($version:path, $bench:expr, $c:expr) => {{
        let mut group = $c.benchmark_group(format!("ML-KEM {} {}", stringify!($version), $bench));
        group.measurement_time(Duration::from_secs(10));

        use $version as version;
        #[cfg(feature = "pre-verification")]
        {
            fun!("portable", version::portable, group);
            fun_unpacked!("portable", version::portable::unpacked, group);
        }
        #[cfg(all(feature = "simd128", feature = "pre-verification"))]
        {
            fun!("neon", version::neon, group);
            fun_unpacked!("neon", version::neon::unpacked, group);
        }
        #[cfg(all(feature = "simd256", feature = "pre-verification"))]
        {
            fun!("avx2", version::avx2, group);
            fun_unpacked!("avx2", version::avx2::unpacked, group);
        }
        #[cfg(not(feature = "pre-verification"))]
        fun!("verified", version, group);
    }};
}

pub fn key_generation(c: &mut Criterion) {
    let mut rng = OsRng;

    macro_rules! fun {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(format!("libcrux {} (external random)", $name), |b| {
                use $p as p;

                let mut seed = [0; 64];
                rng.fill_bytes(&mut seed);
                b.iter(|| {
                    let _kp = core::hint::black_box(p::generate_key_pair(seed));
                })
            });
        };
    }

    macro_rules! fun_unpacked {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(
                format!("libcrux unpacked {} (external random)", $name),
                |b| {
                    use $p as p;

                    let mut seed = [0; 64];
                    rng.fill_bytes(&mut seed);
                    b.iter(|| {
                        let mut kp = p::init_key_pair();
                        p::generate_key_pair(seed, &mut kp);
                    })
                },
            );
        };
    }

    init!(mlkem512, "Key Generation", c);
    init!(mlkem768, "Key Generation", c);
    init!(mlkem1024, "Key Generation", c);
}

pub fn pk_validation(c: &mut Criterion) {
    let mut rng = OsRng;

    macro_rules! fun {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(format!("libcrux {}", $name), |b| {
                use $p as p;

                let mut seed = [0; 64];
                rng.fill_bytes(&mut seed);
                b.iter_batched(
                    || {
                        let keypair = p::generate_key_pair(seed);
                        keypair
                    },
                    |keypair| {
                        let _valid = black_box(p::validate_public_key(keypair.public_key()));
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    macro_rules! fun_unpacked {
        ($name:expr, $p:path, $group:expr) => {
            // We don't do anything here.
        };
    }

    init!(mlkem512, "PK Validation", c);
    init!(mlkem768, "PK Validation", c);
    init!(mlkem1024, "PK Validation", c);
}

#[target_feature(enable = "avx2")]
pub unsafe fn encapsulation(c: &mut Criterion) {
    macro_rules! fun {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(format!("libcrux {} (external random)", $name), |b| {
                use $p as p;
                let mut seed1 = [0; 64];
                OsRng.fill_bytes(&mut seed1);
                let mut seed2 = [0; 32];
                OsRng.fill_bytes(&mut seed2);
                b.iter_batched(
                    || p::generate_key_pair(seed1),
                    |keypair| {
                        let (_shared_secret, _ciphertext) =
                            black_box(p::encapsulate(keypair.public_key(), seed2));
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    macro_rules! fun_unpacked {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(
                format!("libcrux unpacked {} (external random)", $name),
                |b| {
                    use $p as p;
                    let mut seed1 = [0; 64];
                    OsRng.fill_bytes(&mut seed1);
                    let mut seed2 = [0; 32];
                    OsRng.fill_bytes(&mut seed2);
                    b.iter_batched(
                        || {
                            let mut kp = p::init_key_pair();
                            p::generate_key_pair(seed1, &mut kp);
                            kp
                        },
                        |keypair| {
                            let (_shared_secret, _ciphertext) =
                                black_box(p::encapsulate(&keypair.public_key, seed2));
                        },
                        BatchSize::SmallInput,
                    )
                },
            );
        };
    }

    init!(mlkem512, "Encapsulation", c);
    init!(mlkem768, "Encapsulation", c);
    init!(mlkem1024, "Encapsulation", c);
}

#[target_feature(enable = "avx2")]
pub unsafe fn decapsulation(c: &mut Criterion) {
    macro_rules! fun {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(format!("libcrux {}", $name), |b| {
                use $p as p;
                let mut seed1 = [0; 64];
                OsRng.fill_bytes(&mut seed1);
                let mut seed2 = [0; 32];
                OsRng.fill_bytes(&mut seed2);
                b.iter_batched(
                    || {
                        let keypair = p::generate_key_pair(seed1);
                        let (ciphertext, _shared_secret) =
                            p::encapsulate(keypair.public_key(), seed2);
                        (keypair, ciphertext)
                    },
                    |(keypair, ciphertext)| {
                        let _shared_secret =
                            black_box(p::decapsulate(keypair.private_key(), &ciphertext));
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    macro_rules! fun_unpacked {
        ($name:expr, $p:path, $group:expr) => {
            $group.bench_function(format!("libcrux unpacked {}", $name), |b| {
                use $p as p;
                let mut seed1 = [0; 64];
                OsRng.fill_bytes(&mut seed1);
                let mut seed2 = [0; 32];
                OsRng.fill_bytes(&mut seed2);
                b.iter_batched(
                    || {
                        let mut keypair = p::init_key_pair();
                        p::generate_key_pair(seed1, &mut keypair);
                        let (ciphertext, _shared_secret) =
                            p::encapsulate(&keypair.public_key, seed2);
                        (keypair, ciphertext)
                    },
                    |(keypair, ciphertext)| {
                        let _shared_secret = black_box(p::decapsulate(&keypair, &ciphertext));
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    init!(mlkem512, "Decapsulation", c);
    init!(mlkem768, "Decapsulation", c);
    init!(mlkem1024, "Decapsulation", c);
}

pub fn comparisons(c: &mut Criterion) {
    // key_generation(c);
    unsafe { encapsulation(c) };
    unsafe { decapsulation(c) };
    // pk_validation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);

// pub(crate) const MICROS_PER_MILLI: f64 = 1_000.0;
// pub(crate) const MICROS_PER_SECOND: f64 = 1_000_000.0;
// pub(crate) const MILLI_PER_ITERATION_THRESHOLD: u128 = 1_000 * 10_000 as u128;
// pub(crate) const SECOND_PER_ITERATION_THRESHOLD: u128 = 1_000_000 * 10_000 as u128;

// pub(crate) fn print_time(label: &str, d: std::time::Duration) {
//     let micros = d.as_micros();
//     let time = if micros < MILLI_PER_ITERATION_THRESHOLD {
//         format!("{} μs", micros / 10_000 as u128)
//     } else if micros < SECOND_PER_ITERATION_THRESHOLD {
//         format!(
//             "{:.2} ms",
//             (micros as f64 / (MICROS_PER_MILLI * 10_000 as f64))
//         )
//     } else {
//         format!(
//             "{:.2}s",
//             (micros as f64 / (MICROS_PER_SECOND * 10_000 as f64))
//         )
//     };
//     let space = if label.len() < 6 {
//         "\t\t".to_string()
//     } else {
//         "\t".to_string()
//     };

//     println!("{label}:{space}{time}");
// }

// pub fn main() {
//     let mut seed1 = [0; 64];
//     OsRng.fill_bytes(&mut seed1);
//     let mut seed2 = [0; 32];
//     OsRng.fill_bytes(&mut seed2);
//     let keypair = mlkem768::avx2::generate_key_pair(seed1);

//     let mut time = std::time::Duration::ZERO;
//     let start = std::time::Instant::now();
//     for _ in 0..10_000 {
//         let (_shared_secret, _ciphertext) =
//             black_box(mlkem768::avx2::encapsulate(keypair.public_key(), seed2));
//     }
//     let end = std::time::Instant::now();
//     time += end.duration_since(start);
//     print_time("encaps", time);
// }
