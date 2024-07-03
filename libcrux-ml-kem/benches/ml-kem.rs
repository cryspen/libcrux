use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand_core::OsRng;
use rand_core::RngCore;

use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768};

macro_rules! init {
    ($version:path, $bench:expr, $c:expr) => {{
        let mut group = $c.benchmark_group(format!("ML-KEM {} {}", stringify!($version), $bench));
        group.measurement_time(Duration::from_secs(10));

        use $version as version;
        #[cfg(feature = "pre-verification")]
        fun!("portable", version::portable, group);
        #[cfg(all(feature = "simd128", feature = "pre-verification"))]
        fun!("neon", version::neon, group);
        #[cfg(all(feature = "simd256", feature = "pre-verification"))]
        fun!("neon", version::avx2, group);
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
                        keypair.public_key().as_slice().into()
                    },
                    |public_key| {
                        let _valid = black_box(p::validate_public_key(public_key));
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }

    init!(mlkem512, "PK Validation", c);
    init!(mlkem768, "PK Validation", c);
    init!(mlkem1024, "PK Validation", c);
}

pub fn encapsulation(c: &mut Criterion) {
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

    init!(mlkem512, "Encapsulation", c);
    init!(mlkem768, "Encapsulation", c);
    init!(mlkem1024, "Encapsulation", c);
}

pub fn decapsulation(c: &mut Criterion) {
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

    init!(mlkem512, "Decapsulation", c);
    init!(mlkem768, "Decapsulation", c);
    init!(mlkem1024, "Decapsulation", c);
}

pub fn comparisons(c: &mut Criterion) {
    pk_validation(c);
    key_generation(c);
    encapsulation(c);
    decapsulation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
