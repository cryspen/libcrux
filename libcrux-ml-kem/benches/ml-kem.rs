use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand_core::OsRng;
use rand_core::RngCore;

use libcrux_ml_kem::{mlkem1024, mlkem512, mlkem768};

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

    let mut group = c.benchmark_group("ML-KEM 512 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem512::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem512::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem512::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 768 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem768::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem768::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem768::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 1024 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem1024::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem1024::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem1024::avx2, group);
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

    let mut group = c.benchmark_group("ML-KEM 512 PK Validation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem512::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem512::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem512::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 768 PK Validation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem768::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem768::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem768::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 1024 PK Validation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem1024::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem1024::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem1024::avx2, group);
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

    let mut group = c.benchmark_group("ML-KEM 512 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem512::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem512::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem512::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 768 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem768::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem768::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem768::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 1024 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem1024::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem1024::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem1024::avx2, group);
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

    let mut group = c.benchmark_group("ML-KEM 512 Decapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem512::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem512::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem512::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 768 Decapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem768::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem768::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem768::avx2, group);
    drop(group);

    let mut group = c.benchmark_group("ML-KEM 1024 Decapsulation");
    group.measurement_time(Duration::from_secs(10));

    fun!("portable", mlkem1024::portable, group);
    #[cfg(feature = "simd128")]
    fun!("neon", mlkem1024::neon, group);
    #[cfg(feature = "simd256")]
    fun!("neon", mlkem1024::avx2, group);
}

pub fn comparisons(c: &mut Criterion) {
    pk_validation(c);
    key_generation(c);
    encapsulation(c);
    decapsulation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
