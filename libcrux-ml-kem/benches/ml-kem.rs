use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand_core::OsRng;
use rand_core::RngCore;

use libcrux_ml_kem::mlkem768;

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("Kyber768 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux (external random)", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter(|| {
            let _kp = mlkem768::generate_key_pair(seed);
        })
    });

    #[cfg(feature = "simd256")]
    group.bench_function("libcrux neon unpacked (external random)", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter(|| {
            let _kp = mlkem768::avx2::generate_key_pair_unpacked(seed);
        })
    });

    #[cfg(feature = "simd128")]
    group.bench_function("libcrux neon unpacked (external random)", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter(|| {
            let _kp = mlkem768::neon::generate_key_pair_unpacked(seed);
        })
    });

    group.bench_function("libcrux portable unpacked (external random)", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter(|| {
            let _kp = mlkem768::portable::generate_key_pair_unpacked(seed);
        })
    });
}

pub fn comparisons_pk_validation(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("Kyber768 PK Validation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter_batched(
            || {
                let keypair = mlkem768::generate_key_pair(seed);
                keypair.public_key().as_slice().into()
            },
            |public_key| {
                let _valid = black_box(mlkem768::validate_public_key(public_key));
            },
            BatchSize::SmallInput,
        )
    });

}

pub fn comparisons_encapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux (external random)", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || mlkem768::generate_key_pair(seed1),
            |keypair| {
                let (_shared_secret, _ciphertext) =
                    mlkem768::encapsulate(keypair.public_key(), seed2);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux unpacked portable (external random)", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || mlkem768::portable::generate_key_pair_unpacked(seed1),
            |keypair| {
                let (_shared_secret, _ciphertext) =
                    mlkem768::portable::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(feature = "simd128")]
    group.bench_function("libcrux unpacked neon (external random)", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || mlkem768::neon::generate_key_pair_unpacked(seed1),
            |keypair| {
                let (_shared_secret, _ciphertext) =
                    mlkem768::neon::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(feature = "simd256")]
    group.bench_function("libcrux unpacked avx2 (external random)", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || mlkem768::avx2::generate_key_pair_unpacked(seed1),
            |keypair| {
                let (_shared_secret, _ciphertext) =
                    mlkem768::avx2::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_decapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Decapsulation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || {
                let keypair = mlkem768::generate_key_pair(seed1);
                let (ciphertext, _shared_secret) =
                    mlkem768::encapsulate(keypair.public_key(), seed2);
                (keypair, ciphertext)
            },
            |(keypair, ciphertext)| {
                let _shared_secret = mlkem768::decapsulate(keypair.private_key(), &ciphertext);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux unpacked portable", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || {
                let keypair = mlkem768::portable::generate_key_pair_unpacked(seed1);
                let (ciphertext, _shared_secret) =
                    mlkem768::portable::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
                (keypair, ciphertext)
            },
            |(keypair, ciphertext)| {
                let _shared_secret = mlkem768::portable::decapsulate_unpacked(&keypair, &ciphertext);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(feature = "simd128")]
    group.bench_function("libcrux unpacked neon", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || {
                let keypair = mlkem768::neon::generate_key_pair_unpacked(seed1);
                let (ciphertext, _shared_secret) =
                    mlkem768::neon::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
                (keypair, ciphertext)
            },
            |(keypair, ciphertext)| {
                let _shared_secret = mlkem768::neon::decapsulate_unpacked(&keypair, &ciphertext);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(feature = "simd256")]
    group.bench_function("libcrux unpacked avx2", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || {
                let keypair = mlkem768::avx2::generate_key_pair_unpacked(seed1);
                let (ciphertext, _shared_secret) =
                    mlkem768::avx2::encapsulate_unpacked(&keypair.public_key, &keypair.public_key_hash, seed2);
                (keypair, ciphertext)
            },
            |(keypair, ciphertext)| {
                let _shared_secret = mlkem768::avx2::decapsulate_unpacked(&keypair, &ciphertext);
            },
            BatchSize::SmallInput,
        )
    });

}

pub fn comparisons(c: &mut Criterion) {
    comparisons_pk_validation(c);
    comparisons_key_generation(c);
    comparisons_encapsulation(c);
    comparisons_decapsulation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
