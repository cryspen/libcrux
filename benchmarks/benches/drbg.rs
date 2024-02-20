use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use libcrux::{digest::Algorithm, drbg::*};
use ring::rand::Random;

fn init(c: &mut Criterion) {
    let mut group = c.benchmark_group("Drbg");

    group.bench_function("libcrux Sha256", |b| {
        b.iter(|| {
            let _drbg = Drbg::new(Algorithm::Sha256).unwrap();
        })
    });

    // group.bench_function("Ring", |b| {
    //     use ring::rand::SystemRandom;

    //     b.iter(|| {
    //         let _rng = SystemRandom::new();
    //     })
    // });

    // group.bench_function("RustCrypto", |b| {
    //     use rand_core::OsRng;

    //     b.iter(|| {
    //         let _rng = OsRng; // Nothing to do really
    //     })
    // });

    // group.bench_function("OpenSSL", |b| {
    //     use openssl::rand::rand_bytes;

    //     b.iter(|| {
    //         let _rng = rand_bytes; // Nothing to do really
    //     })
    // });
}

fn generate(c: &mut Criterion) {
    let mut group = c.benchmark_group("Drbg");

    group.bench_function("libcrux Sha256", |b| {
        b.iter_batched(
            || {
                let drbg = Drbg::new(Algorithm::Sha256).unwrap();
                drbg
            },
            |mut drbg| {
                let mut random_bytes = [0u8; 32];
                drbg.fill_bytes(&mut random_bytes);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::rand::{generate, SystemRandom};

        b.iter_batched(
            || SystemRandom::new(),
            |rng| {
                let _random_bytes: Random<[u8; 32]> = generate(&rng).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("RustCrypto", |b| {
        use rand_core::OsRng;

        b.iter_batched(
            || {},
            |()| {
                let mut random_bytes = vec![0u8; 32];
                OsRng.fill_bytes(&mut random_bytes);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        use openssl::rand::rand_bytes;

        b.iter_batched(
            || {},
            |()| {
                let mut random_bytes = [0u8; 32];
                rand_bytes(&mut random_bytes).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, init, generate);
criterion_main!(benches);
