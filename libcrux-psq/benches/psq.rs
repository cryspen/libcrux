use rand::thread_rng;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("PSK-PQ Key Generation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter(|| {
            let _ = libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::MlKem768, &mut rng);
        })
    });
    group.bench_function("libcrux X25519", |b| {
        b.iter(|| {
            let _ = libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::X25519, &mut rng);
        })
    });
    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter(|| {
            let _ =
                libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::ClassicMcEliece, &mut rng);
        })
    });
}

pub fn comparisons_psk_generation(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("PSK-PQ Pre-Shared Key Generation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::MlKem768, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.generate_psk(
                    b"bench context",
                    chrono::Duration::hours(1),
                    &mut thread_rng(),
                );
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux X25519", |b| {
        b.iter_batched(
            || libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::X25519, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.generate_psk(
                    b"bench context",
                    chrono::Duration::hours(1),
                    &mut thread_rng(),
                );
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter_batched(
            || {
                libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::ClassicMcEliece, &mut rng)
                    .unwrap()
            },
            |(_sk, pk)| {
                let _ = pk.generate_psk(
                    b"bench context",
                    chrono::Duration::hours(1),
                    &mut thread_rng(),
                );
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_psk_derivation(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("PSK-PQ Pre-Shared Key Derivation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::MlKem768, &mut rng)
                        .unwrap();

                let (_psk, message) = pk
                    .generate_psk(b"bench context", chrono::Duration::hours(1), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.derive_psk(&pk, &message, b"bench context");
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux X25519", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::X25519, &mut rng)
                        .unwrap();

                let (_psk, message) = pk
                    .generate_psk(b"bench context", chrono::Duration::hours(1), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.derive_psk(&pk, &message, b"bench context");
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter_batched(
            || {
                let (sk, pk) = libcrux_psq::generate_key_pair(
                    libcrux_psq::Algorithm::ClassicMcEliece,
                    &mut rng,
                )
                .unwrap();

                let (_psk, message) = pk
                    .generate_psk(b"bench context", chrono::Duration::hours(1), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.derive_psk(&pk, &message, b"bench context");
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons(c: &mut Criterion) {
    comparisons_key_generation(c);
    comparisons_psk_generation(c);
    comparisons_psk_derivation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
