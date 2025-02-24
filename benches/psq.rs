use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use libcrux_psq::traits::PSQ;
use libcrux_traits::kem::KEM;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

pub fn kem_key_generation(c: &mut Criterion) {
    let mut rng = rand::rng();

    let mut group = c.benchmark_group("Raw KEM Key Generation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter(|| {
            let _ = libcrux_kem::key_gen(libcrux_kem::Algorithm::MlKem768, &mut rng);
        })
    });
    group.bench_function("libcrux X25519", |b| {
        b.iter(|| {
            let _ = libcrux_kem::key_gen(libcrux_kem::Algorithm::X25519, &mut rng);
        })
    });
    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter(|| {
            let _ = libcrux_kem::key_gen(libcrux_kem::Algorithm::XWingKemDraft02, &mut rng);
        })
    });
    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter(|| {
            let _ = classic_mceliece_rust::keypair_boxed(&mut rand_old::thread_rng());
        })
    });
}

pub fn kem_encaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut old_rng = rand_old::thread_rng();
    let mut group = c.benchmark_group("Raw KEM Encapsulation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::MlKem768, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut rand::rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux X25519", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::X25519, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut rand::rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::XWingKemDraft02, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut rand::rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter_batched(
            || classic_mceliece_rust::keypair_boxed(&mut old_rng),
            |(pk, _sk)| {
                let _ = encapsulate_boxed(&pk, &mut rand_old::thread_rng());
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn kem_decaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut old_rng = rand_old::thread_rng();
    let mut group = c.benchmark_group("Raw KEM Decapsulation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_kem::key_gen(libcrux_kem::Algorithm::MlKem768, &mut rng).unwrap();
                let (_ss, enc) = pk.encapsulate(&mut rng).unwrap();
                (sk, enc)
            },
            |(sk, enc)| enc.decapsulate(&sk),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux X25519", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_kem::key_gen(libcrux_kem::Algorithm::X25519, &mut rng).unwrap();
                let (_ss, enc) = pk.encapsulate(&mut rng).unwrap();
                (sk, enc)
            },
            |(sk, enc)| enc.decapsulate(&sk),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_kem::key_gen(libcrux_kem::Algorithm::XWingKemDraft02, &mut rng)
                        .unwrap();
                let (_ss, enc) = pk.encapsulate(&mut rng).unwrap();
                (sk, enc)
            },
            |(sk, enc)| enc.decapsulate(&sk),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter_batched(
            || {
                let (pk, sk) = classic_mceliece_rust::keypair_boxed(&mut old_rng);
                let (enc, _ss) = encapsulate_boxed(&pk, &mut old_rng);
                (sk, enc)
            },
            |(sk, enc)| decapsulate_boxed(&enc, &sk),
            BatchSize::SmallInput,
        )
    });
}

pub fn psq_encaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut group = c.benchmark_group("PSQ Encapsulation");
    group.measurement_time(Duration::from_secs(15));

    macro_rules! encaps_bench {
        ($name:literal, $implementation:path) => {
            group.bench_function($name, |b| {
                b.iter_batched(
                    || {
                        let (_pqsk, pqpk) =
                            <$implementation as KEM>::generate_key_pair(&mut rng).unwrap();
                        pqpk
                    },
                    |pqpk| {
                        let _ = <$implementation as PSQ>::encapsulate_psq(
                            &pqpk,
                            b"some context",
                            &mut rand::rng(),
                        )
                        .unwrap();
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }
    encaps_bench!("libcrux ML-KEM-768", libcrux_psq::impls::MlKem768);
    encaps_bench!("libcrux X25519", libcrux_psq::impls::X25519);
    encaps_bench!(
        "libcrux XWingKemDraft02",
        libcrux_psq::impls::XWingKemDraft02
    );
    encaps_bench!(
        "classic_mceliece_rust (mceliece460896f)",
        libcrux_psq::classic_mceliece::ClassicMcEliece
    );
}

pub fn psq_decaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut group = c.benchmark_group("ECDH-bound PSK-PQ Pre-Shared Key Receive");
    group.measurement_time(Duration::from_secs(15));

    macro_rules! decaps_bench {
        ($name:literal, $implementation:path) => {
            group.bench_function($name, |b| {
                b.iter_batched(
                    || {
                        let (pqsk, pqpk) =
                            <$implementation as KEM>::generate_key_pair(&mut rng).unwrap();
                        let (_psk, ctx) = <$implementation as PSQ>::encapsulate_psq(
                            &pqpk,
                            b"some context",
                            &mut rand::rng(),
                        )
                        .unwrap();
                        (pqsk, pqpk, ctx)
                    },
                    |(pqsk, pqpk, ctx)| {
                        let _ = <$implementation as PSQ>::decapsulate_psq(
                            &pqsk,
                            &pqpk,
                            &ctx,
                            b"some context",
                        )
                        .unwrap();
                    },
                    BatchSize::SmallInput,
                )
            });
        };
    }
    decaps_bench!("libcrux ML-KEM-768", libcrux_psq::impls::MlKem768);
    decaps_bench!("libcrux X25519", libcrux_psq::impls::X25519);
    decaps_bench!(
        "libcrux XWingKemDraft02",
        libcrux_psq::impls::XWingKemDraft02
    );
    decaps_bench!(
        "classic_mceliece_rust (mceliece460896f)",
        libcrux_psq::classic_mceliece::ClassicMcEliece
    );
}

pub fn comparisons(c: &mut Criterion) {
    // Raw KEM operations
    kem_key_generation(c);
    kem_encaps(c);
    kem_decaps(c);

    // PSQ protocol
    psq_encaps(c);
    psq_decaps(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
