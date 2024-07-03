use classic_mceliece_rust::{decapsulate_boxed, encapsulate_boxed};
use rand::thread_rng;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

pub fn comparisons_kem_key_generation(c: &mut Criterion) {
    let mut rng = thread_rng();
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
            let _ = classic_mceliece_rust::keypair_boxed(&mut rng);
        })
    });
}

pub fn comparisons_kem_encaps(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("Raw KEM Encapsulation");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::MlKem768, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut thread_rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux X25519", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::X25519, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut thread_rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter_batched(
            || libcrux_kem::key_gen(libcrux_kem::Algorithm::XWingKemDraft02, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.encapsulate(&mut thread_rng());
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter_batched(
            || classic_mceliece_rust::keypair_boxed(&mut rng),
            |(pk, _sk)| {
                let _ = encapsulate_boxed(&pk, &mut thread_rng());
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_kem_decaps(c: &mut Criterion) {
    let mut rng = thread_rng();
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
                let (pk, sk) = classic_mceliece_rust::keypair_boxed(&mut rng);
                let (enc, _ss) = encapsulate_boxed(&pk, &mut rng);
                (sk, enc)
            },
            |(sk, enc)| decapsulate_boxed(&enc, &sk),
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_psq_key_generation(c: &mut Criterion) {
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
    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter(|| {
            let _ =
                libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::XWingKemDraft02, &mut rng);
        })
    });
    group.bench_function("classic_mceliece_rust (mceliece460896f)", |b| {
        b.iter(|| {
            let _ =
                libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::ClassicMcEliece, &mut rng);
        })
    });
}

pub fn comparisons_psq_send(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("PSK-PQ Pre-Shared Key Send");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::MlKem768, &mut rng).unwrap(),
            |(_sk, pk)| {
                let _ = pk.send_psk(
                    b"bench context",
                    Duration::from_secs(3600),
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
                let _ = pk.send_psk(
                    b"bench context",
                    Duration::from_secs(3600),
                    &mut thread_rng(),
                );
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter_batched(
            || {
                libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::XWingKemDraft02, &mut rng)
                    .unwrap()
            },
            |(_sk, pk)| {
                let _ = pk.send_psk(
                    b"bench context",
                    Duration::from_secs(3600),
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
                let _ = pk.send_psk(
                    b"bench context",
                    Duration::from_secs(3600),
                    &mut thread_rng(),
                );
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_psq_receive(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("PSK-PQ Pre-Shared Key Receive");
    group.measurement_time(Duration::from_secs(15));

    group.bench_function("libcrux ML-KEM-768", |b| {
        b.iter_batched(
            || {
                let (sk, pk) =
                    libcrux_psq::generate_key_pair(libcrux_psq::Algorithm::MlKem768, &mut rng)
                        .unwrap();

                let (_psk, message) = pk
                    .send_psk(b"bench context", Duration::from_secs(3600), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.receive_psk(&pk, &message, b"bench context");
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
                    .send_psk(b"bench context", Duration::from_secs(3600), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.receive_psk(&pk, &message, b"bench context");
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux XWingKemDraft02", |b| {
        b.iter_batched(
            || {
                let (sk, pk) = libcrux_psq::generate_key_pair(
                    libcrux_psq::Algorithm::XWingKemDraft02,
                    &mut rng,
                )
                .unwrap();

                let (_psk, message) = pk
                    .send_psk(b"bench context", Duration::from_secs(3600), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.receive_psk(&pk, &message, b"bench context");
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
                    .send_psk(b"bench context", Duration::from_secs(3600), &mut rng)
                    .unwrap();
                (pk, sk, message)
            },
            |(pk, sk, message)| {
                let _ = sk.receive_psk(&pk, &message, b"bench context");
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons(c: &mut Criterion) {
    // Raw KEM operations
    comparisons_kem_key_generation(c);
    comparisons_kem_encaps(c);
    comparisons_kem_decaps(c);

    // PSQ protocol
    comparisons_psq_key_generation(c);
    comparisons_psq_send(c);
    comparisons_psq_receive(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
