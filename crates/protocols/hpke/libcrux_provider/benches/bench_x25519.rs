use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::*, HpkeCrypto};
use hpke_rs_libcrux::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("x25519 Derive"), |b| {
        b.iter_batched(
            || {
                let (pk, sk) =
                    HpkeLibcrux::kem_key_gen(KemAlgorithm::DhKem25519, &mut HpkeLibcrux::prng())
                        .unwrap();
                (sk.clone(), pk.clone())
            },
            |(sk, pk)| {
                let _ = HpkeLibcrux::dh(KemAlgorithm::DhKem25519, &pk, &sk);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("x25519 Derive Base"), |b| {
        b.iter_batched(
            || {
                let (_pk, sk) =
                    HpkeLibcrux::kem_key_gen(KemAlgorithm::DhKem25519, &mut HpkeLibcrux::prng())
                        .unwrap();
                sk.clone()
            },
            |sk| {
                let _pk = HpkeLibcrux::secret_to_public(KemAlgorithm::DhKem25519, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
