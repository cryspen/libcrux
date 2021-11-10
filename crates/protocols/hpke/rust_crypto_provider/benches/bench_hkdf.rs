use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::*, HpkeCrypto, RngCore};
use hpke_rs_rust_crypto::*;
use rand::rngs::OsRng;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("HKDF SHA256 Extract"), |b| {
        b.iter_batched(
            || {
                let mut salt = vec![0u8; 77];
                let mut ikm = vec![0u8; 32];
                OsRng.fill_bytes(&mut salt);
                OsRng.fill_bytes(&mut ikm);
                (salt.clone(), ikm.clone())
            },
            |(salt, ikm)| {
                let _ = HpkeRustCrypto::kdf_extract(KdfAlgorithm::HkdfSha256, &salt, &ikm);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("HKDF SHA256 Expand"), |b| {
        b.iter_batched(
            || {
                let mut info = vec![0u8; 77];
                let mut prk = vec![0u8; 32];
                OsRng.fill_bytes(&mut info);
                OsRng.fill_bytes(&mut prk);
                (prk.clone(), info.clone())
            },
            |(prk, info)| {
                let _ = HpkeRustCrypto::kdf_expand(KdfAlgorithm::HkdfSha256, &prk, &info, 32);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
