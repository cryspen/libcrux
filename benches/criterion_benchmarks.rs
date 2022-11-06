#[macro_use]
extern crate criterion;
extern crate libcrux;
extern crate rand;

use criterion::{BatchSize, Criterion};
use libcrux::{
    digest::{self, digest_size, Algorithm},
    hacl::{self, sha2::hacl_hash},
};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use libcrux::jasmin::{
    sha2::sha256 as libjade_sha256,
    sha3::sha3_256 as libjade_sha3_256,
    x25519::{x25519 as libjade_x25519, x25519_base},
};

fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn jasmin_x25519(c: &mut Criterion) {
    c.bench_function("X25519 DH Jasmin", |b| {
        b.iter_batched(
            || {
                let sk1 = randombytes(32);
                let pk1 = x25519_base(&sk1).unwrap();
                let sk2 = randombytes(32);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = libjade_x25519(&sk2, &pk1).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn jasmin_x25519(_: &mut Criterion) {}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn jasmin_sha2(c: &mut Criterion) {
    c.bench_function("SHA2 256 Jasmin", |b| {
        b.iter_batched(
            || randombytes(3756),
            |payload| {
                let _zz = libjade_sha256(&payload).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn jasmin_sha2(_: &mut Criterion) {}

fn x25519(c: &mut Criterion) {
    jasmin_x25519(c);
    c.bench_function("X25519 DH HACL", |b| {
        b.iter_batched(
            || {
                let sk1 = randombytes(32);
                let pk1 = hacl::curve25519::derive_base(&sk1);
                let sk2 = randombytes(32);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = libcrux::hacl::curve25519::derive(&sk2, &pk1).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn jasmin_sha3(c: &mut Criterion) {
    c.bench_function("SHA3 256 Jasmin", |b| {
        b.iter_batched(
            || randombytes(3756),
            |payload| {
                let _zz = libjade_sha3_256(&payload).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn jasmin_sha3(_: &mut Criterion) {}

fn sha2(c: &mut Criterion) {
    jasmin_sha2(c);
    c.bench_function("SHA2 256 HACL", |b| {
        b.iter_batched(
            || randombytes(3756),
            |payload| {
                let _zz: [u8; digest_size(Algorithm::Sha256)] =
                    hacl_hash(Algorithm::Sha256, &payload);
            },
            BatchSize::SmallInput,
        )
    });
}

fn sha3(c: &mut Criterion) {
    jasmin_sha3(c);
    c.bench_function("SHA3 256 HACL", |b| {
        b.iter_batched(
            || randombytes(3756),
            |payload| {
                let _zz: [u8; digest_size(Algorithm::Sha3_256)] =
                    hacl_hash(Algorithm::Sha3_256, &payload);
            },
            BatchSize::SmallInput,
        )
    });
}

fn benchmarks(c: &mut Criterion) {
    // x25519(c);
    // sha2(c);
    sha3(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
