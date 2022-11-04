#[macro_use]
extern crate criterion;
extern crate libcrux;
extern crate rand;

use criterion::{BatchSize, Criterion};
use libcrux::hacl;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use libcrux::jasmin::x25519::{x25519 as libjade_x25519, x25519_base};

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

fn benchmarks(c: &mut Criterion) {
    x25519(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
