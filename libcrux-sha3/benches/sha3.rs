#![allow(non_snake_case)]
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};

use libcrux_sha3::*;

pub fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

pub fn fmt(x: usize) -> String {
    let base = (x as f64).log(1024f64).floor() as usize;
    let suffix = ["", "KB", "MB", "GB"];
    format!("{} {}", x >> (10 * base), suffix[base])
}

macro_rules! impl_comp {
    ($fun:ident, $libcrux:expr, $rust_crypto:ty, $openssl:expr) => {
        // Comparing libcrux performance for different payload sizes and other implementations.
        fn $fun(c: &mut Criterion) {
            const PAYLOAD_SIZES: [usize; 1] = [1024 * 1024 * 10];

            let mut group = c.benchmark_group(stringify!($fun).replace("_", " "));

            for payload_size in PAYLOAD_SIZES.iter() {
                group.throughput(Throughput::Bytes(*payload_size as u64));

                group.bench_with_input(
                    BenchmarkId::new("libcrux", fmt(*payload_size)),
                    payload_size,
                    |b, payload_size| {
                        b.iter_batched(
                            || randombytes(*payload_size),
                            |payload| {
                                let _d: [u8; digest_size($libcrux)] = hash($libcrux, &payload);
                            },
                            BatchSize::SmallInput,
                        )
                    },
                );

                // group.bench_with_input(
                //     BenchmarkId::new("RustCrypto", fmt(*payload_size)),
                //     payload_size,
                //     |b, payload_size| {
                //         use sha3::Digest;

                //         b.iter_batched(
                //             || randombytes(*payload_size),
                //             |payload| {
                //                 let mut hasher = <$rust_crypto>::new();
                //                 hasher.update(&payload);
                //                 let _result = hasher.finalize();
                //             },
                //             BatchSize::SmallInput,
                //         )
                //     },
                // );

                // #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
                // group.bench_with_input(
                //     BenchmarkId::new("OpenSSL", fmt(*payload_size)),
                //     payload_size,
                //     |b, payload_size| {
                //         use openssl::hash::*;

                //         b.iter_batched(
                //             || randombytes(*payload_size),
                //             |payload| {
                //                 let _result = hash($openssl, &payload);
                //             },
                //             BatchSize::SmallInput,
                //         )
                //     },
                // );

                // #[cfg(not(target_arch = "wasm32"))]
                // if stringify!($fun) != "Sha3_224" {
                //     group.bench_with_input(
                //         BenchmarkId::new("PQClean", fmt(*payload_size)),
                //         payload_size,
                //         |b, payload_size| {
                //             b.iter_batched(
                //                 || randombytes(*payload_size),
                //                 |payload| {
                //                     let mut digest = [0; libcrux::digest::digest_size($libcrux)];
                //                     unsafe {
                //                         $pqclean(
                //                             digest.as_mut_ptr(),
                //                             payload.as_ptr() as _,
                //                             payload.len(),
                //                         )
                //                     };
                //                 },
                //                 BatchSize::SmallInput,
                //             )
                //         },
                //     );
                // }
            }
        }
    };
}

impl_comp!(
    Sha3_224,
    Algorithm::Sha3_224,
    sha3::Sha3_224,
    MessageDigest::sha3_224() // libcrux_pqclean::sha3_256 // This is wrong, but it's not actually used.
);
impl_comp!(
    Sha3_256,
    Algorithm::Sha3_256,
    sha3::Sha3_256,
    MessageDigest::sha3_256() // libcrux_pqclean::sha3_256
);
impl_comp!(
    Sha3_384,
    Algorithm::Sha3_384,
    sha3::Sha3_384,
    MessageDigest::sha3_384() // libcrux_pqclean::sha3_384
);
impl_comp!(
    Sha3_512,
    Algorithm::Sha3_512,
    sha3::Sha3_512,
    MessageDigest::sha3_512() // libcrux_pqclean::sha3_512
);

fn benchmarks(c: &mut Criterion) {
    Sha3_224(c);
    Sha3_256(c);
    Sha3_384(c);
    Sha3_512(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
