#![allow(non_snake_case)]
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};

use libcrux_secret_independence::*;
use libcrux_sha3::*;

pub fn randombytes_vec(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

pub fn randomsecretbytes_vec(n: usize) -> Vec<U8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);

    bytes.into_iter().map(|x| x.classify()).collect()
}

pub fn randombytes<const N: usize>() -> [u8; N] {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = [0u8; N];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

pub fn fmt(x: usize) -> String {
    let base = (x as f64).log(1024f64).floor() as usize;
    let suffix = ["", "KB", "MB", "GB"];
    format!("{} {}", x >> (10 * base), suffix[base])
}

macro_rules! impl_comp {
    ($fun:ident, $libcrux:expr, $neon_fun:ident) => {
        // Comparing libcrux performance for different payload sizes and other implementations.
        fn $fun(c: &mut Criterion) {
            const PAYLOAD_SIZES: [usize; 3] = [128, 1024, 1024 * 1024 * 10];

            let mut group = c.benchmark_group(stringify!($fun).replace("_", " "));

            for payload_size in PAYLOAD_SIZES.iter() {
                group.throughput(Throughput::Bytes(*payload_size as u64));

                group.bench_with_input(
                    BenchmarkId::new("libcrux", fmt(*payload_size)),
                    payload_size,
                    |b, payload_size| {
                        b.iter_batched(
                            || randomsecretbytes_vec(*payload_size),
                            |payload| {
                                const LEN: usize = digest_size($libcrux);
                                let _d: SecretArray<u8, LEN> = hash($libcrux, &payload);
                            },
                            BatchSize::SmallInput,
                        )
                    },
                );

                #[cfg(all(feature = "simd128", target_arch = "aarch64"))]
                group.bench_with_input(
                    BenchmarkId::new("rust version (simd128)", fmt(*payload_size)),
                    payload_size,
                    |b, payload_size| {
                        b.iter_batched(
                            || randombytes(*payload_size),
                            |payload| {
                                let mut digest = [0u8.classify(); digest_size($libcrux)];
                                neon::$neon_fun(&mut digest, &payload.classify_each());
                            },
                            BatchSize::SmallInput,
                        )
                    },
                );
            }
        }
    };
}

impl_comp!(Sha3_224, Algorithm::Sha224, sha224);
impl_comp!(Sha3_256, Algorithm::Sha256, sha256);
impl_comp!(Sha3_384, Algorithm::Sha384, sha384);
impl_comp!(Sha3_512, Algorithm::Sha512, sha512);

#[cfg(all(feature = "simd256", target_arch = "x86_64"))]
fn shake256(c: &mut Criterion) {
    let mut group = c.benchmark_group("shake256");
    group.bench_function("avx2", |b| {
        b.iter_batched(
            || {
                (
                    randombytes::<33>().classify(),
                    randombytes::<33>().classify(),
                    randombytes::<33>().classify(),
                    randombytes::<33>().classify(),
                )
            },
            |(payload0, payload1, payload2, payload3)| {
                let mut digest0 = [0u8.classify(); 128];
                let mut digest1 = [0u8.classify(); 128];
                let mut digest2 = [0u8.classify(); 128];
                let mut digest3 = [0u8.classify(); 128];
                avx2::x4::shake256(
                    payload0.as_slice(),
                    payload1.as_slice(),
                    payload2.as_slice(),
                    payload3.as_slice(),
                    &mut digest0,
                    &mut digest1,
                    &mut digest2,
                    &mut digest3,
                );
            },
            BatchSize::SmallInput,
        )
    });
}

fn benchmarks(c: &mut Criterion) {
    #[cfg(all(feature = "simd256", target_arch = "x86_64"))]
    shake256(c);
    Sha3_224(c);
    Sha3_256(c);
    Sha3_384(c);
    Sha3_512(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
