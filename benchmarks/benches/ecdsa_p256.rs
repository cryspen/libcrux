use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use benchmarks::util::*;
use libcrux_ecdsa::{
    p256::{Nonce, PrivateKey, PublicKey},
    DigestAlgorithm,
};

const PK_HEX: &str = "0460FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB67903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299";
const SK_HEX: &str = "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721";

fn sign(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("ECDSA (P256) Signing");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let mut rng = rand::rng();

                let sk: [u8; 32] = hex_str_to_array(SK_HEX);
                let sk = PrivateKey::try_from(&sk).unwrap();
                let nonce = Nonce::random(&mut rng).unwrap();
                let msg = b"sample";

                (msg, sk, nonce)
            },
            |(msg, sk, nonce)| {
                let _sig =
                    libcrux_ecdsa::p256::sign(DigestAlgorithm::Sha256, &msg[..], &sk, &nonce)
                        .unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{rand::SystemRandom, signature::ECDSA_P256_SHA256_FIXED_SIGNING};

        b.iter_batched(
            || {
                let rng = SystemRandom::new();
                let pk = hex_str_to_bytes(PK_HEX);
                let sk: [u8; 32] = hex_str_to_array(SK_HEX);
                let msg = b"sample";

                let keypair = ring::signature::EcdsaKeyPair::from_private_key_and_public_key(
                    &ECDSA_P256_SHA256_FIXED_SIGNING,
                    &sk,
                    &pk,
                    &rng,
                )
                .unwrap();

                (keypair, rng, msg)
            },
            |(keypair, rng, msg)| {
                let _sig = keypair.sign(&rng, msg).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        b.iter_batched(
            || {
                use openssl::ec::{EcGroup, EcKey};
                use openssl::nid::Nid;

                let nid = Nid::X9_62_PRIME256V1; // NIST P-256 curve
                let group = EcGroup::from_curve_name(nid).unwrap();
                let sk = EcKey::generate(&group).unwrap();

                let msg = b"sample";
                (sk, msg)
            },
            |(sk, msg)| {
                let _sig = openssl::ecdsa::EcdsaSig::sign(msg, sk.as_ref()).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn verify(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("ECDSA (P256) Verification");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let mut rng = rand::rng();

                let pk = hex_str_to_bytes(PK_HEX);
                let pk = PublicKey::try_from(pk.as_slice()).unwrap();
                let sk: [u8; 32] = hex_str_to_array(SK_HEX);
                let sk = PrivateKey::try_from(&sk).unwrap();
                let nonce = Nonce::random(&mut rng).unwrap();
                let msg = b"sample";
                let sig = libcrux_ecdsa::p256::sign(DigestAlgorithm::Sha256, &msg[..], &sk, &nonce)
                    .unwrap();
                (msg, sig, pk)
            },
            |(msg, sig, pk)| {
                let _ = libcrux_ecdsa::p256::verify(DigestAlgorithm::Sha256, &msg[..], &sig, &pk);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{
            rand::SystemRandom,
            signature::{self, KeyPair, ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA256_FIXED_SIGNING},
        };

        b.iter_batched(
            || {
                let rng = SystemRandom::new();
                let pk = hex_str_to_bytes(PK_HEX);
                let sk: [u8; 32] = hex_str_to_array(SK_HEX);
                let msg = b"sample";

                let keypair = ring::signature::EcdsaKeyPair::from_private_key_and_public_key(
                    &ECDSA_P256_SHA256_FIXED_SIGNING,
                    &sk,
                    &pk,
                    &rng,
                )
                .unwrap();
                let signature = keypair.sign(&rng, msg).unwrap();

                (keypair, msg, signature)
            },
            |(keypair, msg, signature)| {
                let pk = signature::UnparsedPublicKey::new(
                    &ECDSA_P256_SHA256_FIXED,
                    keypair.public_key().as_ref(),
                );
                let _ = pk.verify(msg, signature.as_ref()).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        b.iter_batched(
            || {
                use openssl::ec::{EcGroup, EcKey};
                use openssl::nid::Nid;

                let nid = Nid::X9_62_PRIME256V1; // NIST P-256 curve
                let group = EcGroup::from_curve_name(nid).unwrap();
                let sk = EcKey::generate(&group).unwrap();
                let pk = sk.public_key();
                let pk = EcKey::from_public_key(&group, &pk).unwrap();

                let msg = b"sample";
                let sig = openssl::ecdsa::EcdsaSig::sign(msg, sk.as_ref()).unwrap();
                (sig, msg, pk)
            },
            |(sig, msg, pk)| {
                let _ = sig.verify(msg, pk.as_ref()).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, sign, verify,);
criterion_main!(benches);
