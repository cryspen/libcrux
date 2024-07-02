# ML-KEM

This crate implements all three ML-KEM ([FIPS 203](https://csrc.nist.gov/pubs/fips/203/ipd) (Initial Public Draft)) variants 512, 768, and 1024. It is
formally verified using [hax](https://cryspen.com/hax) and
 [F*](https://fstar-lang.org).

Functions in this crate use CPU feature detection to pick the most efficient version
on each platform. To use a specific version with your own feature detection
use e.g. one of the following
- `mlkem768::avx2::generate_key_pair`,
- `mlkem768::neon::generate_key_pair`,
- `mlkem768::portable::generate_key_pair`,

analogously for encapsulation and decapsulation.

```Rust
 use rand::{rngs::OsRng, RngCore};

 // Ensure you use good randomness.
 // It is not recommended to use OsRng directly!
 // Instead it is highly encouraged to use RNGs like NISTs DRBG to account for
 // bad system entropy.
 fn random_array<const L: usize>() -> [u8; L] {
     let mut rng = OsRng;
     let mut seed = [0; L];
     rng.try_fill_bytes(&mut seed).unwrap();
     seed
 }

 use libcrux_ml_kem::*;

 // This example uses ML-KEM 768. The other variants can be used the same way.

 // Generate a key pair.
 let randomness = random_array();
 let key_pair = mlkem768::generate_key_pair(randomness);

 // Encapsulating a shared secret to a public key.
 let randomness = random_array();
 let (ciphertext, shared_secret) = mlkem768::encapsulate(key_pair.public_key(), randomness);

 // Decapsulating a shared secret with a private key.
 let shared_secret_decapsulated = mlkem768::decapsulate(key_pair.private_key(), &ciphertext);
```


## Features

By default, all ML-KEM parameter sets are enabled. If required, they are
available individually under feature flags `mlkem512`, `mlkem768`,
`mlkem1024`.

In addition to the verified implementations of the ML-KEM variants, the
feature flag `pre-verification` gives access to, as yet, unverified
implementations of ML-KEM that are optimized for SIMD instruction sets.

### Kyber Round 3
The `kyber` flag (in combination with `pre-verification`) also gives access
to an, as yet, unverified implementation of Kyber as submitted in Round 3 of
the NIST PQ competition.

