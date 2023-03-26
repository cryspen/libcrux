# libjade in libcrux

## libjade: 

A formally verified cryptographic library written in 
[the jasmin programming language](https://github.com/jasmin-lang/jasmin)
with computer-verified proofs in [EasyCrypt](https://github.com/EasyCrypt/easycrypt);
libjade is part of the [Formosa-Crypto](https://formosa-crypto.org) project.

Each assembly implementation in libjade enjoys the following properties:

* Memory Safety
* Functional Correctness against a formal specification also written in EasyCrypt
* Timing Attack Protection
* Protection against Spectre v1
* Protection against Spectre v4
* Stack cleanup

libjade currently includes verified implementations for several hash functions, stream ciphers,
authenticated encryption, scalar multiplication, and post-quantum cryptography. For each algorithm,
libjade includes a reference implementation for x86 platforms, but also optimized SIMD implementations
for AVX2 platforms where available.

## libjade Algorithms in libcrux

The libcrux library currently uses the following verified implementations
from HACL*:

* ChaCha20 - reference x86_64 + Intel AVX2
* Poly1305 - reference x86_64 + Intel AVX2
* Curve25519 - reference x86_64 + Intel ADX+BMI2
* SHA-3 - portable x86_64

### Verifying libjade and Generating assembly code

TODO: something like the following

We pull code from the [HACL* repository](https://github.com/hacl-star/hacl-star) and run the verification
on the whole repository using the provided Makefile. The build depends upon [F*](https://www.fstar-lang.org/)
and [KaRaMeL](https://github.com/FStarLang/karamel). There is also a Docker image and a Nix recipe for building HACL*.
Once all the code is verified, the generated C code is taken from [dist/](https://github.com/hacl-star/hacl-star/tree/main/dist/gcc-compatible).

### Wrapping the libjade APIs within Rust

TODO: something like the following

For each algorithm we import into libcrux, we inspect the high-level verified APIs provided by HACL* and reflect
the correct types and pre-conditions in the libcrux Rust APIs. This is a manual process and is carefully reviewed
by multiple developers. We include pointers to the formal specs, the F* APIs, and the C APIs for all the algorithms we use in libcrux:

* ChaCha20 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Chacha20.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/chacha20/Hacl.Chacha20.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Chacha20.h)
* Poly1305 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Poly1305.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/poly1305/Hacl.Impl.Poly1305.fsti), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Poly1305_32.h)
* ChaCha20Poly1305 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Chacha20Poly1305.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/chacha20poly1305/Hacl.Impl.Chacha20Poly1305.fst), [C API]()
* Curve25519 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Curve25519.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/curve25519/Hacl.Impl.Curve25519.Generic.fsti), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Curve25519_51.h)
* SHA-2 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Sha2.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/streaming/Hacl.Streaming.SHA2.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Streaming_SHA2.h)
* SHA-3 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Sha3.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/streaming/Hacl.Streaming.SHA3.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Hash_SHA3.c)


## Spec Equivalence between Hacspec and libjade

TODO: somthing like the following

We can formally relate crypo specification in hacspec to those used by HACL*, by first compiling the hacspec to EasyCrypt and then proving that the two specifications are equivalent in EasyCrypt
In the subdirectory [spec-equivalence](spec-equivalence/) We show how this can be done for two algorithms.

### ChaCha20 Spec Equivalence

We start from the [Chacha20 specification in hacspec](https://github.com/hacspec/hacspec/blob/protocols/examples/chacha20/src/chacha20.rs) and compile it to EasyCrypt using the Circus tool.
We then prove that the result is equivalent to the [EasyCrypt Chacha20 specification]() used in libjade.
The proof of equivalence is in [](spec-equivalence/) and it needs an EasyCrypt installation to verify.

### Poly1305 Spec Equivalence

As with ChaCha20, we take the [Poly1305 specification in hacspec](https://github.com/hacspec/hacspec/blob/protocols/examples/poly1305/src/poly1305.rs) and compile it to EasyCrypt using the Circus tool.
We then prove that the result is equivalent to the [EasyCrypt Poly1305 specification]() used in libjade.
The proof of equivalence is in []() and it needs an EasyCrypt installation to verify.


## References

libjade and its associated proof methodologies have been published in the following papers:

*
*
*


