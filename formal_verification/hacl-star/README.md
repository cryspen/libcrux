# HACL* in libcrux

## HACL*: A High-Assurance Cryptographic Library

[HACL*](https://github.com/hacl-star/hacl-star) is a formally verified library of modern cryptographic algorithms
written in the [F*](https://www.fstar-lang.org/) language and compiled to portable C. Each implementation in HACL*
is verified for:

* Memory Safety in the C memory model
* Functional Correctness against a formal specification also written in F*
* Secret Independence, i.e. that control flow and memory accesses do not depend on secrets

Once these properties are proved, the code is compiled to C using a compiler called
[KaRaMeL](https://github.com/FStarLang/karamel). HACL* includes portable C implementations
for a wide variety of modern crypto algorithms, including hash functions, encryption schemes,
Diffie-Hellman, elliptic curves, and signature schemes. For each algorithm, HACL* includes
a reference implementation in portable C, and often also includes verified implementations
optimized for specific SIMD platforms such as Intel AVX2, AVX512, and ARM Neon.

## HACL* Algorithms in libcrux

The libcrux library currently uses the following verified implementations
from HACL*:

* ChaCha20 - portable C + Intel AVX2 + ARM Neon
* Poly1305 - portable C + Intel AVX2 + ARM Neon
* ChaCha20Poly1305 - portable C
* Curve25519 - portable C + Intel ADX+BMI2 (using ValeCrypto)
* SHA-2 - portable C
* SHA-3 - portable C

### Verifying HACL* and Generating C code

We pull code from the [HACL* repository](https://github.com/hacl-star/hacl-star) and run the verification
on the whole repository using the provided Makefile. The build depends upon [F*](https://www.fstar-lang.org/)
and [KaRaMeL](https://github.com/FStarLang/karamel). There is also a Docker image and a Nix recipe for building HACL*.
Once all the code is verified, the generated C code is taken from [dist/](https://github.com/hacl-star/hacl-star/tree/main/dist/gcc-compatible).

### Wrapping the HACL* C APIs within Rust

For each algorithm we import into libcrux, we inspect the high-level verified APIs provided by HACL* and reflect
the correct types and pre-conditions in the libcrux Rust APIs. This is a manual process and is carefully reviewed
by multiple developers. We include pointers to the formal specs, the F* APIs, and the C APIs for all the algorithms we use in libcrux:

* ChaCha20 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Chacha20.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/chacha20/Hacl.Chacha20.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Chacha20.h)
* Poly1305 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Poly1305.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/poly1305/Hacl.Impl.Poly1305.fsti), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Poly1305_32.h)
* ChaCha20Poly1305 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Chacha20Poly1305.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/chacha20poly1305/Hacl.Impl.Chacha20Poly1305.fst), [C API]()
* Curve25519 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Curve25519.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/curve25519/Hacl.Impl.Curve25519.Generic.fsti), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Curve25519_51.h)
* SHA-2 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Sha2.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/streaming/Hacl.Streaming.SHA2.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Streaming_SHA2.h)
* SHA-3 - [Spec](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Sha3.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/code/streaming/Hacl.Streaming.SHA3.fst), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/Hacl_Hash_SHA3.c)


## Spec Equivalence between Hacspec and HACL*

We can formally relate crypo specification in hacspec to those used by HACL*, by first compiling the hacspec to F* and then proving that the two specifications are equivalent in F*.
In the subdirectory [spec-equivalence](spec-equivalence/) We show how this can be done for two algorithms.

### ChaCha20 Spec Equivalence

We start from the [Chacha20 specification in hacspec](https://github.com/hacspec/hacspec/blob/protocols/examples/chacha20/src/chacha20.rs) and compile it to F* using the Circus tool.
We then prove that the result is equivalent to the [F* Chacha20 specification](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Chacha20.fst) used in HACL*.
The proof of equivalence is in [Hacspec.Chacha20.Proof.fst](spec-equivalence/Hacspec.Chacha20.Proof.fst) and it needs an F* installation to verify.

### Poly1305 Spec Equivalence

As with ChaCha20, we take the [Poly1305 specification in hacspec](https://github.com/hacspec/hacspec/blob/protocols/examples/poly1305/src/poly1305.rs) and compile it to F* using the Circus tool.
We then prove that the result is equivalent to the [F* Poly1305 specification](https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.Poly1305.fst) used in HACL*.
The proof of equivalence is in [Hacspec.Chacha20.Proof.fst](spec-equivalence/Hacspec.Poly1305.Proof.fst) and it needs an F* installation to verify.

### Other Algorithms

Spec equivalence proofs for other algorithms are ongoing. In the future, we hope that new HACL* implementations will start from the hacspec-generated specs, so that spec equivalence proofs will become unnecessary.


## References

HACL* and its associated proof methodologies have been published in the following papers:

* J. K. Zinzindohoué, K. Bhargavan, J. Protzenko, and B. Beurdouche, “Hacl*: A verified modern cryptographic library,” in Proceedings of the 2017 ACM SIGSAC conference on computer and communications security, CCS 2017, dallas, tx, usa, october 30 – november 03, 2017, 2017, p. 1789–1806.
* J. Protzenko, J. Zinzindohoué, A. Rastogi, T. Ramananandro, P. Wang, S. Zanella-Béguelin, A. Delignat-Lavaud, C. Hritcu, K. Bhargavan, C. Fournet, and N. Swamy, “Verified low-level programming embedded in F*,” PACMPL, vol. 1, iss. {ICFP}, p. 17:1–17:29, 2017. 
* J. Protzenko, B. Beurdouche, D. Merigoux, and K. Bhargavan, “Formally Verified Cryptographic Web Applications in WebAssembly,” in IEEE Symposium on Security and Privacy (S&P), 2019.
* J. Protzenko, B. Parno, A. Fromherz, C. Hawblitzel, M. Polubelova, K. Bhargavan, B. Beurdouche, J. Choi, A. D. -, C. Fournet, N. Kulatova, T. Ramananandro, A. Rastogi, N. Swamy, C. M. Wintersteiger, and S. Z. Béguelin, “Evercrypt: A fast, verified, cross-platform cryptographic provider,” in 2020 IEEE symposium on security and privacy, SP 2020, san francisco, ca, usa, may 18-21, 2020, 2020, p. 983–1002.
* M. Polubelova, K. Bhargavan, J. Protzenko, B. Beurdouche, A. Fromherz, N. Kulatova, and S. Z. Béguelin, “Haclxn: verified generic SIMD crypto (for all your favourite platforms),” in CCS ’20: 2020 ACM SIGSAC conference on computer and communications security, virtual event, usa, november 9-13, 2020, 2020, p. 899–918





