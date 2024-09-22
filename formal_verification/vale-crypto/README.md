# Vale Crypto in libcrux

## Vale: Verified Assembly Language for Everest

Vale is a tool for constructing formally verified high-performance assembly language code, with an emphasis on cryptographic code. It uses existing verification frameworks, such as Dafny and F*, for formal verification. It supports multiple architectures, such as x86, x64, and ARM, and multiple platforms, such as Windows, Mac, and Linux. Additional architectures and platforms can be supported with no changes to the Vale tool.
Each assembly implementation in Vale is verified for:

* Memory Safety in the x86 memory model
* Functional Correctness against a formal specification written in F* or Dafny
* Secret Independence, i.e. that control flow and memory accesses do not depend on secrets

Vale Crypto includes verified Intel assembly implementations of
AES-GCM, SHA-2, Poly1305, and the field arithmetic used in Curve25519

## Vale Algorithms in libcrux

The libcrux library currently uses the following verified implementations
from Vale:

* AES-GCM - Intel AES-NI

### Verifying Vale* and Generating Intel assembly

We pull code from the [HACL* repository](https://github.com/hacl-star/hacl-star) and run the verification
on the whole repository using the provided Makefile. The build depends upon [F*](https://www.fstar-lang.org/)
and [Vale](https://github.com/project-everest/vale). Once all the code is verified, the generated assembly code
and C header files are taken from [dist/](https://github.com/hacl-star/hacl-star/tree/main/dist/gcc-compatible).

### Wrapping the Vale C APIs within Rust

For each algorithm we import into libcrux, we inspect the high-level verified APIs provided by Vale and reflect
the correct types and pre-conditions in the libcrux Rust APIs. This is a manual process and is carefully reviewed
by multiple developers. We include pointers to the formal specs, the F* APIs, and the C APIs for all the algorithms we use in libcrux:

* AES-GCM - [Spec](https://github.com/hacl-star/hacl-star/blob/main/vale/specs/crypto/Vale.AES.GCM_s.fst), [F* API](https://github.com/hacl-star/hacl-star/blob/main/vale/code/crypto/aes/Vale.AES.GCM.fsti), [C API](https://github.com/hacl-star/hacl-star/blob/main/dist/gcc-compatible/EverCrypt_AEAD.h)


## Spec Equivalence between Hacspec and Vale

We can formally relate crypo specification in hacspec to those used by HACL*, by first compiling the hacspec to F* and then proving that the two specifications are equivalent in F*.
At this time we have not proved spec equivalence between the two AES-GCM specs.


## References

Vale and its associated proof methodologies have been published in the following papers:

* [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)  
Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson. In Proceedings of the USENIX Security Symposium, 2017. Distinguished Paper Award.
* [A Verified, Efficient Embedding of a Verifiable Assembly Language](https://www.microsoft.com/en-us/research/publication/a-verified-efficient-embedding-of-a-verifiable-assembly-language/)  
Aymeric Fromherz, Nick Giannarakis, Chris Hawblitzel, Bryan Parno, Aseem Rastogi, Nikhil Swamy. In Proceedings of the Symposium on Principles of Programming Languages (POPL), 2019.
* [Verified Transformations and Hoare Logic: Beautiful Proofs for Ugly Assembly Language](https://project-everest.github.io/assets/vale-transformers.pdf)  
Jay Bosamiya, Sydney Gibson, Yao Li, Bryan Parno, Chris Hawblitzel. In Proceedings of the Conference on Verified Software: Theories, Tools, and Experiments (VSTTE) 2020.






