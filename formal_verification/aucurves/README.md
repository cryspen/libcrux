# AUCurves in libcrux

## AUCurves: High Assurance Cryptography by means of code synthesis.

[AUCurves](https://github.com/AU-COBRA/AUCurves) synthesizes formally verified implementations of pairing-friendly elliptic curves. Currently, it produces implementations of the groups G1 and G2 of the elliptic curve BLS12-381, as well as the quadratic field extension arithmetic underlying G2.

It expands the infrastructure provided by the [Fiat-Crypto] and [Bedrock2] projects. We use the base field arithmetic synthesized by Fiat-Crypto as atomic building blocks in our implementations, and use Bedrock2's "ExprImp" as an intermediate language that allows us to proof correctness of our implementations, while abstracting over a number of parameters such as prime modulos, system bitwidth and curve-defining parameters.

More information on the pipeline can be found in the literature below.

### Properties and Guarantees
Can be found [here](https://github.com/hacspec/rwc-2023-talk/blob/main/libcrux/Architecture.md).

Briefly, the implementation is verified for:

* Memory Safety, since it produces rust
* Functional Correctness against a formal specification written in both Coq and hacspec
* Secret Independence, at least for the code produced by fiat-cryptography, as this is straight-line code.

AUCurves can produce both C and rust code.

## AUCurves Algorithms in libcrux

The libcrux library currently uses the following verified implementations
from AUCurves:

* BLS12-381 - rust

### Verifying AUCurves and Generating code

We pull code from the [AUCurves](https://github.com/AU-COBRA/AUCurves) and run the verification
on the whole repository using the provided Makefile. The build process is explained there.

### Embedding in Rust
The syntesis of bedrock2 code is verified in Coq. We provide a [small file](https://github.com/AU-COBRA/AUCurves/blob/main/src/Bedrock/ToRustString.v) for printing Bedrock2 to rust. This file has not yet been independently audited.

## Spec Equivalence between Hacspec and AUCurves
We provide a hacspec specification of the affine groups G1 and G2 of the BLS12-381 elliptic curve as well as the underlying fields. We prove the equivalence between the bedrock and hacspec implementations, by a chain of equivalence proofs. First, the bedrock implementation is proven equivalent to the gallina specification defined in the file MontgomeryCurveSpecs. This is then proven equivalent to the fiat-crypto specification of the projective Weierstrass curve. Fiat-crypto provides a proof that this is equivalent to the affine Weierstrass curve. Finally, this is proven equivalent to the hacspec implementation.

## References

AUCurves and its associated proof methodologies have been published in the following abstract. A longer paper is in preparation: 
* Workshop paper: Rasmus Holdsbjerg-Larsen, Bas Spitters, Mikkel Milo, [A Verified Pipeline from a Specification Language to Optimized Safe Rust](https://popl22.sigplan.org/details/CoqPL-2022-papers/5/A-Verified-Pipeline-from-a-Specification-Language-to-Optimized-Safe-Rust), CoqPL'22, 2022
* Diego Aranha, Rasmus Holdsbjerg-Larsen, Benjamin Salling Hvass, Bas Spitters, Synthesizing High-Assurance Implementations of Pairing Groups, In progress

As stated, AUCurves depends on:
* [Fiat-Crypto]
* [Bedrock2]

[Fiat-Crypto]: https://github.com/mit-plv/fiat-crypto
[Bedrock2]: https://github.com/mit-plv/bedrock2
