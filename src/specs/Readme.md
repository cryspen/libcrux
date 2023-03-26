# Specifications (hacspec)

This directory contains specifications for primitives in libcrux.
These are the basis for the correctness proofs of the efficient primitives in [src].

| Algorithm          | HACL                                                                        | libjade                       | AU curves                       |
| ------------------ | --------------------------------------------------------------------------- | ----------------------------- | ------------------------------- |
| [Chacha20]         | [✔](../Architecture.md#hacl)[✍🏻](../proofs/hacl/Hacspec.Chacha20.Proof.fst) | [✔](../sys/libjade/Readme.md) |                                 |
| [Poly1305]         | [✔](../Architecture.md#hacl)[✍🏻](../proofs/hacl/Hacspec.Poly1305.Proof.fst) | [✔](../sys/libjade/Readme.md) |                                 |
| [Chacha20Poly1305] | [✔](../Architecture.md#hacl)✍🏻                                              |                               |                                 |
| [Curve25519]       | [✔](../Architecture.md#hacl)                                                | [✔](../sys/libjade/Readme.md) |                                 |
| [Sha2 256]         | [✔](../Architecture.md#hacl)                                                |                               |                                 |
| [Bls12-381]        |                                                                             |                               | [✔](../au_curves/Readme.md)🧪✍🏻 |

- ✔ implementation
- ✍🏻 proof
- 🧪 property based testing

[src]: ../src/
[chacha20]: chacha20.rs
[poly1305]: poly1305.rs
[chacha20poly1305]: chacha20poly1305.rs
[curve25519]: curve25519.rs
[sha2 256]: sha256.rs
[bls12-381]: bls12-381.rs
