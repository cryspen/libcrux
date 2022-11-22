//! # AU Curves
//!
//! In this project we aim to develop frameworks for synthesizing formally verified implementations of cryptographic primitives.
//! At the moment we are able to produce implementations of groups G1 and G2 of the elliptic curve(s) BLS12-381, as well as the quadratic field extension arithmetic underlying G2.
//!
//! **Our approach**
//! We expand on the infrastructure provided by the Fiat-Crypto and Bedrock2 projects, upon which this project depends.
//! We use the base field arithmetic synthesized by Fiat-Crypto as (as of yet) atomic building blocks in our implementations, and use Bedrock2's "ExprImp" as an intermediate language that allows us to proof correctness of our implementations, while abstracting over a number of parameters such as prime modulos, system bitwidth and curve-defining parameters.
//!
//! **Proving equivalence**
//! We provide a hacspec specification of the affine groups G1 and G2 of the BLS12-381 elliptic curve as well as the underlying fields. We prove the equivalence between the bedrock and hacspec implementations, by doing a chain of equivalence proofs. First the bedrock implementation is proven equivalent to the gallina specification defined in the file MontgomeryCurveSpecs. This is then proven equivalent to the fiat-crypto specification of the projective weierstrass curve. Fiat-crypto provides a proof that this is equivalent to the affine weierstrass curve. Finally, this is proven equivalent to the hacspec implementation.
//!
//! https://github.com/AU-COBRA/AUCurves/

pub mod bls12;
