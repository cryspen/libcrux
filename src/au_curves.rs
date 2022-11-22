//! # Cobra
//!
//! Verified cryptography from the Concordium Blockchain Research Center Aarhus
//! (Cobra).
//!
//! It expands on the infrastructure provided by the Fiat-Crypto and Bedrock2
//! projects, upon which this project depends.
//! It uses the base field arithmetic synthesized by Fiat-Crypto as (as of yet)
//! atomic building blocks in our implementations, and use Bedrock2's "ExprImp"
//! as an intermediate language that allows us to proof correctness of our
//! implementations, while abstracting over a number of parameters such as prime
//! modulos, system bitwidth and curve-defining parameters.

pub use au_curves::*;
