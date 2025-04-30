//! # Libcrux Secrets
//!
//! This crate implements classification and declassification operations over
//! machine integers and arrays/slices of machine integers
//!
//! To check your code for secret independence, you first identify all the secret
//! values in your code and swap their types to use secret integers:
//! - u8 -> U8, i16 -> I16 etc.
//! - [u8] -> U8, [i16; N] -> [I16; N], etc
//! You should be able to run your code as before with no performance impact
//!
//! Then you can turn on the feature `check-secret-independence` to check
//! whether your code obeys the secret independent coding discipline:
//! - does it branch on comparisons over secret values?
//! - does it access arrays on secret indices?
//! - does it use non-constant-time operations like division or modulus?
//!
//! To convince the typechecker, you will need to convert some public values to secret
//! using `.classify()` operations.
//!
//! In some cases, you may decide that a certain declassification of secret values to
//! public values is safe, and in this case you may use a `.declassify()` operation.
//! However, note that every use of `.declassify()` is at the responsibility of the
//! programmer and represents a potential side-channel leak
//!
mod traits;
pub use traits::*;
mod int;
pub use int::*;
