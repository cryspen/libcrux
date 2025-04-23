//! `minicore`: A Rust Model for the `core` Library
//!
//! `minicore` is a simplified, self-contained model of Rust’s `core` library. It aims to provide
//! a purely Rust-based specification of `core`'s fundamental operations, making them easier to
//! understand, analyze, and formally verify. Unlike `core`, which may rely on platform-specific
//! intrinsics and compiler magic, `minicore` expresses everything in plain Rust, prioritizing
//! clarity and explicitness over efficiency.
//!
//! ## Key Features
//!
//! - **Partial Modeling**: `minicore` includes only a subset of `core`, focusing on modeling
//!   fundamental operations rather than providing a complete replacement.
//! - **Exact Signatures**: Any item that exists in both `minicore` and `core` has the same type signature,
//!   ensuring compatibility with formal verification efforts.
//! - **Purely Functional Approach**: Where possible, `minicore` favors functional programming principles,
//!   avoiding unnecessary mutation and side effects to facilitate formal reasoning.
//! - **Explicit Implementations**: Even low-level operations, such as SIMD, are modeled explicitly using
//!   Rust constructs like bit arrays and partial maps.
//! - **Extra Abstractions**: `minicore` includes additional helper types and functions to support
//!   modeling. These extra items are marked appropriately to distinguish them from `core` definitions.
//!
//! ## Intended Use
//!
//! `minicore` is designed as a reference model for formal verification and reasoning about Rust programs.
//! By providing a readable, well-specified version of `core`'s behavior, it serves as a foundation for
//! proof assistants and other verification tools.

pub mod abstractions;
pub mod arch;
