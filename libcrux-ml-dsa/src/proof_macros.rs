//! Crate-wide proof-annotation markers.
//!
//! `proof!` forwards its tokens **verbatim** to `hax_lib::fstar!`, so the
//! extracted F* is byte-for-byte identical to writing `hax_lib::fstar!`
//! directly — i.e. it is *proof-neutral* (it cannot change what F* verifies).
//! Its only job is to give a Rust reviewer a clear "this is an annotation, not
//! code" marker at each call site. The F* *logic* (lemmas / predicates) lives
//! in each module's `mod spec` → `<Module>.Spec`, edited locally with the code;
//! this generic forwarder never changes, so it lives once, here.
//!
//! (Rust requires proc-macros in a separate crate, but a `macro_rules!` can live
//! in-crate; `#[macro_use]` in `lib.rs` makes `proof!` available everywhere.)

macro_rules! proof {
    ($($t:tt)*) => {
        hax_lib::fstar!($($t)*)
    };
}

/// Trusted **inline admit** — a body-position `admit ()` whose trust is
/// *declared* (strategy-A trusted-annotation campaign, G1).
///
/// `trusted_admit!("<category>: <reason>")` is the trust-tagged sibling of
/// `proof!("admit ()")`. The `$reason` is a category-prefixed **Rust-only**
/// annotation (checked by `scripts/annotation_lint.py`), dropped from
/// extraction; the emitted F* is byte-identical to `hax_lib::fstar!("admit ()")`
/// — a single `macro_rules!` layer, exactly like `proof!`, so it inherits the
/// same (span-fix-validated) extraction behaviour.
///
/// The enclosing fn MUST also carry `#[libcrux_macros::trusted(inline-admit)]`.
macro_rules! trusted_admit {
    ($reason:literal) => {
        hax_lib::fstar!("admit ()")
    };
}

/// Trusted **inline assume** — a body-position `assume (…)` whose trust is
/// *declared* (strategy-A trusted-annotation campaign, G1).
///
/// `trusted_assume!("<category>: <reason>", r#"assume (…)"#)` is the
/// trust-tagged sibling of `proof!(r#"assume (…)"#)`. `$reason` is a
/// category-prefixed **Rust-only** annotation; `$body` is the F* payload
/// (may contain `${…}` antiquotes) forwarded verbatim to `hax_lib::fstar!`
/// through a single `macro_rules!` layer — byte-identical to writing the
/// `hax_lib::fstar!` directly.
///
/// The enclosing fn MUST also carry `#[libcrux_macros::trusted(inline-assume)]`.
macro_rules! trusted_assume {
    ($reason:literal, $body:literal) => {
        hax_lib::fstar!($body)
    };
}
