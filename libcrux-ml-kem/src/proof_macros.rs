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
