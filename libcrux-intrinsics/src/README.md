This directory contains implementations of intrinsics for AVX2 and NEON.

When compiling to Rust, a set of feature flags ensure that either the arm64.rs
or avx2.rs implementation is used, depending on the choice of target. This is a
normal compilation run where the target determines what intrinsics are used.

When compiling to C, we do not know which target the C code itself will be
compiled for, meaning that we need to retain both the AVX2 and NEON variants in
the source (Rust) code, and defer the choice of target until C compilation-time.
In other words, both NEON and AVX2 variants need to be extracted in a single
Rust compilation run (so as to produce C code for both variants).

In that case, what we do is simply use "placeholders" for both arm64.rs and
avx2.rs, and instruct Eurydice to treat those as "abstract", so as not to
extract the dummy implementations. Those will be provided by hand.

There is currently no static check that the signatures in arm64.rs and
arm64_extract.rs (and avx2.rs and avx2_extract.rs, respectively) correspond,
other than the normal Rust extraction and C extraction are both run on CI on the
same codebase, meaning that if there was a mismatch, it would be caught by one
or the other.
