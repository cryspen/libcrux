# ML-DSA — Formal Verification

This directory holds the [F\*](https://www.fstar-lang.org/) verification of the
`libcrux-ml-dsa` implementation of ML-DSA (FIPS 204). The proofs are produced
from the Rust source by [hax](https://github.com/cryspen/hax), which extracts
the annotated Rust into F\*; F\* then discharges the proof obligations against a
hacspec-style reference specification.

```
src/*.rs  ──hax──▶  proofs/fstar/extraction/*.fst(i)  ──F*/Z3──▶  verified
   ▲ #[hax_lib::requires/ensures/...]      │ spec: proofs/fstar/spec, specs/ml-dsa
   └────────────────────────────────────── └ make check/<Module>.fst
```

Unlike the sibling `libcrux-ml-kem` proofs, ML-DSA verification is a **work in
progress**: the arithmetic core is proven functionally correct, but the
top-level signing/verification API is not yet fully verified (see below). The
authoritative, per-function tally is
[`verification_status.md`](./verification_status.md).

## What is proven

The verification is split across three parameter sets (ML-DSA-44/65/87) and two
SIMD backends (Portable, AVX2). The current state:

1. **Functional correctness of the arithmetic core.** The number-theoretic
   transform (forward and inverse, every layer), Montgomery and Barrett
   reduction, and the coefficient decompose/`make_hint`/`use_hint` machinery
   carry F\* postconditions that tie the SIMD bit-twiddling to the mathematical
   reference spec (`Hacspec_ml_dsa.*`, `Spec.MLDSA.*`) **modulo
   q = 8380417**. Both the Portable and AVX2 SIMD backends implement the same
   `Libcrux_ml_dsa.Simd.Traits.t_Operations` trait contract, so these
   per-operation specs hold uniformly across both.

2. **Memory & panic safety.** Essentially all functions (the exact per-tier tally is
   auto-generated in [`verification_status.md`](./verification_status.md) — not hand-typed
   here) are proven **free of panics and arithmetic overflow** and to respect every callee
   precondition — including essentially all serialization/encoding and support code, much of
   it additionally carrying interval/bounds `ensures`.

3. **Serialization bounds.** The (de)serialization of commitments, errors,
   `gamma1`, `t0`/`t1`, signatures, and keys is verified for the coefficient
   range bounds the higher-level proofs depend on.

### What is *not* yet proven

- **Top-level API (admitted).** The public `sign`, `verify`, and
  `generate_key_pair` (the `ml_dsa_generic` layer) are currently proven
  panic-free but their **functional-correctness `ensures` are admitted** — the
  end-to-end "the signature scheme computes exactly the FIPS-204 reference"
  theorem is not yet closed. The admitted sites are listed under *Body-admit
  sites* in the status document.
- **Rejection sampling (accepted carve-outs).** A small number of `lax` markers
  (in `sample`; the exact set is in the status doc) wrap unbounded
  rejection-sampling loops (`while !done { … }`) whose termination is only
  probabilistic, so F\* cannot discharge termination without a statistical
  argument. These are trusted by design, mirroring ML-KEM's `sample_from_xof`
  carve-out.
- **Not extracted.** `src/simd/tests.rs` (6 test functions) is filtered out of
  extraction.

This is therefore a *mixed* verification result: the arithmetic is proven
correct and the whole crate is (almost entirely) panic-safe, but the top-level
signature scheme is not yet an end-to-end functional-correctness proof. It is
also not a cryptographic (EUF-CMA) *security* proof — that is out of scope for
this tree.

## Verification state

The authoritative, auto-generated tally lives in
[`verification_status.md`](./verification_status.md) (regenerate with
`generate_verification_status.py`). Headline as of the last run:

| Metric | Count | % |
| --- | --- | --- |
| Total functions | 618 | |
| **Panic-safe** (panic-free + spec-bearing) | 599 | **96.9%** |
| &nbsp;&nbsp;— cites high-level hacspec | 91 | 14.7% |
| &nbsp;&nbsp;— interval/bounds ensures | 86 | 13.9% |
| &nbsp;&nbsp;— other non-trivial ensures | 152 | 24.6% |
| &nbsp;&nbsp;— panic-free only | 270 | 43.7% |
| Lax (admitted) | 13 | 2.1% |
| Unverified (not extracted) | 6 | 1.0% |

Of the 13 `lax`, ~5 are the accepted rejection-sampling carve-outs above; the
rest (top-level `sign`/`verify`/`keygen` bodies) are the actionable work-list.
The 6 unverified are the `src/simd/tests.rs` test helpers. See
`_excluded_modules` in `verification_status.config.json` for out-of-scope code.

## Reproducing the results

Toolchain (pinned): F\* `2026.03.24`, Z3 `4.13.3`, `cargo-hax` `0.3.7`.

```sh
# 1. Extract Rust → F* (regenerates proofs/fstar/extraction/*.fst(i))
cd libcrux-ml-dsa
./hax.sh extract

# 2. Verify everything with F* (uses .fstar-cache/ for incremental checking)
cd proofs/fstar/extraction
make                                            # full crate
make check/Libcrux_ml_dsa.Simd.Portable.Ntt.fst # a single module

# 3. Regenerate the status table
cd ../../..            # back to libcrux-ml-dsa/
python3 proofs/generate_verification_status.py

# 4. Run the implementation test suite
cargo test --features simd256              # AVX2  (on x86-64)
cargo test                                 # Portable
```

A module verifies cleanly when F\* prints `Verified module: <M>` /
`All verification conditions discharged successfully`. The proofs verify
**with hints** (`--use_hints`); the recorded `.hints` files are checked in.

## Layout

| Path | Contents |
| --- | --- |
| `fstar/extraction/` | hax-extracted `.fst`/`.fsti` + the `Makefile` (the proofs) |
| `fstar/spec/`, `../../specs/ml-dsa/` | the hacspec reference spec + commute lemmas |
| `verification_status.md` | auto-generated per-function proof-tier tally |
| `generate_verification_status.py` / `.sh`, `verification_status.config.json` | status generator |
