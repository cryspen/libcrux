# Hacspec-style SHA-3 specification

This is a hacspec-style Rust implementation of SHA-3, closely following FIPS-202. Its purpose
is to serve as a reference implementation for verifying functional correctness of more efficient
implementations.

## Extraction via HAX

### F*

Prerequisites:
* Hax 0.3.6 (https://github.com/cryspen/hax/tree/87ba96831ecfeb7dbb54efcf97036fbc5f25bc71)
* F* 2026/03/24
  (https://github.com/FStarLang/FStar/releases/tag/v2026.03.24)

Run `hax_fstar.sh extract` to produce the F* files, and `hax_fstar.sh prove` to type-check them.

### Lean

Prerequisites:
* Hax `cargo-hax-v0.4.0` (mainline https://github.com/cryspen/hax, commit
  `f8fe6933`) providing the `lean` backend, with the charon/aeneas binaries pinned
  workspace-wide in `specs/hax.toml` (aeneas `nightly-2026.09.03-6852e64`, charon
  `nightly-2026.09.02`; `cargo hax tools install` fetches them).
* The Hax Lean proof library `cryspen/hax-lean` at `v0.3.17` and Lean toolchain
  `leanprover/lean4:v4.31.0` (both pulled in via `proofs/lean/lakefile.toml`).

The extraction is the hax scenario declared in `hax.toml` (`[scenario.hacspec-sha3]`;
`ml-kem/hax.toml` and `ml-dsa/hax.toml` declare the sibling crates' scenarios, and
`cargo hax extract` from `specs/` runs all three). Run `cargo hax extract` here to
extract, then `cd proofs/lean && lake build` to type-check. There is no
post-processing: the former `hax_aeneas.py` driver is gone. The generated
`proofs/lean/HacspecSha3/Extraction/ProofObligations.lean` (sorry-stubbed proof
obligations) is left on disk and imported by nothing.