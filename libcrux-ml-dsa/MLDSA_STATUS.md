# MLDSA Verification Status

**Branch**: `ml-dsa-proofs`
**Sprint plan**: [`proofs/sprint-plan.md`](proofs/sprint-plan.md)
**Style guide**: [`proofs/proof-style-guide.md`](proofs/proof-style-guide.md)
**Outstanding admits**: [`proofs/outstanding-admits.md`](proofs/outstanding-admits.md)

## Spec hierarchy (DO NOT FORGET)

- ✅ **Canonical**: `Hacspec_ml_dsa.*` — in
  `specs/ml-dsa/proofs/fstar/extraction/Hacspec_ml_dsa.*.fst`. ALL new
  proofs and post-conditions cite this.
- ⚠️ **Obsolete (scheduled for deletion)**: `Spec.MLDSA.Math`,
  `Spec.MLDSA.Ntt`, `Spec.Intrinsics`. Cited only by
  `montgomery_multiply` post and AVX2 NTT. Banner-marked. Removed in
  Phase 4.
- 🔄 **Temporary scaffolding**: `Spec.Utils.*` — shared with ML-KEM via
  `proofs/fstar/extraction/Makefile:36`. Pieces we use will move to a
  future `Proof_utils.*` module.

## Quick links

- [Sprint plan](proofs/sprint-plan.md) — phase structure, parallelism, 20-min rule
- [ML-KEM proof-style guide](../libcrux-ml-kem/proofs/proof-style-guide.md) — original methodology
- [ML-KEM status](../libcrux-ml-kem/MLKEM_STATUS.md) — sister-effort tracker

## 20-minute proof rule

Every proof attempt has a hard wall-clock budget of **20 minutes**. If a
proof does not close in that window:

1. Mark the function as admitted using one of:
   - `#[hax_lib::fstar::verification_status::panic_free]` on the Rust function, OR
   - `hax_lib::fstar!("admit()")` at the top of the function body
2. Document in `proofs/outstanding-admits.md` (file:line, diagnosis, suggested mitigation).
3. Move on.

Goal: maximum easy-proof coverage in the sprint window. Hard proofs go
to the USER lane (math-heavy or Z3-blocked) for human follow-up.

## Phase status

| Phase | Description | Status | Owner / branch |
|---|---|---|---|
| **0** | Hardening + scaffolding (FIPS fixes, cross-spec tests, mirror docs, hacspec extensions) | done | `ml-dsa-proofs` |
| **1** | Strengthen Operations trait posts | done | `ml-dsa-proofs` |
| **2** | Portable Operations proofs (waves 2A–2G) | unblocked | handoff |
| **3** | AVX2 Operations proofs (waves 3A–3E) | unblocked | handoff |
| **4** | Spec migration & integration (waves 4A–4D) | pending | handoff |

## Operations trait method status

The 21 methods of `Operations` in `src/simd/traits.rs:36-176`. Status
columns: pre/post strength after Phase 1 (T), portable proof (P), AVX2
proof (A). Legend: ✅ done, 🟡 admit/bounds-only, ⏳ pending.

| Method | T | P | A | Spec anchor | Notes |
|---|---|---|---|---|---|
| `zero` | ✅ | ⏳ | ⏳ | trivial (`repr() == [0;8]`) | already strong |
| `from_coefficient_array` | ✅ | ⏳ | ⏳ | trivial | already strong |
| `to_coefficient_array` | ✅ | ⏳ | ⏳ | trivial | already strong |
| `add` | ✅ | ⏳ | ⏳ | `Polynomial.poly_add` | per-lane integer post (already strong, kept) |
| `subtract` | ✅ | ⏳ | ⏳ | `Polynomial.poly_sub` | per-lane integer post (already strong, kept) |
| `infinity_norm_exceeds` | ✅ | ⏳ | ⏳ | `Arithmetic.coeff_norm` lifted | opaque post via `infinity_norm_exceeds_post` |
| `decompose` | ✅ | ⏳ | ⏳ | `Arithmetic.decompose` × 8 lanes | per-lane opaque `decompose_lane_post` + dual-trigger lemmas |
| `compute_hint` | ✅ | ⏳ | ⏳ | `Arithmetic.make_hint` × 8 + popcount | per-lane bool→0/1 conversion captured |
| `use_hint` | ✅ | ⏳ | ⏳ | `Arithmetic.uuse_hint` × 8 lanes | spec name has typo `uuse_hint` |
| `montgomery_multiply` | ✅ | ⏳ | ⏳ | per-lane `mod_q(a·b·R⁻¹)` | both `Spec.MLDSA.Math.mod_q` (kept) and `Hacspec_ml_dsa.Arithmetic.mod_q` posts in parallel; Phase 4A drops obsolete |
| `shift_left_then_reduce` | ✅ | ⏳ | ⏳ | `Arithmetic.shift_left_then_reduce` | per-lane opaque post |
| `power2round` | ✅ | ⏳ | ⏳ | `Arithmetic.power2round` | per-lane opaque post; spec returns (r1, r0) |
| `rejection_sample_<_field_modulus` | 🟡 | ⏳ | ⏳ | `Encoding.coeff_from_three_bytes` | bounds-only; lane post deferred to Phase 2 (admit doc) |
| `rejection_sample_<_eta_2` | 🟡 | ⏳ | ⏳ | `Encoding.coeff_from_half_byte` | bounds-only; admit doc |
| `rejection_sample_<_eta_4` | 🟡 | ⏳ | ⏳ | `Encoding.coeff_from_half_byte` | bounds-only; admit doc |
| `gamma1_serialize` | 🟡 | ⏳ | ⏳ | `Encoding.bit_pack` width γ₁_exp+1 | length-preserving post; bitvec deferred (admit doc) |
| `gamma1_deserialize` | 🟡 | ⏳ | ⏳ | `Encoding.bit_unpack` width γ₁_exp+1 | gamma1_exponent precondition added; bitvec deferred |
| `commitment_serialize` | 🟡 | ⏳ | ⏳ | `Encoding.simple_bit_pack` width 4 or 6 | length-preserving post; admit doc |
| `error_serialize` | 🟡 | ⏳ | ⏳ | `Encoding.bit_pack` width 3 or 4 | length-preserving post; admit doc |
| `error_deserialize` | ✅ | ⏳ | ⏳ | `Encoding.bit_unpack` width 3 or 4 | per-lane bounds [-η, η] |
| `t0_serialize` | 🟡 | ⏳ | ⏳ | `Encoding.bit_pack` width 13 | length-preserving post; admit doc |
| `t0_deserialize` | 🟡 | ⏳ | ⏳ | `Encoding.bit_unpack` width 13 | bitvec deferred |
| `t1_serialize` | 🟡 | ⏳ | ⏳ | `Encoding.simple_bit_pack` width 10 | length-preserving post; admit doc |
| `t1_deserialize` | ✅ | ⏳ | ⏳ | `Encoding.simple_bit_unpack` width 10 | per-lane bounds [0, 2¹⁰) |
| `ntt` | 🟡 | ⏳ | ⏳ | `Ntt.ntt` flat-256 | bounds-only post (existing); per-poly admit (Tier-3 chain, USER lane) |
| `invert_ntt_montgomery` | 🟡 | ⏳ | ⏳ | `Ntt.intt` flat-256 | bounds-only post (existing); per-poly admit (USER lane) |
| `reduce` | ✅ | ⏳ | ⏳ | per-lane `mod_q` ∧ `\|x\| < q` | per-lane opaque post + lookup/intro lemmas |

## Pre-budgeted admits

Going in we expect the following will land as admits (worth listing
upfront so a session doesn't burn the 20-min budget on them):

- AVX2 NTT layers 1–2 — Z3-blocked on 4-zeta parallel SIMD wall (ML-KEM USER-4 analog).
- AVX2 INVNTT layers 1–2 — analogous.
- Full NTT composition (Tier-3 chain across 8 layers with BitRev₈ zeta indexing) — likely USER-2 analog.
- `compute_ciphertext_coefficient`-style Barrett-exactness enumerations — USER-1 analog.

## FIPS 204 audit

Read-only audit dated 2026-04-27 produced 33 findings (no Critical, 4
High, 12 Medium, 16 Low/cosmetic). Implementation conforms in all
correctness-critical respects (interop-tested against PQ-Crystals
KATs).

Items being acted on in Phase 0A (proof simplification benefit):

| ID | Sev | Location | Status |
|---|---|---|---|
| F4 | High | `src/encoding/signature.rs:33-49` (HintBitPack zero-pad) | ✅ Phase 0A |
| F3 | High | `src/ml_dsa_generic.rs:359-399` (verify_internal length asserts) | ✅ Phase 0A |
| F5 | High | `src/encoding/signature.rs:90-130` (HintBitUnpack Err semantics) | ✅ Phase 0A |
| F2 | High annotation | `src/pre_hash.rs:26`, `src/ml_dsa_generic.rs:699` (OID DER comment) | ✅ Phase 0A |
| F15 | Med | `src/simd/portable/arithmetic.rs:380-420` (constant-time mask: `\|\|` → `\|`) | ✅ Phase 0A |
| F13 | Med | `src/matrix.rs::vector_times_ring_element` + 3 callers in `ml_dsa_generic.rs` | **Deferred** to Phase 2+ — refactor to `(out, lhs, rhs)` signature is bigger than the 20-min Phase-0 budget and the "clone preserves equivalence" lemma it would eliminate is not blocking until sign-loop proofs land |

Items F1, F6–F12, F14, F16–F33 are conformance-confirmations or
cosmetic/perf with no proof impact — deferred past the sprint.

## Cross-spec test activation checklist (for the next session)

The cross-spec test scaffolding lands in Phase 0 with **41 TODO
markers** — every per-Operations-method test is stubbed because the
`Operations` trait, the per-impl SIMD unit types, and the hacspec
helpers are all `pub(crate)`. The scaffolding compiles and the 36
non-stubbed tests pass (`cargo test --features cross-spec-tests`),
but the meat of the tests is one source-side accessibility change
away.

**Activation steps** (next session, ≤30 min):

1. **In `libcrux-ml-dsa/src/simd/traits.rs`**: change
   `pub(crate) trait Operations` → `pub trait Operations` and the
   two consts (`COEFFICIENTS_IN_SIMD_UNIT`, `SIMD_UNITS_IN_RING_ELEMENT`)
   to `pub`. Pattern matches `libcrux-ml-kem/src/vector/traits.rs`
   where the analogous trait is unconditionally `pub`.

2. **In `libcrux-ml-dsa/src/lib.rs`** (under existing `test-utils` feature):
   ```rust
   #[cfg(feature = "test-utils")]
   pub mod simd { pub use crate::simd::*; }
   #[cfg(feature = "test-utils")]
   pub mod polynomial { pub use crate::polynomial::*; }
   ```

3. **In `specs/ml-dsa/src/lib.rs`**: re-export the per-element helpers:
   ```rust
   pub use arithmetic::{decompose, make_hint, use_hint, power2round,
                         shift_left_then_reduce, montgomery_reduce, mod_q};
   pub use encoding::{coeff_from_three_bytes, coeff_from_half_byte,
                       simple_bit_pack, simple_bit_unpack,
                       bit_pack, bit_unpack, hint_bit_pack, hint_bit_unpack};
   pub use ntt::{ntt, intt};
   pub use sampling::sample_in_ball;
   ```

4. **In `libcrux-ml-dsa/tests/cross_spec/{arithmetic,encoding,sampling,ntt,helpers}.rs`
   and `tests/edge_cases.rs`**: each TODO marker has the intended body
   inlined as a comment — uncomment them. Then run
   `cargo test --features cross-spec-tests` to confirm.

After step 4, the per-method tests (24 cross-spec × 2 SIMD variants
where `simd256` is enabled) become real assertions against the
hacspec.

## Documentation cadence

This file MUST be kept in sync after each meaningful step (new
commit or wave complete). The session may close at any time — this
file plus `proofs/outstanding-admits.md` are the resume point.
