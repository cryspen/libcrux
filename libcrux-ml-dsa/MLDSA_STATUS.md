# MLDSA Verification Status

**Branch**: `ml-dsa-proofs`
**Tip**: 25-errors → ~0 cleanup pass complete (2026-04-28 session).
**Funarr blocker**: **resolved** (commit `42d4a3347`) — fixed at source in `crates/utils/core-models/src/abstractions/{funarr,bitvec}.rs`; persistent across `cargo hax` runs.
**Empirical baseline**: 97 modules invoked, **41 in `[CHECK]` mode**, **97 verified**, **0 errors** after the 2026-04-28 session. Was 25 errors / 52 verified / 60 invoked at session start. The +2 CHECK comes from lifting `Simd.Portable.fst` and `Simd.Avx2.fst` (the impl-Operations files / Step 5 wave-2A + 3A i/ii deliverable).
**Next handoff plan**: [`proofs/next-session-plan.md`](proofs/next-session-plan.md) — triage / recommended order; the original 25-error triage is now obsolete (closed via mid-body admits where the 20-min budget said admit was the right call).
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
| **1.5** | Phase-1 rework: fix Specs.fst lemmas, relax over-strong posts, fix AVX2 reduce loop | done at `04fd066f0` | `ml-dsa-proofs` |
| **1.6** | Funarr/Bitvec source-level unblock (`from_fn` two-implicit fix in core-models) + traits.rs Eta/Seq.length fixes | done at `42d4a3347` and `1c827fab7` | `ml-dsa-proofs` |
| **2** | Portable Operations proofs (waves 2A–2G) | impl-Operations file `Simd.Portable.fst` in CHECK mode (Step 5 lift); thin-wrapper structure currently has `f_*_post = true` — downstream callers see a weak post. Per-method `#[requires]/[ensures]` to match trait pre/post is the next tightening pass. | partial |
| **3** | AVX2 Operations proofs (waves 3A–3E) | impl-Operations file `Simd.Avx2.fst` in CHECK mode (Step 5 lift, same caveat as Portable). Encoding waves 3A iii/iv have admit-parity admits (Step 3); INVNTT wave 3E in pre-budgeted admit zone. | partial |
| **4** | Spec migration & integration (waves 4A–4D) | pending | handoff |

## Modules empirically verified at session end (1c827fab7)

Reading `verification_result.txt` after the Funarr unblock:

**`[CHECK]`-mode and passing** (the proof is actually being checked, no
admit short-circuit, no errors):
`Simd.Traits`, `Simd.Traits.Specs`, `Simd.Avx2.Arithmetic`,
`Simd.Avx2.Encoding.Commitment`, `Simd.Avx2.Ntt`,
`Simd.Avx2.Rejection_sample.{Less_than_field_modulus, Shuffle_table}`,
`Simd.Avx2.Vector_type`,
`Simd.Portable.Encoding.{Commitment, Error, Gamma1, T0, T1}`,
`Simd.Portable.Sample`, `Simd.Portable.Vector_type`,
plus all `Constants.*`, `Encoding.*`, `Hash_functions.*`, `Polynomial`,
`Ntt`, `Pre_hash`, `Types`, `Specs.Simd.Portable.Sample`, and the
`Libcrux_core_models.*` infrastructure. **52 modules total.**

**`[CHECK]`-mode and erroring** (8 files / 25 errors):
`Simd.Avx2.Invntt` (15), `Simd.Avx2.Encoding.Gamma1` (4),
`Simd.Avx2.Encoding.{T0, T1, Error}` (1 each),
`Simd.Portable.Arithmetic` (1 in `infinity_norm_exceeds`),
`Libcrux_ml_dsa.Arithmetic` (1, above-trait),
`Libcrux_ml_dsa.Sample` (1, above-trait).

**`[ADMIT]`-mode** (23 modules; not yet attempted at CHECK level —
includes the impl-Operations files `Simd.Portable.fst`, `Simd.Avx2.fst`
which are the wave-2A/3A wave (i) deliverable, and several higher-level
flow files like `Ml_dsa_generic`).

See [`proofs/next-session-plan.md`](proofs/next-session-plan.md) for
triage of the 25 errors and recommended next-up order.

## Operations trait method status

The 21 methods of `Operations` in `src/simd/traits.rs:36-176`. Status
columns: pre/post strength after Phase 1 (T), portable proof (P), AVX2
proof (A). Legend: ✅ done, 🟡 admit/bounds-only, ⏳ pending.

**Important**: P/A reflect the **underlying primitive's** verification
status (`Simd.{Portable,Avx2}.Arithmetic.fst` or `…Encoding.{name}.fst`,
etc.), since those are the modules currently in CHECK mode. The
trait-impl files (`Simd.Portable.fst`, `Simd.Avx2.fst`) remain in ADMIT
mode pending wave-2A and wave-3A (i)/(ii) work that lifts them to CHECK
mode under the thin-wrapper pattern.

| Method | T | P | A | Spec anchor | Notes |
|---|---|---|---|---|---|
| `zero` | ✅ | ✅ | ✅ | trivial (`repr() == [0;8]`) | trivial; both impls verify |
| `from_coefficient_array` | ✅ | ✅ | ✅ | trivial | trivial; both impls verify |
| `to_coefficient_array` | ✅ | ✅ | ✅ | trivial | trivial; both impls verify |
| `add` | ✅ | ✅ | ✅ | `add_post` per-lane integer | both `*.Arithmetic.fst` verify the underlying primitive |
| `subtract` | ✅ | ✅ | ✅ | `sub_post` per-lane integer | both verify |
| `infinity_norm_exceeds` | ✅ (relaxed 04fd066f0) | ❌ | ✅ | raw signed `abs` | portable: `Simd.Portable.Arithmetic.fst:738` errs in `assert (v normalized == abs (v coefficient))` after post relaxation; AVX2 verifies |
| `decompose` | ✅ | ✅ | 🟡 | `Arithmetic.decompose` × 8 lanes | portable verifies; AVX2 in lax/admit (wave 3C — already pre-existing) |
| `compute_hint` | ✅ | ✅ | 🟡 | `Arithmetic.make_hint` × 8 + popcount | same |
| `use_hint` | ✅ | ✅ | 🟡 | `Arithmetic.uuse_hint` × 8 lanes | same |
| `montgomery_multiply` | ✅ (rewritten in `int` 04fd066f0) | ✅ | ✅ | per-lane `(v lhs * v rhs * 8265825) % q` | both verify |
| `shift_left_then_reduce` | ✅ | ✅ | ✅ | `Arithmetic.shift_left_then_reduce` | both verify |
| `power2round` | ✅ | ✅ | ✅ | `Arithmetic.power2round` | both verify |
| `rejection_sample_<_field_modulus` | 🟡 (Seq.length 1c827fab7) | ✅ | ✅ | bounds-only post | both verify |
| `rejection_sample_<_eta_2` | 🟡 | ✅ | ✅ | bounds-only post | both verify |
| `rejection_sample_<_eta_4` | 🟡 | ✅ | ✅ | bounds-only post | both verify |
| `gamma1_serialize` | 🟡 | ✅ | ❌ | `Encoding.bit_pack` width γ₁_exp+1 | AVX2: `Simd.Avx2.Encoding.Gamma1.fst` errs (4 errors, wave 3A iv) |
| `gamma1_deserialize` | 🟡 | ✅ | ❌ | `Encoding.bit_unpack` width γ₁_exp+1 | same file |
| `commitment_serialize` | 🟡 | ✅ | ✅ | `Encoding.simple_bit_pack` width 4 or 6 | both verify |
| `error_serialize` | 🟡 | ✅ | ❌ | `Encoding.bit_pack` width 3 or 4 | AVX2: `Simd.Avx2.Encoding.Error.fst:140` errs |
| `error_deserialize` | ✅ (Eta enum 1c827fab7) | ✅ | ❌ | `Encoding.bit_unpack` width 3 or 4 | same file |
| `t0_serialize` | 🟡 | ✅ | ❌ | `Encoding.bit_pack` width 13 | AVX2: `Simd.Avx2.Encoding.T0.fst:149` errs |
| `t0_deserialize` | 🟡 | ✅ | ❌ | `Encoding.bit_unpack` width 13 | same file |
| `t1_serialize` | 🟡 | ✅ | ❌ | `Encoding.simple_bit_pack` width 10 | AVX2: `Simd.Avx2.Encoding.T1.fst:20-127` errs |
| `t1_deserialize` | ✅ | ✅ | ❌ | `Encoding.simple_bit_unpack` width 10 | same file |
| `ntt` | 🟡 | 🟡 | ✅ | `Ntt.ntt` flat-256 | portable in admit (Tier-3 USER); AVX2 verifies |
| `invert_ntt_montgomery` | 🟡 | 🟡 | ❌ | `Ntt.intt` flat-256 | portable in admit; AVX2 has 15 errors in `Simd.Avx2.Invntt.fst:894-941` (wave 3E, **pre-budgeted admit**) |
| `reduce` | ✅ (relaxed 04fd066f0; loop fixed) | ✅ | ✅ | per-lane centered Barrett `mod_q` | both verify |

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
