# MLDSA Verification Status

**Branch**: `ml-dsa-proofs`
**Tip**: Step 9 partial (2026-04-28 session). Both `Operations::infinity_norm_exceeds` and `Operations::power2round` impl bodies discharge for both Portable and AVX2; Portable `Operations::montgomery_multiply` body discharges. Spec.MLDSA.Math reframed as the Tier-1 shared-spec layer.
**Funarr blocker**: **resolved** (commit `42d4a3347`) — fixed at source in `crates/utils/core-models/src/abstractions/{funarr,bitvec}.rs`; persistent across `cargo hax` runs.
**Empirical baseline**: **71 modules invoked (warm cache), [CHECK]=15, [ADMIT]=56, 71 verified, 0 errors, 0 make-level failures**. Cold-cache totals would still match the prior 98 invoked / 42 CHECK / 56 ADMIT (the 5 newly-discharged impl methods all live inside `Simd.Portable.fst` and `Simd.Avx2.fst`, already CHECK modules).

**This session's deltas (Step 8 AVX2)**:
1. **Piece A — per-lane bridge lemmas** (`specs/ml-dsa/proofs/fstar/commute/Hacspec_ml_dsa.Commute.Chunk.fst`): proved `lemma_add_lane_commute` and `lemma_sub_lane_commute` — given `int_is_i32 (v lhs ± v rhs)` (from `add_pre`/`sub_pre`) and `lhs_future == add_mod_opaque lhs rhs` (from the strengthened AVX2 `arithmetic::{add,subtract}` post), conclude per-lane `v lhs_future == v lhs ± v rhs`. Body is just `Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype`.
2. **Piece B — strengthen AVX2 free fns** (`libcrux-ml-dsa/src/simd/avx2/arithmetic.rs:40-52`): added `ensures` clauses to `add` and `subtract` advertising `forall i. to_i32x8 lhs_future i == add_mod_opaque (to_i32x8 lhs i) (to_i32x8 rhs i)` (resp. `sub_mod_opaque`). Discharged for free by the existing `mm256_{add,sub}_epi32_lemma` SMTPat axioms in `Spec.Intrinsics.fsti`. No body admit needed.
3. **Piece C — replace AVX2 add/subtract body admits** (`libcrux-ml-dsa/src/simd/avx2.rs:60-122`): `admit ()` → `let _orig = *lhs; arithmetic::add(...); reveal_opaque add_pre/add_post; pfk forall k<8 → lemma_add_lane_commute; Classical.forall_intro pfk`. The `f_repr` content bridge (Step 7 Piece 1) plus `int_is_i32` instantiation per-k makes the chain go through. Same shape for subtract.

**Operations trait pre-conditions audit (2026-04-28)**: every method's pre
now matches what its Portable free fn requires for panic freedom — a
gap-by-gap audit closed 13 methods (`use_hint`, all `rejection_sample_*`,
all `gamma1_*`, `commitment_serialize`, all `error_*`, all `t0_*`, all
`t1_*`, `reduce`). Bounds preconditions are packaged in opaque
predicate form (reuse of `Spec.Utils.is_i32b_array_opaque`; new
`is_binary_array_8_opaque` in `src/simd/traits/specs.rs`) following the
ML-KEM `bounded_pos_i16_array` pattern. All four `bounded_{add,sub}_{pre,post}`
SMTPat-bridge lemmas now have real `reveal_opaque` + `Classical.forall_intro`
proofs (no admits).
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
| **2** | Portable Operations proofs (waves 2A–2G) | `Simd.Portable.fst` in CHECK mode with all 21 impl methods carrying the strong trait pre/post via `#[hax_lib::attributes]` + per-method `#[requires]/[ensures]` (Step 5 + 5b). Body admits remain on methods whose underlying free-function post is weaker than the trait's. | mostly done |
| **3** | AVX2 Operations proofs (waves 3A–3E) | `Simd.Avx2.fst` in CHECK mode with all 21 impl methods carrying strong trait pre/post in the same Portable shape (Step 5 + 5b extension). All bodies admit since the AVX2 free functions operate on Vec256 (bitvec model) while the trait posts cite `f_repr` (i32x8 view) — bridging needs per-method translation lemmas (deferred). Encoding waves 3A iii/iv have admit-parity admits (Step 3); INVNTT wave 3E in pre-budgeted admit zone. | mostly done |
| **4** | Spec migration & integration (waves 4A–4D) | pending | handoff |

## Modules empirically verified at session end (60f5a9fe9)

Reading `verification_result.txt` after the 2026-04-28 cleanup +
tightening session:

**41 modules in `[CHECK]` mode, all passing**. Notable additions vs
the Funarr-unblock baseline:
- `Simd.Portable.fst` — impl-Operations file, lifted Step 5 + Step 5b.
- `Simd.Avx2.fst` — impl-Operations file, lifted Step 5 + Step 5b.

**56 modules in `[ADMIT]` mode**, including high-level flow files
(`Ml_dsa_generic.*`, `Sample`, the `Hash_functions.*` adapters, the
`Pre_hash` flow, the `Constants.Ml_dsa_*` instantiations).

Total: 97 modules invoked, 97 verified, 0 errors.

See [`proofs/next-session-plan.md`](proofs/next-session-plan.md) for
the recommended next-up order; the original 25-error triage is
historical.

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
| `add` | ✅ | ✅ | ✅ (AVX2 impl closed; this session, Step 8) | `add_post` per-lane integer | both `*.Arithmetic.fst` verify the underlying primitive; AVX2 impl now uses `lemma_add_lane_commute` bridge |
| `subtract` | ✅ | ✅ | ✅ (AVX2 impl closed; this session, Step 8) | `sub_post` per-lane integer | both verify; AVX2 impl uses `lemma_sub_lane_commute` bridge |
| `infinity_norm_exceeds` | ✅ (relaxed 04fd066f0) | ✅ (Portable impl closed; Step 9) | ✅ (AVX2 impl closed; Step 9) | raw signed `abs` | both impls discharge: Portable arithmetic post strengthened to bidirectional `<==>` form; AVX2 trait impl bridges f_repr↔to_i32x8 via to_coefficient_array post |
| `decompose` | ✅ | ✅ | 🟡 | `Arithmetic.decompose` × 8 lanes | portable verifies; AVX2 in lax/admit (wave 3C — already pre-existing) |
| `compute_hint` | ✅ | ✅ | 🟡 | `Arithmetic.make_hint` × 8 + popcount | same |
| `use_hint` | ✅ | ✅ | 🟡 | `Arithmetic.uuse_hint` × 8 lanes | same |
| `montgomery_multiply` | ✅ (rewritten in `int` 04fd066f0) | ✅ (impl closed; Step 9) | 🟡 | per-lane `(v lhs * v rhs * 8265825) % q` | Portable impl now discharges via `lemma_montgomery_multiply_lane_intro` after revealing `Spec.MLDSA.Math.mod_q`; AVX2 impl still admits (needs `lemma_mont_mul_bound_and_mod_q` deferred) |
| `shift_left_then_reduce` | ✅ (relaxed Step 9.3) | ✅ (impl closed; Step 9.3) | ✅ (impl closed; Step 9.3) | centered-Barrett bound + mod-q congruence with `input * 2^13` | post relaxed from strict-equality with Hacspec's `[0,q-1]` form to mod-q congruence + bound (impls return Barrett `(-q,q)`); both impls discharge via the relaxed lane post and new commute lemmas |
| `power2round` | ✅ | ✅ (impl closed; Step 9) | ✅ (impl closed; Step 9) | `Spec.MLDSA.Math.power2round` (Tier-1) → `Arithmetic.power2round` (Tier-3) | both impls discharge via `lemma_power2round_lane_commute` |
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
| `reduce` | ✅ (relaxed 04fd066f0; loop fixed) | ✅ (Portable impl closed `c91f0b413`) | ✅ (AVX2 impl closed; this session) | per-lane centered Barrett `mod_q` | Both Portable and AVX2 trait methods have full proofs |

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
