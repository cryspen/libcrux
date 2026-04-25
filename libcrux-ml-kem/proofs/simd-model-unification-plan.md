# Unify the AVX2 SIMD Models Across libcrux-ml-kem and libcrux-ml-dsa

> **STATUS: DEFERRED.** Pick this up **after the trait layer is stabilized
> (i.e., once C4' AVX2 mirror is done and every function in
> `vector/traits.rs` is verified down to SIMD/integer-arithmetic admits)**.
>
> Why deferred: the migration would discharge several of the SIMD
> admits that the in-flight C4' work is currently routing around (see
> "Sequencing relative to in-flight C4' AVX2 work" section below), but
> doing it mid-flight would invalidate proof-state work-in-progress.
> Finishing C4' first leaves the proof state at a clean, well-documented
> bridge-admit boundary; Phase 1 of this migration then discharges
> several of those admits as a side effect.
>
> When picked up, this plan should be moved into the repo (e.g.
> `proofs/simd-model-unification-plan.md` in libcrux-ml-kem) so it is
> discoverable to anyone working on either codebase.

## Context

Two F*-verified Rust crypto crates today use **two parallel, incompatible models** for AVX2 SIMD intrinsics:

- **Model A (ML-KEM)** — hand-written F* `Libcrux_intrinsics.Avx2_extract.fsti` (~76 intrinsics) plus a `BitVec.*` helper library (`fstar-helpers/fstar-bitvec/`). Lane view `vec256_as_i16x16: bit_vec 256 → t_Array i16 (sz 16)` is **abstract** (val, no body). Has the `Tactics.GetBit.prove_bit_vector_equality'` tactic that closes serialize/deserialize bit-pack proofs.
- **Model B (ML-DSA)** — `core-models` Rust crate (`crates/utils/core-models/src/core_arch/x86.rs`, ~1500 lines) extracted to F* via hax. ~88 `#[hax_lib::opaque]` intrinsics + ~10 concrete. Lane view `to_i32x8` / `to_i16x16` is **defined** with inversion lemmas. 62 SMTPat lemmas in `libcrux-ml-dsa/proofs/fstar/spec/Spec.Intrinsics.fsti` auto-fire to close lane-level goals. Rust source is unit-tested against real CPU intrinsics — the model is itself testable.

The two models cannot be intermixed: ML-KEM's `vec256_as_i16x16 v` and ML-DSA's `to_i16x16 v` denote different functions over different bit-vector libraries (`fstar-helpers/fstar-bitvec/BitVec.Bv` vs `core_models::abstractions::bitvec::BitVec`). Every SIMD lemma we write today is doomed to a single repo.

The cost shows up most acutely in our in-flight work: the milestone "every trait fn in `vector/traits.rs` proven down to SIMD + integer-arithmetic admits" lives entirely on Model A and inherits its weak spots — `lemma_mm256_castsi256_si128`, `lemma_mm256_set_epi16`, `lemma_mm256_mullo_epi16`, and the ML-KEM-specific per-control shuffle/permute lemmas all end in `admit ()` because Model A's `vec256_as_i16x16` is abstract.

A single critical observation makes unification tractable: `crates/utils/intrinsics/src/lib.rs:13-19` already wires either model into the same `libcrux_intrinsics::avx2` namespace via a single `#[cfg(... pre_core_models)]` flag. ML-KEM passes `--cfg pre_core_models` (`libcrux-ml-kem/hax.py:71`); ML-DSA does not. The Rust-side toggle is one line.

## Recommendation

**Adopt Model B (`core-models`) as the unified foundation.** Backport Model A's two sharp tools (strong lane-form `ensures` clauses, `Tactics.GetBit` tactic) into `core-models`. Migrate ML-KEM proofs by switching the cfg flag and rewriting a thin compatibility layer.

Why Model B as the base:
- Single Rust source-of-truth, randomized-tested against real CPU (`direct_convertions_tests`) — catches model bugs before F* sees them.
- `vec256_as_i16x16` becomes a definition, not a `val` — the four currently-admitted lane-bridge lemmas in ML-KEM (`lemma_mm256_castsi256_si128`, `lemma_mm256_extracti128_si256_1`, `lemma_mm256_castsi128_si256_lo`, `lemma_mm256_inserti128_si256_1`) become provable for free.
- SMTPat library scales: ML-DSA already has 62 auto-firing lemmas; we can grow this set across both repos with cumulative leverage.
- Executable F* extraction is preserved.

What to backport from Model A:
1. **Strong lane-form `ensures` clauses** for plain-arithmetic intrinsics (add/sub/mul lo/hi). Model B currently exposes lane facts via SMTPat at use sites; Model A exposes them in the post directly. Both work; the post-form is easier to read and avoids one round-trip through Z3.
2. **`Tactics.GetBit.prove_bit_vector_equality'`**, copied into a shared tactics module under `core-models` and the namespace constant in `Tactics.GetBit.fst:42-46` updated to include `Libcrux_core_models.Core_arch.X86`. This tactic is what makes ML-KEM's serialize_{1,4,10,12}/deserialize_{1,4,10,12} closable; ML-DSA does not need it but pays nothing to inherit it.
3. **Per-control specialized lemmas** (`mm256_mullo_epi16_specialized{1,2,3}`, `madd_rhs n`) ported into `core-models` as opt-in `from_fn` definitions guarded by `#[hax_lib::fstar::before("[@@ $REWRITE_RULE]")]`.

## Migration phases for ML-KEM

### Phase 1 — proof of concept (small, end-to-end) — ~1 week

**Goal**: prove the wiring works on one module before sweeping.

Steps:
1. Extend `core-models` with the minimum lemmas needed to spec `mm256_add_epi16` and `mm256_sub_epi16` in lane-form, plus `to_i16x16` ↔ `vec256_as_i16x16` aliasing.
2. Write the compatibility shim `Libcrux_intrinsics.Avx2_extract.fsti`/`.fst` that re-emits the old API as definitions over the core-models types. Just enough to type-check `Libcrux_ml_kem.Vector.Avx2.Arithmetic.fst`. ~50 lines.
3. Drop `--cfg pre_core_models` from hax invocation for the intrinsics crate only (keep ML-KEM's other crates on the old flag if they need it).
4. Re-extract; verify `Libcrux_ml_kem.Vector.Avx2.Arithmetic.fst` passes.

**Critical files**:
- `crates/utils/intrinsics/src/lib.rs` (1 line removal, deferred to Phase 3)
- `crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fsti` (replace with shim)
- `crates/utils/core-models/src/core_arch/x86.rs` (add 2-3 strong-post intrinsics)
- `libcrux-ml-dsa/proofs/fstar/spec/Spec.Intrinsics.fsti` (extend SMTPat coverage as needed)

**Pass condition**: `Vector.Avx2.Arithmetic.fst` verifies with no admits introduced.

### Phase 2 — methodical sweep — 2-4 weeks

Rewrite proofs module-by-module in this order (cheapest first):
1. `Libcrux_ml_kem.Vector.Avx2.fst` (typeclass-only; mostly mechanical renames)
2. `Vector.Avx2.Arithmetic.fst` (already proven in Phase 1 baseline)
3. `Vector.Avx2.Ntt.fst` (lane-form, similar to Arithmetic)
4. `Vector.Avx2.Compress.fst` (lane-form + a few shifts)
5. `Vector.Avx2.Sampling.fst`
6. `Vector.Avx2.Serialize.fst` (GetBit-tactic users — do **after** the namespace fix)

For each module:
- Replace `assert (forall i. get_lane result i == ...)` chains with declarative `ensures` posts that the SMTPat library auto-fires on. Net effect: deletions, not rewrites.
- Update `Tactics.GetBit.fst:42-46` `delta_namespace` list to include `Libcrux_core_models.Core_arch.X86`. One change unblocks all GetBit-style proofs.
- Re-tune Z3 (`rlimit`, `--split_queries`, `--ext context_pruning`) per module if needed.

**Estimated touch count**: ~150 proof sites. Of these, 50-80% are deletions/renames; ~20% need fresh SMTPat lemmas in `Spec.Intrinsics.fsti` for intrinsics ML-KEM uses but ML-DSA does not (e.g., `mm256_shuffle_epi32` per-control variants).

### Phase 3 — cleanup — ~1 week

1. Delete the original `Libcrux_intrinsics.Avx2_extract.fsti` + `.fst` (the hand-written ones; the shim replaces them).
2. Delete `fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti`/`.Constants.fst`/`.TestShuffle.fst` after porting `mm_movemask_epi8_bv`, `mm256_concat_pairs_n`, `mm256_madd_epi16_specialized'`, and `saturate8` to `core-models`.
3. Drop the `pre_core_models` cfg from `crates/utils/intrinsics/src/lib.rs`, `Cargo.toml`, and `libcrux-ml-kem/hax.py:71`.
4. Audit: ensure no admitted lane-bridge lemmas remain.

## Files to modify

- `/root/libcrux-mlkem-proofs/crates/utils/intrinsics/src/lib.rs` — remove `pre_core_models` cfg branch (Phase 3)
- `/root/libcrux-mlkem-proofs/crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fsti` — replace with thin shim (Phase 1) → delete (Phase 3)
- `/root/libcrux-mlkem-proofs/crates/utils/core-models/src/core_arch/x86.rs` — add strong-post `ensures` for arithmetic intrinsics (Phase 1+2); port specialized shuffle/madd lemmas (Phase 2)
- `/root/libcrux-mlkem-proofs/libcrux-ml-dsa/proofs/fstar/spec/Spec.Intrinsics.fsti` — extend SMTPat lemma coverage for intrinsics ML-KEM uses (Phase 2)
- `/root/libcrux-mlkem-proofs/fstar-helpers/fstar-bitvec/Tactics.GetBit.fst` — update `delta_namespace` list (Phase 1.5, before Phase 2 step 6)
- `/root/libcrux-mlkem-proofs/libcrux-ml-kem/hax.py:71` — drop `--cfg pre_core_models` env (Phase 3)
- `/root/libcrux-mlkem-proofs/libcrux-ml-kem/src/vector/avx2/*.rs` — proof-body changes (Phase 2)
- `/root/libcrux-mlkem-proofs/libcrux-ml-kem/src/vector/avx2.rs` — proof-body changes; `op_*` wrappers (Phase 2)
- `/root/libcrux-mlkem-proofs/fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti` — delete (Phase 3)

## Functions / utilities to reuse (already exist)

- `core_models::abstractions::bitvec::BitVec` (`crates/utils/core-models/src/abstractions/bitvec.rs`) — replaces `BitVec.Bv` in fstar-helpers
- `to_i32x8`, `to_i16x16`, inversion lemmas (`Spec.Intrinsics.fsti:119-194`) — replace abstract `vec256_as_i16x16` with definitions
- `bitvec_postprocess_norm` rewrite tactic (`crates/utils/core-models/src/abstractions/bitvec.rs:189-227`) — complements GetBit
- `Tactics.GetBit.prove_bit_vector_equality'` (`fstar-helpers/fstar-bitvec/Tactics.GetBit.fst`) — kept verbatim; just one namespace constant updated
- The cfg toggle `crates/utils/intrinsics/src/lib.rs:13-19` — already wires both models into `libcrux_intrinsics::avx2`

## Sequencing relative to in-flight C4' AVX2 work

**Recommendation: finish C4' AVX2 mirror to a stable bridge-admit state before starting migration.**

C4' is currently mid-stride: 7 admitted serialize/deserialize bridge lemmas + 6 admitted NTT-layer wrapper bridges in `src/vector/avx2.rs`. These bridges are stated against `vec256_as_i16x16`. After Phase 1 of the migration:
- `vec256_as_i16x16` becomes a definition (`= to_i16x16`), not a val.
- The four currently-admitted lane-bridge lemmas (`lemma_mm256_castsi256_si128`, etc.) become provable.
- The 7 serialize bridge admits become discharable via `Tactics.GetBit.prove_bit_vector_equality'` + the new lane-bridge lemmas.

Net effect: **the migration discharges admits the in-flight work has been documenting "removal plans" for**. Sequencing is therefore: (1) finish C4' to a clean state with bridges admitted and removal-plans documented in `MLKEM_STATUS.md`; (2) Phase 1 migration discharges the four lane-bridge admits as a side effect; (3) Phase 2 sweeps simultaneously discharge the remaining bridge admits as the GetBit tactic plumbing is rewired into core-models.

The opposite sequencing (pause C4', migrate first) is **not recommended** because the C4' admits are not caused by Model A's deficiencies; they are pending strengthenings of primitive posts and per-N bridges that need the same proof effort either way.

## Open questions for the user

1. **Naming**: keep `vec256_as_i16x16` as a shim alias for at least Phase 2 (diff-minimal proof migration), or rename uniformly to `to_i16x16` immediately?
2. **Mask extraction soundness**: Model B's `mm_movemask_epi8` is admitted; Model A has a definition (`BitVec.Intrinsics.fsti:117-126`). Port the Model A definition into core-models early so the unified model is strictly stronger?
3. **Tactic deduplication**: keep both `bitvec_postprocess_norm` and `prove_bit_vector_equality'` indefinitely (safer), or invest 1 week unifying them (cleaner)?
4. **Scope**: full unification (Phases 1+2+3), or stop after Phase 1 to validate the approach and revisit?
5. **ML-DSA arithmetic refactor**: retroactively adopt strong lane-form `ensures` for ML-DSA's simple arithmetic (currently per-call-site posts)? Improves consistency but isn't strictly required.
6. **Rust unit-test bar**: require every newly ported intrinsic in core-models to have a `direct_convertions_tests`-style randomized test against the upstream CPU intrinsic? (Recommend yes — this is the main soundness lever.)

## Verification

After each phase:
- `cd libcrux-ml-kem && python3 hax.py extract` — re-extract Rust → F*
- `cd libcrux-ml-kem/proofs/fstar/extraction && make run/<module>.fst` — verify each affected F* module
- `cd crates/utils/core-models && cargo test` — run randomized intrinsic tests
- `cd libcrux-ml-dsa && python3 hax.py extract && make verify` — confirm no ML-DSA regression

End-to-end after Phase 3:
- Full `make` from both `libcrux-ml-kem/proofs/fstar/extraction` and `libcrux-ml-dsa/proofs/fstar/extraction` passes.
- Zero admitted lane-bridge or set-epi16 lemmas in either repo.
- `grep -r "admit_smt_queries\|= admit ()" crates/utils/core-models libcrux-ml-kem libcrux-ml-dsa` returns only known-acceptable cases (e.g., `lemma_compress_ciphertext_coefficient_fe_commute` Barrett admit).
