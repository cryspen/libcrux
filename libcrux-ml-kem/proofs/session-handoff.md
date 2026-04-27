# Session handoff — trait-opacify branch

**Branch**: `trait-opacify` (worktree at `~/libcrux-trait-opacify`).
**Tip**: `1c47e3632` (pushed to `origin/trait-opacify`).

## Spec hierarchy — DO NOT FORGET

- ✅ **Canonical**: `Hacspec_ml_kem.*` — the only spec we cite from new
  proofs.  Lives in `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.*`.
- ⚠️ **Obsolete (scheduled for deletion)**: `Spec.MLKEM.*`.  Banners on:
  - `proofs/fstar/spec/Spec.MLKEM.fst`
  - `proofs/fstar/spec/Spec.MLKEM.Math.fst`
  - `proofs/fstar/spec/Spec.MLKEM.Instances.fst`
  Existing citations (mostly in `Serialize.fsti`) are migrating; do NOT
  add new ones.
- 🔄 **Temporary scaffolding**: `Spec.Utils.*` — pieces we use will move
  to a future `Proof_utils.*` module.

## What's done (Phases 1–5 of trait-opacify)

- 11 per-lane / per-branch `[@@ "opaque_to_smt"]` predicates in
  `src/vector/traits.rs::spec` (compress/decompress lane_post,
  ntt/inv_ntt layer branch_post, ntt_multiply branch_post).
- Trait posts refactored: `forall16/4` stays transparent; the inner FE
  body is opaque.  Callers iterate per-lane/per-branch as opaque atoms
  without the FE-algebra body flooding their SMT context.
- Two helper lemmas in `traits::spec`:
  - `lemma_bounded_i16_array_lookup` — dual-trigger SMTPat
    `[SMTPat (Seq.index x i); SMTPat (bounded_i16_array lo hi x)]`,
    fires per-index only when both appear together.
  - `lemma_bounded_i16_array_intro` — explicit, no SMTPat.  Used 4× in
    `serialize.rs` for the intro direction.
- Impl-side reveals: 38 in portable.rs, 17 in avx2.rs, 2 in
  `Hacspec_ml_kem.Commute.Chunk.fst`.  Above-trait modules (Polynomial,
  Ntt, Invert_ntt, Matrix, Sampling, Serialize) have **zero** reveals
  of the new opaque predicates — design goal preserved.
- All three trait-boundary admits dropped:
  - `Libcrux_ml_kem.Polynomial.fst` (Phase 3, commit `9f154fd80`)
  - `Libcrux_ml_kem.Invert_ntt.fst` (Phase 4, commit `9f154fd80`)
  - `Libcrux_ml_kem.Serialize.fst` (Phase 5, commit `1c47e3632`)
- Side fixes: serialize.rs val/let order for serialize_{1,4}_lemma;
  hash_functions::neon and downstream gated `cfg(not(hax))`;
  `add_standard_error_reduce` rlimit 300 → 600.

Verification: 53 Checked / 4 Admitted (pre-existing) / 1 Failed
(pre-existing decidable-eq on Vector.Neon.Vector_type.fsti, unrelated).

## What's open (Phase 6 + post-strengthening)

### Phase 6 — drop the 6 portable NTT-layer impl admits
File: `src/vector/portable.rs`, lines 331, 410, 488, 563, 638, 715.
All currently `--admit_smt_queries true`:
- `op_ntt_layer_{1,2,3}_step`
- `op_inv_ntt_layer_{1,2,3}_step`

Approach: use **fstar-mcp** to iterate on just the offending file
(seconds per attempt vs. 20+ minutes for full hax extract+prove).  Each
op_* method already has a `reveal_opaque (\`%X_step_branch_post)` of
the new opaque predicate, plus the existing 8 butterfly_pair_commute
calls + `forall4 p_layer_X` assertion.  Either the reveal is in the
wrong scope or rlimit/structure tweaks are needed.

### Phase 7 — Above-trait post-strengthening (post-only)

Module-by-module strengthening to cite `Hacspec_ml_kem.*`.  Pre-conditions
NEVER touched; posts only get NEW conjunctive additions.  Each commit
lands without breaking neighbours.

| # | Phase | Module(s) | Citation target |
|---|---|---|---|
| 7a | Polynomial scalar ops (7 fns) | `Polynomial.fst` | `Hacspec_ml_kem.Polynomial.*` |
| 7b | NTT/inv-NTT layers 1–3 (8 fns) | `Ntt.fst`, `Invert_ntt.fst` | `Hacspec_ml_kem.{Ntt,Invert_ntt}.*` |
| 7c | Serialize re-root | `Serialize.fst` (8 already-cite-Spec.MLKEM + 6 trivial) | `Hacspec_ml_kem.Serialize.*` (added alongside Spec.MLKEM, then Spec.MLKEM dropped) |
| 7d | Matrix (4 fns Medium + 1 Hard) | `Matrix.fst` | `Hacspec_ml_kem.Matrix.*` |
| 7e | Phase 6 (parallel) | portable.rs admits | n/a |
| 7f-i | Hard cases | full NTT, ntt_multiply, to_standard_domain, compute_vector_u, invert_ntt_montgomery | `Hacspec_ml_kem.*` |
| 7j | Migrate downstream Ind_cpa/Ind_cca | n/a | drop Spec.MLKEM lookups |
| 7k | Drop Spec.MLKEM conjuncts in Serialize.fst | n/a | redundant-conjunct cleanup |
| 7l | **Delete `Spec.MLKEM.*` module** | drop files | |
| 7m | `Spec.Utils` → `Proof_utils` migration | symbol-level rewrite | |

### Required new commute infrastructure (in `Hacspec_ml_kem.Commute.Chunk.fst`)

**Tier 1 — per-poly composition** (built from existing per-element lemmas
via `Classical.forall_intro` over 16 vectors × 16 lanes = 256 elements):
- `lemma_add_to_ring_element_poly_commute`
- `lemma_subtract_reduce_poly_commute`
- `lemma_poly_barrett_reduce_poly_commute`
- `lemma_add_error_reduce_poly_commute`
- `lemma_add_standard_error_reduce_poly_commute`
- `lemma_add_message_error_reduce_poly_commute`
- `lemma_multiply_by_constant_poly_commute`

**Tier 2 — NTT layer-step commute**:
- `lemma_ntt_layer_n_commute (layer ∈ {1,2,3})`
- `lemma_inv_ntt_layer_n_commute`

**Tier 3 — full-NTT composition** (Hard):
- `lemma_ntt_full_commute` (chain 7 layers)
- `lemma_invert_ntt_full_commute` (with Montgomery scale-by-3303)
- `lemma_ntt_multiply_commute` (128-iteration loop over A1–A4)

**Tier 4 — matrix/vector composition**:
- `lemma_add_vectors_commute`, `lemma_sub_vectors_commute`
- `lemma_multiply_matrix_by_column_commute`
- `lemma_compute_message_commute`, `lemma_compute_ring_element_v_commute`,
  `lemma_compute_vector_u_commute`, `lemma_compute_As_plus_e_commute`

## Resume checklist for the next session

1. `cd ~/libcrux-trait-opacify`.
2. `git status` — should be clean on `trait-opacify`.
3. `git log --oneline -5` — confirm `1c47e3632` is at the top (or a
   newer Phase 6/7 commit).
4. Read this file + `MLKEM_STATUS.md` for the latest plan.
5. **Default to `fstar-mcp` for proof iteration** — avoids ~20-min full
   hax extract+prove cycles when only a single F* file is in flight.
6. Use the `proofdebugging` skill for systematic Z3 failure triage
   (`--query_stats`, `--split_queries`, binary-search with `admit()`).

## Useful constants and patterns

- Verification: `cd libcrux-ml-kem && python3 hax.py extract && python3 hax.py prove`.
- Per-module: `make Libcrux_ml_kem.<Module>.fst.checked` from
  `libcrux-ml-kem/proofs/fstar/extraction/`.
- Single-file iteration: fstar-mcp session loaded with the right include
  paths (matches Makefile.generic).
- `verification_result.txt` always reflects the LAST `python3 hax.py prove`
  run.  TOTAL TIME entries give pure F* per-module CPU times.

## Outstanding admits / deferred proofs (full roster)

Mapped to phases so nothing falls through.  See `MLKEM_STATUS.md` for the
canonical version of this table.

### Trait-impl layer

- **6 portable NTT-layer ops** (`--admit_smt_queries true`) →
  **Phase 6** above.  Lines 331, 410, 488, 563, 638, 715 in
  `src/vector/portable.rs` (op_ntt_layer_{1,2,3}_step +
  op_inv_ntt_layer_{1,2,3}_step).
- **4 AVX2 NTT-layer 1/2 bridge admits** in `src/vector/avx2.rs`
  (`op_ntt_layer_{1,2}_step_bridge`, `op_inv_ntt_layer_{1,2}_step_bridge`)
  → **Phase 6 extension** or defer.  Z3-blocked on the 4-zeta-parallel
  SIMD wall; mitigation is per-zeta-sub-function refactor or the SIMD
  model unification (`proofs/simd-model-unification-plan.md`).
- **A8** (`lemma_compress_ciphertext_coefficient_fe_commute` in
  `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`,
  admitted with statement preserved) → **Phase 7a prerequisite**.
  Barrett-exactness 4-case math; closing it strengthens
  `compress_then_serialize_{10,11,4,5}` downstream posts.
- **`op_ntt_multiply` is `panic_free` on portable + AVX2** →
  **Phase 7i**.  Blocked on Tier-3 layer composition (the 128-iteration
  loop over A1–A4 base-case mults).
- **7 AVX2 serialize/deserialize bridges** (admitted in `avx2.rs`
  fstar::before block) → out-of-scope here; separate effort.
- **AVX2 `Vector.Avx2.Sampling.fst` / `Vector.Avx2.Compress.fst`** —
  3× `admit ()` each, pre-existing → out-of-scope.

### Above-trait modules

- **`Sampling.sample_from_uniform_distribution_next`**
  `--admit_smt_queries true` on the rejection loop body → out-of-scope
  (orthogonal to Hacspec_ml_kem migration).
- **`Ind_cpa.fst`** module admit → **Phase 7j** (migrate downstream off
  `Spec.MLKEM`).
- **`Ind_cca.Unpacked.fst`** module admit → **Phase 7j**.

### Pre-existing Vector.Neon

- All `Vector.Neon.*` modules in ADMIT_MODULES → out-of-scope (no Neon
  proofs done).
- `Vector.Neon.Vector_type.fsti(10,0-13,1)` Error 162 (decidable-eq) →
  out-of-scope.  Only Failed module in `hax.py prove`.

## File references

- `MLKEM_STATUS.md` — top-level status with table of completed/open phases.
- This file — session handoff with detailed plan + resume checklist.
- `proofs/c4f-handoff.md` — pre-trait-opacify state (historical).
- `proofs/commutativity-handoff.md` — older commute infra docs (historical).
- `proofs/fstar/spec/Spec.MLKEM*.fst` — banner-marked obsolete files.

## Update cadence

These two files (`MLKEM_STATUS.md`, `proofs/session-handoff.md`) MUST be
kept in sync as work progresses.  After each meaningful step (new commit
or phase complete), update both — the session may close at any time.
