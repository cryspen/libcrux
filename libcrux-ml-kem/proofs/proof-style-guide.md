# Proof style guide — extracted from ML-KEM trait-opacify

This document distills the architectural patterns and proof techniques we
used to drive `libcrux-ml-kem` toward end-to-end proofs.  A parallel agent
session analyzing `libcrux-ml-dsa` should use this as the template; the
phase structure and patterns generalize directly (different module names,
same shape).

## 1. Spec hierarchy convention

Each crate has three tiers of spec modules.  Cite ONLY the canonical tier
from new proofs; the others are migrations or scaffolding.

| Tier | ML-KEM | Status |
|---|---|---|
| ✅ Canonical | `Hacspec_ml_kem.*` (in `specs/ml-kem/proofs/fstar/extraction/`) | Cite this |
| ⚠️ Obsolete (deletion-pending) | `Spec.MLKEM.*` (in `proofs/fstar/spec/`) | DO NOT extend.  Banner-marked. |
| 🔄 Temporary scaffolding | `Spec.Utils.*` | Used pieces will move to `Proof_utils.*` |

**For ML-DSA: identify the equivalent canonical / obsolete / scaffolding
modules early and banner-mark obsolete ones.**

## 2. Architectural pattern: trait at the bottom + opacity

The libcrux pattern: a SIMD-vector trait (`Vector::Operations` in ML-KEM,
`Simd::Traits::Operations` in ML-DSA) provides a uniform 16/8-element
interface.  Above it sit modules (Polynomial, Ntt, Matrix, Serialize, etc.)
that compose the per-vector operations into per-polynomial / per-vector
algorithms.

The trait posts must give STRONG semantic guarantees (not just bounds) so
above-trait modules can lift to spec correspondence.  But strong posts
flood SMT context with FE-algebra equations on every call.  **Solution:
wrap the FE-equation portion in opaque predicates so the iteration
structure (`forall16` / `forall8` / `forall4`) stays transparent but the
hacspec-internal body is hidden.**

### The forall-of-opaque-atoms shape

Trait post structure:
```
bound_predicate
  /\ Spec.Utils.forall_N (fun i -> X_lane_post v.[i] r.[i])
```
where:
- `forall_N` is `unfold let` — always inlines to an N-conjunction.
- `X_lane_post` is `[@@ "opaque_to_smt"]` — body hidden.

Callers iterating over multiple vectors (e.g., 16 vectors × 16 lanes = 256
elements in ML-KEM) see a conjunction of opaque atoms — they can chain them
in loop invariants without paying the cost of unfolding the FE body.

**Predicate granularity to choose**:
- "Per-lane" for compress / decompress / unary ops (one atom per lane,
  each carrying a small equation referencing one input/output i16 pair).
- "Per-branch" for NTT-layer / butterfly ops (one atom per zeta-group,
  each carrying 4 lane equations sharing a zeta).  ML-KEM uses 4 branches
  (`forall4`); ML-DSA may differ.

## 3. Specific F* / Z3 techniques

### 3.1 Opaque predicate definition

```fstar
[@@ "opaque_to_smt"]
let X_lane_post (input result: i16) : prop =
  i16_to_spec_fe result == hacspec_fn (i16_to_spec_fe input)
```

Trait pre/post then references it:
```
ensures r. bound r /\ Spec.Utils.forall_N (fun i ->
  X_lane_post (Seq.index input i) (Seq.index r i))
```

### 3.2 Dual-trigger SMTPat for predicate unfolding

When a predicate's body would be useful at every call site, but a global
SMTPat would over-instantiate, use a **dual trigger** so the lemma fires
only when both the predicate AND a specific lane access are in context:

```fstar
let lemma_X_lookup (lo hi: i16) (x: t_Slice i16) (i: nat)
    : Lemma (requires bounded x lo hi /\ i < Seq.length x)
            (ensures v lo <= v (Seq.index x i) /\ v (Seq.index x i) <= v hi)
            [SMTPat (Seq.index x i); SMTPat (bounded x lo hi)] =
  reveal_opaque (`%bounded) (bounded x lo hi)
```

Z3 fires this only when `Seq.index x i` and `bounded x lo hi` both appear
in the same goal — per-index, not 16-fold.

**Anti-pattern**: bidirectional SMTPat with the SAME trigger.  The unfold
direction (`bounded → forall`) PLUS the intro direction (`forall → bounded`)
on identical triggers cycles or over-instantiates.  We saw it regress
modules that were previously passing.

### 3.3 Named intro lemma (no SMTPat)

For the intro direction (proving the predicate from the unfolded form),
use a NAMED lemma without SMTPat and invoke it explicitly at the few call
sites that need it:

```fstar
let lemma_X_intro (lo hi: i16) (x: t_Slice i16)
    : Lemma (requires forall (i: nat). i < Seq.length x ==>
                       v lo <= v (Seq.index x i) /\ v (Seq.index x i) <= v hi)
            (ensures bounded x lo hi) =
  reveal_opaque (`%bounded) (bounded x lo hi)
```

Caller (in serialize.rs):
```rust
hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.lemma_X_intro
    (mk_i16 0) (mk_i16 3328)
    (Libcrux_ml_kem.Vector.Traits.f_repr ${unreduced})"#);
```

### 3.4 `Classical.forall_intro` for collapsing N manual aux invocations

Where the impl currently has `aux 0; aux 1; ...; aux 15`, replace with:

```rust
hax_lib::fstar!(r#"
  let aux (j: nat{j < 16}) : Lemma (X_lane_post a.[j] r.[j]) =
    lemma_per_lane_commute (Seq.index a j) (Seq.index r j)
  in
  Classical.forall_intro aux
"#);
```

Z3 sees one universally-quantified obligation instead of 16 sequential
SMT queries.  Measured speedup on ML-KEM:
- `op_compress_1`: 9.9 s → 6.5 s (-35 %)
- `op_compress`: 17.4 s → 8.7 s (-50 %)

### 3.5 Per-element commute lemmas

Each per-element transformation has a "fe_commute" lemma in
`specs/.../Commute.Chunk.fst`:

```fstar
let lemma_X_fe_commute (a result: i16) :
  Lemma (requires <integer-form post from primitive>)
        (ensures hacspec_fn (i16_to_spec_fe a) == i16_to_spec_fe result)
  = (* ~5 lines of integer arithmetic + i16_to_spec_fe refinement *) ()
```

ML-KEM has these for: compress_1 (A5), compress<D> (A8 — admitted, hard),
decompress_1 (A6), decompress_d (A7), butterfly_pair, inv_butterfly_pair,
base_case_mult_{even,odd} (A1–A4).

**For ML-DSA: enumerate the analogous primitive operations and write the
per-element commute lemma for each.**

### 3.6 Tier-N composition lemmas (the climb to hacspec citations)

Above the per-element layer, build composition lemmas tier by tier:

- **Tier 1 (poly-level)**: Use `Classical.forall_intro` to lift a per-lane
  commute lemma to a per-vector statement.  Then iterate over the 16
  vectors of a polynomial.  Result: `to_spec_poly_t result == hacspec_fn args`.
- **Tier 2 (NTT layer-step)**: Composes 8 butterfly_pair_commute calls per
  layer step into the hacspec layer's `forall_n` form.  One lemma per
  layer (1, 2, 3) parameterized by the layer.
- **Tier 3 (full NTT)**: Chains 7 layer-step lemmas.  Hard — involves the
  zeta indexing matching the BitRev₇ table exactly.
- **Tier 4 (matrix/vector)**: `add_vectors`, `sub_vectors`,
  `multiply_matrix_by_column` — built from per-poly composition.

### 3.7 The post-only invariant

Every change in the migration phase satisfies:
- Pre-conditions: **never touched**.
- Post-conditions: **only conjunctive additions** (`P /\ to_spec_poly_t r == hacspec_fn args`).

Result: each module commits independently without breaking neighbours.
Critical when running multiple parallel agent sessions.

## 4. Phase methodology

The proof effort follows a strict bottom-up sequence.  Each phase is
independently commit-able and verifiable.

### Phase 1: Design opaque predicates

For each trait method that has FE-form post equations, define one opaque
per-lane (or per-branch) predicate that wraps the equation body.  Add to
the spec module of the trait (in `traits.rs::spec` for ML-KEM).

### Phase 2: Refactor trait posts + impl reveals

Replace `forall_N (fun i -> equation)` with `forall_N (fun i ->
opaque_lane_post v.[i] r.[i])`.  Add `reveal_opaque (\`%lane_post)` in each
impl method that proves the post.  Use `Classical.forall_intro` where
applicable.

### Phase 3+4+5: Drop trait-boundary admits

Modules that were admitted because their loop-accumulator subtyping
flooded SMT context now verify because the per-iteration post is a
constant-size opaque atom.  Drop the admits one by one and verify.

In ML-KEM these were Polynomial.fst, Invert_ntt.fst, Serialize.fst.
**For ML-DSA: identify the analogous heavy-loop modules.**

### Phase 6: Drop impl-side per-method admits

Some impl methods (e.g., portable NTT-layer ops) get temporary
`--admit_smt_queries true` during Phase 2 if their proof needs more work.
Drop those once stable.

**Use `fstar-mcp` for fast per-file iteration here** (seconds vs. ~20
minutes for full hax extract+prove).

### Phase 7: Strengthen above-trait module posts

Module by module, post-only:
- 7a: scalar/poly ops (Polynomial-equivalent)
- 7b: NTT layers 1-3
- 7c: serialize re-root from obsolete spec to canonical spec
- 7d: matrix
- 7e: parallel impl-admit cleanup
- 7f-i: hard cases (full NTT, multiplication, special domain ops)
- 7j: migrate downstream consumers (Ind_cpa / Ind_cca-equivalent)
- 7k-l: drop obsolete-spec citations and delete that spec module
- 7m: scaffolding migration (Spec.Utils → Proof_utils)

## 5. User-vs-agent task split

Some proofs are best left to the user; agents handle pattern-following
work.

### User lane (manual, math-heavy, Z3-blocked)

- **Standalone integer-arithmetic proofs** (e.g., Barrett 4-case in A8;
  Montgomery inverse identity in `to_standard_domain`).
- **SMT-blocked SIMD proofs** (e.g., AVX2 4-zeta-parallel layer where Z3
  can't handle the wide context).
- **Tier-3 layer compositions** with subtle indexing (BitRev₇).
- Anything that hits "incomplete quantifiers" repeatedly even after rlimit
  bumps and split queries.

### Agent lane (mechanical, pattern-following)

- Tier-1 per-poly composition lemmas via `Classical.forall_intro`.
- Tier-2 NTT layer-step commute lemmas.
- Tier-4 matrix/vector composition lemmas.
- Adding hacspec citations to module posts.
- Re-rooting obsolete spec citations to canonical.
- Symbol-level rewrites for module migrations (`Spec.Utils` → `Proof_utils`).
- Phase 6 impl-admit drops.

### Cut-off rules (escalate to user)

- A single Z3 query times out at rlimit ≥ 800 with `--split_queries always`.
- A lemma needs new mathematical reasoning we don't have a pattern for.
- A refactor would change more than ~50 lines of existing proof code.
- Verification time on a single module exceeds 10 minutes pure F* CPU.

## 6. Tooling

- **`fstar-mcp` skill** — incremental F* typechecking via the fstar-mcp
  server.  Default to this for proof iteration.  Avoids the ~20-minute
  full hax extract+prove cycle when working on a single F* file.
- **`proofdebugging` skill** — systematic Z3 failure triage:
  `--query_stats`, `--split_queries`, binary-search with `admit ()`,
  quantifier-instantiation profiling.
- **`hax.py extract` + `hax.py prove`** — full pipeline.  Use for
  end-to-end regression checks, not inner-loop work.
- **Hint files** in `.fstar-cache/hints/` — speed up Z3 query selection
  but don't skip verification.  Already enabled (`ENABLE_HINTS = --use_hints --record_hints`).
- **`Verification cache** in `.fstar-cache/checked/` — skips entire
  modules when their digest hasn't changed.  Helper-lemma changes in a
  trait spec file invalidate the entire cascade; mitigate by factoring
  helpers into a separate hand-written F* file (NOT regenerated by hax).

## 7. Cache-invalidation cost (lesson learned in ML-KEM)

Every change to `traits.rs`'s `fstar::before` block invalidates
`Vector.Traits.Spec.fst`'s digest, which cascades to ~50+ modules and
forces ~15-20 minute full re-verify.

**Mitigation for future work**: factor `bounded_i16_array` and helper
lemmas (lookup, intro) out of the `traits.rs` `fstar::before` block into a
separate hand-written F* file (e.g., `proofs/fstar/spec/Libcrux_ml_kem.Vector.Bounds.fst`)
included via `FSTAR_INCLUDE_DIRS_EXTRA`.  Then helper-lemma additions
invalidate only that file + its direct importers — seconds, not minutes.

This is a structural cleanup task, applicable to both ML-KEM and ML-DSA.

## 8. Documentation cadence

`MLKEM_STATUS.md` and `proofs/session-handoff.md` MUST be kept in sync
after each meaningful step (new commit or phase complete).  The session
may close at any time — both files together are the resume point.

For ML-DSA, the equivalent files would be `MLDSA_STATUS.md` and
`libcrux-ml-dsa/proofs/session-handoff.md`.

## 9. Branch / commit conventions

- Each phase is one commit.  Commit message: imperative, names the phase,
  notes the dropped admit if any.
- Push to remote after each phase or set of related phases.
- `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>`
  on agent-authored commits.

## 10. Specific ML-KEM artifacts to mine for ML-DSA

When designing the ML-DSA plan, the following ML-KEM artifacts are direct
templates:

- `libcrux-ml-kem/src/vector/traits.rs` — opacity infrastructure (11
  lane/branch predicates + dual-trigger SMTPat lookup + named intro lemma).
- `libcrux-ml-kem/src/vector/portable.rs` — impl reveals + Classical.forall_intro
  pattern for op_compress_*.
- `libcrux-ml-kem/src/serialize.rs` — explicit `lemma_bounded_i16_array_intro`
  calls at compress::<D> sites.
- `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst` —
  per-element fe_commute lemmas + chunk_commutes.
- `MLKEM_STATUS.md` — phase plan + outstanding-admits roster.
- `proofs/session-handoff.md` — resume checklist.

## 11. Estimated effort (ML-KEM remainder, for sizing ML-DSA)

ML-KEM Phase 6 + 7 remaining work (post-trait-opacity-Phase-5):

| Phase | Description | Effort |
|---|---|---|
| 6 | Drop 6 portable NTT-layer admits | 4-6 h |
| 7a | Polynomial 7 fns post-strengthen | 6-10 h |
| 7b | NTT/Inv-NTT layers 1-3 (8 fns) | 8-12 h |
| 7c | Serialize re-root | 6-8 h |
| 7d | Matrix (4 medium) | 6-8 h |
| 7f-i | Hard cases (full NTT, multiply, etc.) | 8-12 h (USER lane) |
| 7j | Ind_cpa/Ind_cca migrate | 4-6 h |
| 7k-l | Drop Spec.MLKEM | 1-2 h |
| 7m | Spec.Utils → Proof_utils | 2-4 h |
| **Total** | | **~50-70 h** |

ML-DSA may be similar or less in shape but additional in scope (different
operations, different spec module structure).  Aggressive parallelism
across multiple agent sessions is required to hit the 48-hour goal.
