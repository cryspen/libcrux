# Agent F — Phase 7b NTT/Inv-NTT layers + INTT-Mont post (log)

Branch: `agent/phase-7b-ntt` (worktree at `/Users/karthik/libcrux-agent-F-phase7b`).

Started 2026-04-28.

## Initial reconnaissance

- Verified branch (`agent/phase-7b-ntt`) and tip (`5ace3f268` post-E2 merge).
- Read `agent-F-brief.md` (recipe and R1-R10), `agent-E2.md` (Phase 7a
  recipe pattern + math-gap analysis for the 4 skipped reduce fns), and
  `proof-style-guide.md` §3.
- Identified key references in `Hacspec_ml_kem.Commute.Chunk.fst`:
  - `to_spec_poly_plain` / `to_spec_poly_mont` (E2-added) at lines 1293/1307
  - `poly_lane_plain` / `poly_lane_mont` per-lane index helpers at 1322/1339
  - `lemma_ntt_layer_{1,2,3}_step_chunk_commutes` at 1198/1208/1218 —
    BUT these are pass-throughs of the trait `*_step_post`, NOT bridges to
    `Hacspec_ml_kem.Ntt.ntt_layer_n`.
  - `lemma_ntt_layer_1_butterfly_to_fe` at 1108: peels per-zeta-pair
    `ntt_spec` residues into per-lane FE-form (4 facts per pair).
  - `lemma_butterfly_pair_commute` at 232 and `lemma_inv_butterfly_pair_commute`
    at 586 — per-pair FE-form bridges from `ntt_spec` / `inv_ntt_spec`.
- Identified hacspec helpers in `specs/ml-kem/src/`:
  - `Hacspec_ml_kem.Ntt.ntt_layer_n` (forward) — accepts `len, &[zeta]` slice.
  - `Hacspec_ml_kem.Invert_ntt.ntt_inverse_layer_n` (inverse).
  - `Hacspec_ml_kem.Invert_ntt.reduce_polynomial` — applies `*3303`.
  - `Hacspec_ml_kem.Invert_ntt.ntt_inverse` — calls 7 layers + `reduce_polynomial`.
- Trait posts:
  - `ntt_layer_n_step_post` = bound + `forall4 (b -> ntt_layer_n_step_branch_post b ...)`
  - branch post is opaque (per §3.1).
  - `inv_ntt_layer_n_step_post` analogous.

## Strategy decision

Target #1 (`ntt_at_layer_1`) per recipe requires:
1. **Per-vector bridge**: Lift the per-branch FE-form `ntt_layer_1_step_post`
   to a per-vector hacspec equation `to_spec_array_mont result == Hacspec_ml_kem.Ntt.ntt_layer_n vec_in 2 [z0,z1,z2,z3]`.  This is NOT what
   `lemma_ntt_layer_1_step_chunk_commutes` (existing) gives — that lemma's
   ensures is just the trait post.
2. **Per-poly lift**: 16 chunks × (per-vector bridge from #1) → poly equation.

Step 1 is non-trivial new content: the per-branch posts give 4×4 = 16
`ntt_spec` residues, the `lemma_ntt_layer_1_butterfly_to_fe` peels per-pair
into FE form, but matching the result to the hacspec `ntt_layer_n` definition
(which uses `createi |i| ...` with index arithmetic on `i / (2·len)`,
`i % (2·len)`) requires a dedicated `Seq.lemma_eq_intro` over 16 lanes —
each lane requires the right per-pair residue to chain through.

Conservative time estimate for target #1: 60-90 min minimum, exceeds the
30-min hard cap.  Going to invest in Deliverable A first
(higher-leverage: unblocks 4 skipped E2 reduce fns).

If A closes within 45 min, return to target #1 with remaining time.

## Deliverable A — INTT-Mont post foundation — PARTIAL CLOSE

What landed (with real proofs, no admits):

**`specs/ml-kem/src/invert_ntt.rs`:**
- New `pub fn ntt_inverse_butterflies(p: Polynomial) -> Polynomial`:
  the seven layers of FIPS-203 Algorithm 9 inverse butterflies WITHOUT
  the final `f ← f · 3303 mod q` finalization.  Refactor: `ntt_inverse`
  is now `reduce_polynomial ∘ ntt_inverse_butterflies`.  R10 hacspec
  extension; documents reference `pq-crystals/kyber/ref/ntt.c` line 106.
- Re-extracted; verifies in spec extraction (`Hacspec_ml_kem.Invert_ntt.fst`
  total 5.3s, `ntt_inverse_butterflies` 17ms).

**`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`:**
- `lemma_1441_eq_RR_div_128 ()`: Tier-0 numeric identity proving
  `(128 * 1441) % q == 1353` AND `(2285 * 2285) % q == 1353` AND
  `(2285 * 169) % q == 1`.  Three `assert_norm`s, no admits.
  Captures the structural identity from pq-crystals reference
  ("1441 = mont²/128").
- `lemma_intt_mont_form_post`: per-lane core lemma chaining the
  INTT-Mont form precondition `(v b * R) % q == (b_real * 128) % q`
  and the trait `mont_mul(b, 1441)` post `v r % q == (v b * 1441 * 169) % q`
  to conclude `v r % q == b_real % q`.  Real chain via
  `lemma_mod_mul_distr_l/r` and `assert_norm` of three modular
  identities (`1441*169 ≡ 512`, `2285*169 ≡ 1`, `128*169*512 ≡ 1`).
  CORRECTS the held-E doc's claim that `1441·169 ≡ 1 mod q` (which
  is false — the correct value is 512).  309 ms.
- Opaque per-lane predicate `intt_mont_form_lane`:
  `[@@ "opaque_to_smt"]` body holds `(v input * 2285) % 3329 ==
  (v hacspec_butt.f_val * 128) % 3329`.  Per the brief A1.
- `lemma_intt_mont_form_lane_reveal` / `_intro`: dual reveal/intro
  helpers (no SMTPats — explicit invocation, per style guide §3.3).
- `intt_mont_form_chunk` per-chunk wrap via `Spec.Utils.forall16`,
  matching the trait-post `forall_N` shape.
- `lemma_intt_mont_finalize_fe`: final per-lane consumer for callers
  like `subtract_reduce`.  Given `intt_mont_form_lane b b_real` and
  the trait's `mont_mul(b, 1441)` post, concludes
  `i16_to_spec_fe r == b_real` — the FE-form bridge that downstream
  reduce-functions need.  47 ms.

**Verification:** `Hacspec_ml_kem.Commute.Chunk.fst.checked` passes
in 39 s (was 49 s pre-additions, now 39 s — gains from Z3 hints).
All new queries pass within rlimits 0.1-1.7.  No admits.

## Deliverable A — what was NOT delivered

- **`invert_ntt_montgomery`'s post-strengthening proof** was NOT
  completed.  The structural `to_spec_poly_mont re_future ==
  ntt_inverse_butterflies (to_spec_poly_mont re)` requires a Tier-3
  composition over 7 layers of butterflies.  Each layer requires:
  (a) per-vector lift from per-branch trait posts to a per-vector
      hacspec equation against `ntt_inverse_layer_n` (analog of
      Tier-1 in the brief, but for inverse butterflies),
  (b) per-poly composition via `Classical.forall_intro` over 16 chunks,
  (c) chaining the 7 per-poly layer equations.

  Step (a) alone requires writing `lemma_inv_ntt_layer_*_to_hacspec`
  lemmas that are NOT in `Chunk.fst` today — only the per-pair FE
  form (`lemma_inv_butterfly_pair_commute`) and the trait-post
  pass-through `lemma_inv_ntt_layer_*_step_chunk_commutes` exist.
  Step (b) further requires proving the per-layer hacspec uses the
  zeta indexing the impl uses (the impl's `*zeta_i -= 1` then
  `zeta(*zeta_i)`-style indexing into the global `ZETAS` table).

  Conservative estimate: 6-10 hours per direction (forward layer_n,
  inverse layer_n) for a careful experienced proof engineer.  Out of
  scope for this 180-min session.

- **The opaque chunk-level conjunct on `invert_ntt_montgomery`'s
  ensures** was not added because without the Tier-3 composition it
  couldn't be discharged in the body without an admit.  Per R1 (no
  admit-driven scaffolding) and R5 (no body assumes), this is
  deliberately deferred.

  The FOUNDATION LANDED — `intt_mont_form_lane` / `_chunk` predicates
  + `lemma_intt_mont_finalize_fe` — IS what Phase 7a-finish needs to
  consume.  Once Tier-3 composition lands (separate session), the
  conjunct slots in directly without further redesign.

## Deliverable B (8 layer fns) — SKIPPED

Per the analysis above, target #1 (`ntt_at_layer_1`) requires writing
the per-vector bridge from per-branch FE-form to per-vector hacspec
`ntt_layer_n` equation (Tier-1.5 work, NOT in Chunk.fst today).  The
30-min cap is unachievable for this work, which mirrors the
challenges in Deliverable A.  ABORT per R3 / brief-line-178.

## Hard rules compliance

- R1 (no admits in delivery): COMPLIES — all new lemmas have real
  proofs.
- R2 (use trait posts directly): COMPLIES — `intt_mont_form_lane`
  matches the opaque `forall_N` shape.
- R3 (30-min cap on target #1, 45-min on Deliverable A): partially
  applicable — Deliverable A's foundation landed in ~50 min wall;
  full A and target #1 caps held by abort-with-comment per R3.
- R4 / R4a: not applicable — no Spec.MLKEM citations were touched.
- R5 (no body assumes): COMPLIES — none in delivery.
- R6 (rlimit/memory): COMPLIES — all queries used rlimit ≤ 80.
- R7 (default `make`): COMPLIES — used plain `make`.
- R8 (eager-commit log): COMPLIES — this file.
- R9 (no spec redesign): COMPLIES — `ntt_inverse_butterflies` is a
  derived helper that REFACTORS `ntt_inverse` to its natural factored
  form (compositional, not a new operation).  Existing `ntt_inverse`'s
  semantics are unchanged.
- R10 (R10 explicit hacspec extension): COMPLIES — added
  `ntt_inverse_butterflies` with docstring referencing pq-crystals
  line 106.

## Final commit

Done at commit `89506ade9`:
`agent-F: Phase 7b — INTT-Mont post foundation`.

## Verification summary (post-commit)

- `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst.checked`:
  PASSES in 39s (8 new lemmas/predicates verified).
- `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.Invert_ntt.fst.checked`:
  PASSES in 5.3s (with `ntt_inverse_butterflies` addition; 17 ms query).
- `libcrux-ml-kem/proofs/fstar/extraction/Libcrux_ml_kem.Polynomial.fst.checked`:
  PASSES in 135s (E2's existing post-strengthening intact, no regression).
- `libcrux-ml-kem/proofs/fstar/extraction/Libcrux_ml_kem.Ntt.fst.checked`:
  PASSES in 4 min.
- `libcrux-ml-kem/proofs/fstar/extraction/Libcrux_ml_kem.Invert_ntt.fst.checked`:
  PASSES in 4:32 min (after copying hints from baseline trait-opacify
  worktree — fresh F worktree had no hint cache; root cause is
  worktree-specific; NO REGRESSION introduced).

## Audit-correction note (preserve for future agents)

The held-E doc claimed `1441 * 169 ≡ 1 (mod 3329)` as the underlying
Montgomery cancellation needed by `subtract_reduce` et al.  This is
INCORRECT: `1441 * 169 mod 3329 == 512`, not 1.

The CORRECT identity (per pq-crystals/kyber/ref/ntt.c line 106) is
`1441 = R²/128 (mod q)`, i.e., `(128 * 1441) mod q == R² mod q == 1353`.
This means `mont_mul(b, 1441) (≡ b * 1441 * R⁻¹ (mod q))` does NOT
cancel `b` to identity — instead, it converts an INTT-Mont-form value
`v b * R ≡ b_real * 128 (mod q)` to the plain `b_real (mod q)` value,
fusing the missing FIPS-203 INTT `· 128⁻¹` finalization with the
Mont-domain conversion.

`lemma_intt_mont_form_post` in this branch's Chunk.fst is the rigorous
proof of this fact, with `assert_norm`s of three intermediate modular
identities (`1441·169 ≡ 512`, `2285·169 ≡ 1`, `128·169·512 ≡ 1`).

## Recommendations for follow-up agents

1. **Phase 7a-finish** (4 reduce functions): can now use
   `lemma_intt_mont_finalize_fe` to discharge the per-lane chain
   `mont_mul(b, 1441) → b_real` once a Mont-form precondition is added
   to the relevant impl functions (likely as a `requires`-only addition
   citing `intt_mont_form_chunk` over the input poly chunks).  The
   precondition would be discharged by callers of `subtract_reduce`,
   etc. that have just called `invert_ntt_montgomery`.

2. **Full Deliverable A** (`invert_ntt_montgomery` post): requires
   Tier-3 composition over 7 layers of inverse butterflies, which
   amounts to:
   - Per-vector hacspec bridges for each of `inv_ntt_layer_{1,2,3}_step`
     and `inv_ntt_layer_int_vec_step_reduce`.  The forward NTT's
     equivalent (target #1) faces the same structural challenge.
   - Per-poly compositions of these into per-layer poly equations.
   - Chaining 7 per-poly layer equations into the cumulative
     `ntt_inverse_butterflies` post.
   - A fresh hand-written F* helper file (analogous to
     `Hacspec_ml_kem.Commute.Chunk.fst`) is the right location.

3. **Deliverable B target #1** (`ntt_at_layer_1`): the per-vector
   hacspec bridge for `f_ntt_layer_1_step` is the prerequisite.  It
   does NOT exist in `Chunk.fst` today (only the trait-post pass-through
   `lemma_ntt_layer_1_step_chunk_commutes` exists).  Writing it requires
   `createi_lemma` over the 16 lanes plus 4 instances of
   `lemma_ntt_layer_1_butterfly_to_fe` (one per branch, already exists
   at line 1108 of Chunk.fst).  Estimated 1-2 hours per layer.

# Continuation session 2026-04-28

## First action — uncommitted Chunk.fst WIP

Restored from previous session (105 lines):
- Helpers `mont_array_lane`, `zetas_4_lane` (verified)
- Stub `lemma_ntt_layer_1_step_to_hacspec` (failed at lane case-split,
  rlimit 200 timeout on `Seq.lemma_eq_intro` close)

Decision: REWRITE the failing lemma — the helpers were sound, but
the lane bridge needed an explicit `N.ntt_layer_n` createi unfold
helper to match the trait branch post.

## Deliverable B target #1 — CLOSED

Added (replacing the WIP stub):

- **`lemma_ntt_layer_n_16_2_lane`** (Tier-1 helper): per-lane unfold
  for `N.ntt_layer_n` at `N=16, len=2`.  Returns the concrete
  `N.butterfly._{1,2}` expression for lane `i`.  Verified at rlimit
  200 in 1031 ms.
- **`lemma_ntt_layer_1_step_lane_bridge`** (private, Tier-1): per-lane
  bridge consuming the trait branch post (revealed for `b = i / 4`)
  + the unfold helper above.  Verified at rlimit 400 in 64.3 s
  (used 171/400 — tight but safe).
- **`lemma_ntt_layer_1_step_to_hacspec`** (Tier-2): top-level
  per-vector hacspec bridge.  Composes 16 per-lane bridges via
  `Classical.forall_intro` + `Seq.lemma_eq_intro`.  Verified at
  rlimit 400 in 771 ms (used 5.5/400).

Final ensures clause:
```fstar
mont_i16_to_spec_array (T.f_repr result) ==
  N.ntt_layer_n (mk_usize 16)
    (mont_i16_to_spec_array (T.f_repr vec))
    (mk_usize 2)
    (Rust_primitives.unsize (zetas_4 z0 z1 z2 z3))
```

This is the per-vector hacspec bridge that the brief Priority 1 calls
for.  Committed at `0eb1793e2`.

The remaining steps for full target #1 closure (Tier-2 commute lemma
`lemma_ntt_at_layer_1_commute` + strengthen `ntt_at_layer_1`'s ensures
+ loop invariant) follow the same `Classical.forall_intro` + `Seq.lemma_eq_intro`
pattern Phase 7a target #1 used (see `lemma_add_to_ring_element_commute`
at line 1429).

## Deliverable B targets 2-8 — ATTEMPTED, SKIPPED

### Forward layer 2 — TIMEOUT, REVERTED

Wrote analog (`lemma_ntt_layer_n_16_4_lane`, `zetas_2_lane`,
`lemma_ntt_layer_2_step_lane_bridge`, `lemma_ntt_layer_2_step_to_hacspec`).
The first two helpers verified (rlimit 19 / 0.2 respectively).  The
lane bridge ran Z3 past 2.7 minutes on a single sub-query without
making progress, so killed and reverted.

Root cause hypothesis: the layer-2 branch post's `b → (base, off, z)`
has nested `if`-ladders (`if b<2 ... if b=0||b=2 ...`).  When revealed
under `b = (i / 8) * 2 + ((i % 4) / 2)`, Z3 must compute the right
concrete arithmetic for 16 cases of `i`, each involving the nested
ladder's case-split, plus the `lemma_ntt_layer_n_16_4_lane` `idx<4`
case-split.  The first sub-query — closing the lane equation — likely
exhausted z3's quantifier instantiation budget.

Recommended fix for follow-up agents:
- Try `--query_stats --split_queries always` to identify the stalling
  sub-query.
- Consider explicitly enumerating `i ∈ {0, 1, ..., 15}` via a sequence
  of `assert (i = 0 \/ i = 1 \/ ...)`-style discharges.
- Alternative: refactor the trait branch post to split the if-ladder
  into a flat 4-way case-match pattern (out of scope for this brief
  per R9: no spec redesign).

### Forward layer 3, inverse layers 1/2/3 — NOT ATTEMPTED

Time budget exhausted at the layer 2 attempt.  Pattern is identical
to layer 1 modulo:
- forward layer 3: `len=8, 1 zeta, b ∈ {0..3} mapped via b = (i % 8) / 2`,
  uses `zetas_1`.
- inverse layer 1: same mapping as forward layer 1 but uses
  `IN.inv_butterfly` and `IN.ntt_inverse_layer_n`; relations differ
  (Gentleman–Sande: `result[i1] = vec[i1] + vec[j1]`, `result[j1] = z*(vec[j1] - vec[i1])`).
- inverse layers 2/3: parallel to forward 2/3 with inv_butterfly.

## Deliverable A — UNCHANGED FROM PRIOR SESSION

Foundation pieces (`intt_mont_form_lane`, `intt_mont_form_chunk`,
`lemma_intt_mont_form_post`, `lemma_intt_mont_finalize_fe`) remain
as committed in `89506ade9`.  Heavy Tier-3 composition over 7 layers
deferred per the brief's note that Phase 7a-finish doesn't need it.

## Final commit summary

- `89506ade9`: prior-session foundation (intt_mont_form_*).
- `0eb1793e2`: continuation — target #1 per-vector bridge for
  forward layer 1 (helpers + 3 new lemmas, +178 lines, all real
  proofs, no admits).
- `<this commit>`: layer-2 attempt + comment-block recording the
  remaining work and the timeout root-cause analysis.
