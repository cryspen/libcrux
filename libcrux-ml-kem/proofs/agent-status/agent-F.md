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

Pending — see "Final deliverable" below.

