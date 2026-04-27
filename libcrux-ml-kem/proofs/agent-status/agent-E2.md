# Agent E2 — Phase 7a Polynomial real proofs (log)

Branch: `agent/phase-7a-polynomial-real` (worktree at
`/Users/karthik/libcrux-agent-E2-phase7a-real`).

Started 2026-04-28 00:16 local.

## Initial reconnaissance (00:16-00:25)

- Verified branch + parent tip: `agent/phase-7a-polynomial-real`,
  HEAD = `0ffe5ff63 Policy update: replace, don't add ...`.
- Read brief (`agent-E2-brief.md`), held-work doc (`held-work-E-Phase7a.md`),
  and the held E branch's Tier-1 lemma signatures.
- Identified key references:
  - `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
    has all per-vector chunk-commute lemmas (`lemma_barrett_reduce_chunk_commutes`,
    `lemma_add_chunk_commutes_plain`, `lemma_sub_chunk_commutes_plain`,
    helper `lemma_barrett_fe_commute`, etc.) plus FE-arithmetic helpers.
  - Trait posts in `libcrux-ml-kem/src/vector/traits.rs::spec`:
    `barrett_reduce_post vec result` = `is_i16b_array_opaque 3328 result /\
    forall i. v result.[i] % 3329 == v vec.[i] % 3329`.
  - `i16_to_spec_fe` (in traits.rs) returns FE refined with `v r.f_val == v x % 3329`.
  - `lemma_barrett_fe_commute (a r: i16) : Lemma (requires v r % 3329 == v a % 3329)
    (ensures i16_to_spec_fe r == i16_to_spec_fe a)` — already proven `= ()`.
  - Spec hacspec polynomial functions in `specs/ml-kem/src/polynomial.rs`:
    `poly_barrett_reduce p = createi |i| FieldElement::new(p[i].val % FIELD_MODULUS)`.
- Spec extraction directory `specs/ml-kem/proofs/fstar/extraction/` is empty
  (gitignored); needs `python3 hax.py extract` to generate Hacspec_ml_kem.* fst.

## Plan

1. Run `python3 hax.py extract` to populate `specs/ml-kem/proofs/fstar/extraction/`
   with `Hacspec_ml_kem.Polynomial.fst` etc.
2. Verify baseline: `make Hacspec_ml_kem.Commute.Chunk.fst.checked` passes
   on the unmodified file.
3. Add the 6 Tier-1 lemmas with REAL proofs (no admits) into Chunk.fst.
4. Strengthen 6 polynomial.rs ensures clauses citing the lemmas; discharge
   in body with NO `assume`s.

## Target #1 — `poly_barrett_reduce` — CLOSED (00:16-00:37, 21 min)

✅ Real proof of `lemma_poly_barrett_reduce_commute` in Chunk.fst (134ms).
✅ Helper `lemma_poly_barrett_reduce_id` (49ms).
✅ Lifts `to_spec_poly_plain` / `to_spec_poly_mont` and per-lane index
   helpers `poly_lane_plain` / `poly_lane_mont`.
✅ `polynomial.rs::poly_barrett_reduce` post strengthened in-place: cites
   `Hacspec_ml_kem.Polynomial.poly_barrett_reduce`, preserves `is_bounded_poly`
   bound. Loop invariant minimally strengthened to carry per-vector
   `barrett_reduce_post (orig.[j]) (curr.[j])` for `j < i` and
   `current.[j] == orig.[j]` for `j >= i`.
✅ Body discharge: ONE call to `lemma_poly_barrett_reduce_commute` after
   the loop, no assumes, no admits.
✅ `Libcrux_ml_kem.Polynomial.fst` re-extracted and verified (190s wall,
   all queries pass).
✅ `Hacspec_ml_kem.Commute.Chunk.fst` verified (51s wall).

Recipe validated.  Pattern: minimal strengthening of `j < i` branch with
the exact trait post needed for the Tier-1 lemma's `requires` shape; one
`{ f_coefficients = orig }` snapshot reconstruction at lemma call site.

Proceed with remaining 5 targets per pattern.

