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

## Target #2 — `add_to_ring_element` — CLOSED (00:37-00:48, 11 min)

✅ Real proof of `lemma_add_to_ring_element_commute` in Chunk.fst (1063ms).
   Per-vector `add_post lhs rhs r` (forall i. v r.[i] == v lhs.[i] + v rhs.[i])
   lifts via existing `lemma_add_fe_commute_plain` to per-lane FE equation,
   then 256-lane Classical.forall_intro + Seq.lemma_eq_intro yields the
   poly equation.  `createi_lemma` unfolds the hacspec side at index j;
   structural equality with `impl_FieldElement__add` follows.
✅ `polynomial.rs::add_to_ring_element` post strengthened to cite
   `Hacspec_ml_kem.Polynomial.add_to_ring_element`, preserves bound.
✅ Loop invariant strengthened with `add_post(orig.[j], rhs.[j], curr.[j])`
   for j < i and `orig.[j] == curr.[j]` for j >= i.
✅ Body: ONE Tier-1 lemma call, no assumes, no admits.
✅ Verifies: Chunk.fst 49s, Polynomial.fst 73s.

## Targets #3, #4, #5, #6 — SKIP-WITH-COMMENT (00:48-00:55, 7 min)

After analyzing the math, I identified a fundamental math gap in the
held-E sketch for these 4 targets.  The held-E doc claimed
"`1441*169 ≡ 1 mod 3329`" as a Montgomery cancellation, which would
make `mont_mul(b, 1441)` the identity at the value level.  This
congruence is FALSE: `1441 * 169 mod 3329 == 512`, NOT 1.

Empirically verified:
```
q = 3329; 1441 * 169 % q == 512   (not 1)
1353 * 169 % q == 169 * 1353 % q == 1353 * 169 mod q (also not 1)
```

Mathematical implication: at the value level, the impl bodies of
subtract_reduce / add_error_reduce / add_message_error_reduce /
add_standard_error_reduce compute (modulo Barrett):
  red == (myself - 512*b) mod q       (target #3)
  red == (myself + 512*error) mod q   (target #4) — wait, signs differ
  ...

These do NOT match the hacspec functions' formulas (which are
`(a +/- b) mod q` with no scaling factor).  The 1441/1353 constants in
the impl exist because the impl's `subtract_reduce` is called AFTER
`invert_ntt_montgomery`, where the operand `b` carries an additional
scaling factor (essentially `b_called == b_real * 128 mod q` from
intt's `1/N` factor mod q), and `1441 = 128^{-1} * R mod q` (to be
verified).  Under that contextual scaling, the math may close — but
this requires either:
  (a) modifying hacspec spec functions (e.g.,
      `add_error_reduce(ntt_product, error)` semantics aware of
      scaling), or
  (b) tightening the impl `requires` to capture that `b_called` is
      already in a particular scaled form, plus a separate Tier-0
      lemma showing `1441 * scaling_factor ≡ 1 mod q`.

Both options are out of scope of E2's brief: (a) violates R9 ("Don't
redesign spec"), and (b) requires non-trivial new arithmetic content
(specifically derivation of the Kyber NTT/Montgomery scale factor
identity), which is more than 22-min target work.

The held-E doc's admit comments admitted this complexity:
"Admitted: requires the `1441*169 ≡ 1 mod q` Montgomery cancellation
lemma — clean math but tedious to spell out at poly level."  The
cancellation as stated is false; the actual cancellation needed
involves the NTT scaling factor and is non-trivial.

Skip-with-comment for #3-#6: keep the existing posts (just bound),
do NOT add the `Hacspec_ml_kem.Polynomial.<f>` citation.  This
preserves the parent's ability to revisit with proper math.

(In Chunk.fst, do NOT add Tier-1 lemma stubs for #3-#6 — would be
admit-driven scaffolding, which R1 forbids.)

## Summary

Final result: 2/6 targets closed with real proofs, 4/6 skip-with-comment
with documented math-gap analysis.

Time used: ~40 min wall clock (well within 150-min total cap).

