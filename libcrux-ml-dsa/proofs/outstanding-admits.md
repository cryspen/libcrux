# Outstanding Admits

This file tracks every `admit()`, `admit_smt_queries`, or
`#[hax_lib::fstar::verification_status::panic_free]` annotation in the
ML-DSA proof effort. Each entry should answer: where, why, and what
mitigation a USER (human prover) might attempt.

## Template entry

```
### <Module>.<function>
- **File / lines**: `path/to/file.rs:LINE_START-LINE_END`
- **Annotation**: `panic_free` | `fstar!("admit()")` | `--admit_smt_queries true`
- **Phase added**: 0 | 1 | 2x | 3x | 4x
- **Diagnosis**: <one paragraph: Z3 timeout? Quantifier blowup? Missing
  lemma? FE-algebra divergence? What was tried in the 20-minute budget?>
- **Suggested mitigation**: <agent-lane vs USER-lane; specific approach
  (split into N sub-lemmas; factor branch-post; explicit zeta-table
  induction; etc.)>
- **Template value**: <does landing this proof unblock similar admits?>
```

---

## Pre-budgeted admits (planned from day 1)

Items we expect to mark admitted on first attempt; including them here
so subsequent sessions don't burn budget retrying:

### Libcrux_ml_dsa.Simd.Avx2.Ntt.{layer_1, layer_2}
- **Phase**: 3D
- **Diagnosis**: 4-zeta-parallel SIMD layer where Z3 can't handle the
  wide context (ML-KEM USER-4 analog, see
  `libcrux-ml-kem/proofs/manual-proof-targets.md`).
- **Suggested mitigation**: USER lane. Refactor each AVX2 layer body
  into 4 per-zeta sub-functions to split the proof obligations; or
  await SIMD model unification (`libcrux-ml-kem/proofs/simd-model-unification-plan.md`).

### Libcrux_ml_dsa.Simd.Avx2.Invntt.{layer_1, layer_2}
- **Phase**: 3E
- **Diagnosis**: Analogous to NTT layers 1–2.
- **Suggested mitigation**: USER lane. Same refactor approach.

### Hacspec_ml_dsa.Commute.Chunk.lemma_ntt_full_commute
- **Phase**: 2F
- **Diagnosis**: Tier-3 composition of 8 layer-step lemmas with BitRev₈
  zeta-table indexing — same shape as ML-KEM USER-2 but one more layer
  (8 vs 7).
- **Suggested mitigation**: USER lane. Template after ML-KEM's
  `lemma_ntt_full_commute` once it lands.
- **Template value**: closes NTT layer of the proof; once forward
  composition is proven, INVNTT and ntt_multiply compositions are
  direct adaptations.

---

## Phase-1 carryover findings (discovered during Phase 2A/3A coordination)

These three findings surfaced when both parallel Phase 2/3 wave agents tried
to discharge the strengthened trait posts. They predate the wave commits and
must be repaired before any Simd.* impl proof can validate end-to-end.
Status: scheduled for repair in the upcoming Phase-1 rework commit (Step B
of the 2026-04-27 coordination plan).

### Libcrux_ml_dsa.Simd.Traits.Specs.lemma_decompose_lane_lookup (Error 19)
- **Source**: `libcrux-ml-dsa/src/simd/traits/specs.rs:75-81`
- **F\*** location: `Libcrux_ml_dsa.Simd.Traits.Specs.fst:69-70`
- **Phase added**: 1 (commit `7be6b31b1`, missed by handoff baseline)
- **Diagnosis**: Lemma fails to typecheck — `unknown because (incomplete
  quantifiers)` at rlimit 80. The lemma's ensures references
  `Hacspec_ml_dsa.Arithmetic.decompose input gamma2`, whose precondition
  requires `gamma2 ∈ {95232, 261888}`. That constraint lives inside the
  body of the opaque `decompose_lane_post`, so F* cannot see it when
  typechecking the ensures clause. The two sister lemmas
  `lemma_reduce_lane_lookup` and `lemma_compute_hint_lane_lookup`
  typecheck because their ensures clauses do not have a function-call
  precondition.
- **Impact**: Specs.fst.checked is never produced; every `Simd.Portable.*`
  and `Simd.Avx2.*` module short-circuits at this dependency. No Phase 2
  or Phase 3 impl proof can be empirically validated until this clears.
- **Repair**: hoist `((v gamma2 == 95232) \/ (v gamma2 == 261888))` into
  the lemma's `requires`. Done in Step B.

### Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post over-strong vs pre
- **Source**: `libcrux-ml-dsa/src/simd/traits/specs.rs` (post predicate)
  and `libcrux-ml-dsa/src/simd/traits.rs` (trait method pre/post).
- **Phase added**: 1
- **Diagnosis**: Trait pre allows `is_i32b_array_opaque FIELD_MAX simd_unit`
  (i.e. `|v lane| ≤ q-1`, the FIELD_MAX range). Phase-1 post cites
  `Hacspec_ml_dsa.Arithmetic.coeff_norm`, which folds inputs through
  `((a%q)+q)%q` and then maps `>q/2` to `q-r` — i.e. centered absolute
  value. For inputs in `(q/2, q-1]` the impl's signed `abs(v lane)` and
  the spec's `coeff_norm` differ, so the post is unprovable as stated.
- **Repair**: relax the post to use the impl's actual signed `abs` (or
  add an explicit lane-centering normalization in the impl). Done in
  Step B by adjusting `infinity_norm_exceeds_post`.

### Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post over-strong vs impl
- **Source**: `libcrux-ml-dsa/src/simd/traits/specs.rs:48-55` (post + lookup
  + intro).
- **Phase added**: 1
- **Diagnosis**: Phase-1 post requires `0 <= v result < 8380417`. Impl
  delegates to `shift_left_then_reduce::<0>` → Barrett reduction → returns
  centered representative in `[-(q-1), q-1]`. The `>= 0` conjunct is
  unprovable for any input whose Barrett reduction lands in `[-(q-1), 0)`.
- **Repair**: relax to `is_i32b 8380416 result /\ (v result) % q == (v input) % q`
  (centered representative + congruence). Done in Step B.

## Implementation bugs (out of proof scope)

### AVX2 Operations::reduce only reduces 4 of 32 SIMD units
- **File / lines**: `libcrux-ml-dsa/src/simd/avx2.rs:160-165`
- **Discovered**: Phase 3A wave (i) coordination, 2026-04-27.
- **Diagnosis**: Body unconditionally calls
  `shift_left_then_reduce::<0>(&mut simd_units[i].value)` for `i ∈ {0, 8, 16, 24}`
  only. `shift_left_then_reduce` operates on a single `Vec256`, so 28 of
  32 SIMD units (indices 1-7, 9-15, 17-23, 25-31) are left un-reduced.
  This is materially false against any per-SIMD-unit forall reduce post
  (Phase 0 or Phase 1) and is a correctness defect pre-dating the proof
  sprint. A correct implementation iterates `for i in 0..simd_units.len()`
  matching the portable impl.
- **Status**: scheduled for fix on a separate non-proof branch (Step C
  of the 2026-04-27 coordination plan); not addressed by Phase 2/3 proof
  waves.

---

## Pre-existing failures (out of scope for the ML-DSA proof sprint)

### Libcrux_core_models.Abstractions.Funarr (Error 92)
- **File**: `crates/utils/core-models/proofs/fstar/extraction/Libcrux_core_models.Abstractions.Funarr.fst:97`
- **Phase observed**: 0 (baseline)
- **Diagnosis**: Pre-existing F* typecheck failure unrelated to ML-DSA.
  `git log` shows the last touches were `3000c7b7a` (core-models: fix
  implicit/explicit argument mismatch in Funarr) and `6accee650`
  (gitignore hax-generated F* files), both prior to this sprint.
  The error appears upstream of any ML-DSA module so `make` reports
  Error 2 even when ML-DSA-specific files would individually verify.
- **Suggested mitigation**: out of scope for the ML-DSA sprint — this
  is in `core-models`, a workspace dependency, and needs to be fixed
  there.  Future sessions should be aware that `make` exits non-zero
  on this file regardless of ML-DSA proof state.

## Active admits

### Libcrux_ml_dsa.Simd.Traits.ntt (per-poly post)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:158-172` (Operations::ntt)
- **Annotation**: bounds-only post retained; no per-poly forall32-with-Hacspec_ml_dsa.Ntt.ntt conjunct added
- **Phase added**: 1
- **Diagnosis**: Tier-3 chain across 8 layers with BitRev₈ zeta indexing — the
  ML-KEM USER-2 analog with one extra layer. A per-poly post would require
  composing 8 layer-step lemmas with subtle indexing; this is Z3-incompatible
  in the trait-level 20-min budget. The bounds-only post is sufficient for
  upstream callers that only need the FIELD_MAX bound.
- **Suggested mitigation**: USER lane. Build per-layer commute lemmas in
  `specs/ml-dsa/proofs/fstar/commute/Hacspec_ml_dsa.Commute.Chunk.fst`
  (Phase 2F prerequisite), then chain into a `lemma_ntt_full_commute` after
  ML-KEM's analog lands as a template.
- **Template value**: closes the NTT layer of the proof; INVNTT and
  ntt_multiply compositions are direct adaptations.

### Libcrux_ml_dsa.Simd.Traits.invert_ntt_montgomery (per-poly post)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:175-187`
- **Annotation**: bounds-only post retained
- **Phase added**: 1
- **Diagnosis**: Analogous to NTT — Tier-3 chain with the additional
  Montgomery-domain → standard-domain conversion at exit.
- **Suggested mitigation**: USER lane, after `lemma_ntt_full_commute` lands.
- **Template value**: matches NTT template once NTT is proven.

### Libcrux_ml_dsa.Simd.Traits.rejection_sample_* (per-byte step posts)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:108-118`
- **Annotation**: bound + count-bound post; per-element citation of
  `Hacspec_ml_dsa.Encoding.coeff_from_three_bytes` /
  `coeff_from_half_byte` deferred (lane post predicates exist in
  `Libcrux_ml_dsa.Simd.Traits.Specs` but the trait post does not connect
  out[i] to the originating randomness chunk).
- **Phase added**: 1
- **Diagnosis**: The trait method consumes a length-24 (or length-4) byte
  buffer and outputs accepted coefficients into `out`. A per-byte step
  predicate would have to thread a loop index `j` through randomness
  chunks and witness the partial-acceptance count — non-trivial in a
  trait-level post and exceeds the 20-min budget.
- **Suggested mitigation**: agent-lane Phase 2 work. Add a
  loop-invariant-style relational predicate citing `coeff_from_*` once
  the impl proof is being driven in `simd/portable/sample.rs`.

### Libcrux_ml_dsa.Simd.Traits.{gamma1,commitment,error,t0,t1}_{serialize,deserialize}
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:120-156`
- **Annotation**: length-preservation + bound conjuncts only;
  `BitVecEq.int_t_array_bitwise_eq` round-trip equation against
  `Hacspec_ml_dsa.Encoding.{simple_bit_pack,bit_pack,simple_bit_unpack,bit_unpack}`
  deferred.
- **Phase added**: 1
- **Diagnosis**: Bit-vector equivalence via `BitVecEq.int_t_array_bitwise_eq`
  is the canonical ML-KEM template, but the encoding-side gamma1/t0 widths
  use offset-encoded bit_pack (each value `v` packed as `b - v` over a
  signed range), which the ML-KEM template does not cover. The full
  predicate can be added once the helpers in
  `fstar-helpers/fstar-bitvec/BitVecEq.fst` are extended for offset packing.
- **Suggested mitigation**: agent-lane Phase 2D. Mirror the ML-KEM
  `serialize_post_N` / `deserialize_post_N` shape, with offset-aware
  variants for gamma1/t0/error.

---

## Resolved admits

(none yet)
