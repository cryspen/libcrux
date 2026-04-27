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

## Phase-1 rework (resolved 2026-04-27, see commit history for SHA)

Three findings + one impl bug surfaced during Phase 2A/3A coordination
have been repaired. Documented here for traceability.

- **`lemma_decompose_lane_lookup` Error 19** — fixed by hoisting
  `((v gamma2 == 95232) \/ (v gamma2 == 261888))` into the lemma's
  `requires`. Same hoist applied to `lemma_compute_hint_lane_lookup` and
  `lemma_use_hint_lane_lookup` which had the identical opaque-shielded
  function-call-precondition issue (revealed once the decompose error
  was cleared).
- **`infinity_norm_exceeds_post` over-strong vs pre** — relaxed: now
  cites raw signed absolute value (`if x >= 0 then x else -x`) instead
  of `Hacspec_ml_dsa.Arithmetic.coeff_norm`. Compatible with the loose
  `is_i32b_array_opaque FIELD_MAX simd_unit` pre. The relationship to
  FIPS 204's centered `coeff_norm` holds whenever inputs are already
  centered.
- **`reduce_lane_post` over-strong vs impl** — relaxed from `0 <= v r < q`
  to centered Barrett range `(-q < v r < q) /\ (v r) % q == (v input) % q`.
- **`montgomery_multiply_lane_post` triple-product i64 overflow** —
  rewrote post in mathematical `int` arithmetic
  (`(v future_lhs) % q == (v lhs * v rhs * 8265825) % q`) instead of the
  i64 expression `(cast lhs *! cast rhs *! mk_i64 8265825)` which
  overflows i64 for arbitrary i32 inputs. Equivalent semantics; sidesteps
  the overflow obligation. Hidden behind decompose lookup error before
  Step B.
- **AVX2 `Operations::reduce` 4-of-32 impl bug** — replaced the four
  hard-coded `shift_left_then_reduce::<0>(&mut simd_units[{0,8,16,24}].value)`
  calls with `for i in 0..simd_units.len() { ... }` matching the portable
  impl.

## Active admits

### Libcrux_ml_dsa.Simd.Traits.Specs.bounded_{add,sub}_{pre,post}
- **File / lines**: `libcrux-ml-dsa/src/simd/traits/specs.rs:292-368`
  (the four `#[hax_lib::fstar::after]` SMTPat-bridge lemmas).
- **Annotation**: `admit ()` in lemma body.
- **Phase added**: pre-existing (predates Phase 1; surfaced once
  `lemma_decompose_lane_lookup` cleared).
- **Diagnosis**: The four lemmas claim
  `is_i32b_array_opaque b1 a /\ is_i32b_array_opaque b2 b /\ b1+b2 ≤ u32::MAX`
  implies `add_pre a b` (i.e. each lane sum fits in i32). But `b1+b2 ≤
  u32::MAX = 2^32-1` allows the sum `v a[i] + v b[i]` to reach `2^32-1`,
  which exceeds `i32::MAX = 2^31-1`. The bound is genuinely insufficient
  to prove the conclusion. Correct constraint would be `b1+b2 ≤ i32::MAX`
  (= `2^31-1`) for `add_pre`, or a similarly tighter constraint for
  `add_post`/`sub_pre`/`sub_post`.
- **Suggested mitigation**: USER lane / pre-Phase-1 owner. Tighten the
  constraint on `b1+b2` to `2147483647` (i32::MAX) in the four lemmas.
  Once tightened, the `reveal_opaque (\`%add_pre)` body should close.
  Alternatively, weaken `add_pre`/`sub_pre`/`add_post`/`sub_post` to
  not require i32-fit (using saturating semantics).
- **Template value**: this is the canonical bounds-bridge SMTPat used by
  every downstream caller of `add`/`subtract` to satisfy the trait pre.
  Until tightened, downstream proofs that rely on this SMTPat are
  effectively unsound (they admit a false lemma). NEEDS FIX before any
  serious correctness claim against `add_pre`/`add_post`.

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
