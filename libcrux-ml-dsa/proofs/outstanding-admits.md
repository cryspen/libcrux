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

## Active admits

(none yet — populated in Phases 1–4)

---

## Resolved admits

(none yet)
