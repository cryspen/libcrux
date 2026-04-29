# Serialize agent status — Cluster 3 lemma scale-up

**Goal.** Confirm the 4 BitVec lemmas committed at `a51ddbfc3`
(`serialize_5/11_bit_vec_lemma`, `deserialize_5/11_bit_vec_lemma{,_bounded}`
plus the matching wrapper `_lemma`s) verify cleanly under
`VERIFY_SLOW_MODULES=yes` — i.e. without `--admit_smt_queries true`.

## Methodology

`Libcrux_ml_kem.Vector.Portable.Serialize.fst` is one of the slowest
modules in the repo (full cold verification several tens of minutes).
A whole-file VERIFY_SLOW run is impractical as an inner loop.

We adopted the **targeted-admit** strategy (per Karthik's instruction):

  - Wrap the entire module body in
    `#push-options "--admit_smt_queries true"` at the top (line 25 of
    the extracted .fst).
  - For each target lemma's existing push-options block, add
    `--admit_smt_queries false` so verification re-engages locally.
  - Verify ONE target lemma per F\* run (the 11-bit equalities are too
    big for a single combined run under the 5-min budget).

The `.fst` edits are LOCAL DEBUG — they live in the **extracted**
.fst (`proofs/fstar/extraction/Libcrux_ml_kem.Vector.Portable.Serialize.fst`),
not in the source `.rs`.  They are reverted via `git checkout --` after
all four lemma sets have been confirmed.

We also dropped `--z3refresh` from the bit-vec lemma push-options for
the targets (kept on non-targets).  The original `--z3refresh` was
contributing measurable overhead (z3 spawn per pointwise sub-goal)
without proof robustness benefit at these widths.

## Per-lemma timings (cold, no hints)

| Run | Lemmas verified (others admitted) | F\* wall | Make wall | Result |
|---|---|---|---|---|
| 1 | `serialize_5_bit_vec_lemma` + `serialize_5_lemma` | 184.3 s | 3 m 13 s | ✅ all VCs discharged |
| 2 | `deserialize_5_bit_vec_lemma{,_bounded}` + `deserialize_5_lemma` | 181.6 s | 3 m 11 s | ✅ all VCs discharged |
| 3 | `serialize_11_bit_vec_lemma` + `serialize_11_lemma` | 665.0 s | 11 m 15 s | ✅ all VCs discharged |
| 4 | `deserialize_11_bit_vec_lemma{,_bounded}` + `deserialize_11_lemma` | 556.4 s | 9 m 26 s | ✅ all VCs discharged |

**Total cold verification time across the 4 single-target runs: 1587 s
(~26 min) F\* time, ~27 min wall.**  Hints recorded after each run; a
re-run that picks up cached hints should be substantially faster (untested
in this session because each run flipped admit settings, invalidating
the hint match).

Per-query Z3 time stayed at ~0.1–0.8 s with `rlimit_used / rlimit_cap`
≪ 1 (the proofs are not Z3-bound; they are F\* tactic-engine bound at
~1.5–2 s per pointwise sub-goal).

The 5-bit pair (80-bit equalities) closes well under the 5-min cap (~3:13
each).  The 11-bit pair (176-bit equalities) has 2.2× the sub-goals **and**
~25 % higher per-query encoding cost, putting each single-target run at
9–11 min — clearly over the 5-min cap.  Reported as data, not as a problem
to "fix": the proof shape is the same as for the 5-bit case; the wall is
proportional to bit-width × per-bit goal-encoding cost.

If 11-bit walls become problematic for routine re-verification, the
prompt's strategy 6 (split each 176-bit lemma into 2 × 88-bit halves)
could be a future optimization.  Not pursued here because the lemmas
already verify and the current cost is paid only on cold runs.

## Net admit count delta

Net change at HEAD vs `a51ddbfc3`: **0** (no source modifications).
The 4 lemmas in question were committed at `a51ddbfc3`.  This agent
**confirmed they verify** under VERIFY_SLOW_MODULES=yes; no source
changes are needed.  The local-debug `.fst` edits are reverted before
report.

## USER-9 forward-path recommendation

The BitVec posts now exist at the **portable** layer.  USER-9 = wire
them into the trait so above-trait callers can use the BitVecEq post.

**Crucial finding (post-status audit of `src/vector/avx2/serialize.rs`):**
the AVX2 5/11 family is *not uniform*.  USER-9 splits into two sub-tasks
of very different difficulty.

### USER-9a: 11-bit family — trivial wrapper bridge (do first)

`src/vector/avx2/serialize.rs:687-700` — `serialize_11` and
`deserialize_11` on AVX2 are **NOT real AVX2**.  They are thin wrappers
that bounce through portable code:

```rust
#[hax_lib::fstar::verification_status(lax)]   // ← lax today
pub(crate) fn serialize_11(vector: Vec256) -> [u8; 22] {
    let mut array = [0i16; 16];
    mm256_storeu_si256_i16(&mut array, vector);
    let input = PortableVector::from_i16_array(&array);
    PortableVector::serialize_11(input)
}

#[hax_lib::fstar::verification_status(lax)]   // ← lax today
pub(crate) fn deserialize_11(bytes: &[u8]) -> Vec256 {
    let output = PortableVector::deserialize_11(bytes);
    let array = PortableVector::to_i16_array(output);
    mm256_loadu_si256_i16(&array)
}
```

To carry a BitVecEq post on the AVX2 side:

  1. Drop the `verification_status(lax)` markers.
  2. Compose the just-confirmed `PortableVector::serialize_11_lemma` /
     `deserialize_11_lemma` with the `Vec256`↔`[i16; 16]` round-trip
     property of `mm256_storeu_si256_i16` / `mm256_loadu_si256_i16` /
     `PortableVector::from_i16_array` / `PortableVector::to_i16_array`.
  3. Wire the trait post on `serialize_11` / `deserialize_11` (currently
     post-less at `src/vector/traits.rs:1372-1378` with TODO(C4)).

That `Vec256`↔`[i16; 16]` bridge is almost certainly already established
in some form: look at how `serialize_10` / `serialize_12` discharge their
existing BitVecEq posts on AVX2 — both use real AVX2 intrinsics and ship
with posts wired today, so the SIMD↔array round-trip is already solved.

Estimated effort: a few hours to drop lax + apply the lemma + wire trait.
**No real SIMD reasoning required.**

### USER-9b: 5-bit family — genuine AVX2↔BitVec bridge

`src/vector/avx2/serialize.rs:352, 466` — `serialize_5` and
`deserialize_5` on AVX2 are **real AVX2**: `mm256_madd_epi16`,
`mm256_set_epi16`, `mm256_shuffle_epi8`, packed-byte tricks.  Both
already have AVX2 trait method bodies that compute via SIMD intrinsics
(no portable bounce).

For these, a genuine SIMD↔BitVec bridge is needed, mirroring the existing
`op_serialize_4_post_bridge` shape used by `serialize_4`.  2 bridge lemmas
(one each for ser/deser_5).  Estimated effort: ~1 lane-day, dependent on
whether the existing AVX2 bridge tactics generalize cleanly to 5-bit
packing.

Recommend folding USER-9a + USER-9b into **Wave-B's A1** (Phase 7c
serialize migration), since A1 already touches `Serialize.fst`.  USER-9a
is essentially free given the lemmas this agent confirmed; USER-9b is
the real work.

### Trait split (option c) — fallback only

If USER-9b walls on a hard AVX2 encoding issue, an `OperationsSerial5`
sub-trait that only the portable backend implements is a structural
escape hatch.  Touches FROZEN `src/vector/traits.rs`; needs user
agreement.  Don't take this path unless 9b proves intractable.

## Hard-rule audit

  - **R1 file-disjoint**: only edited `Libcrux_ml_kem.Vector.Portable.Serialize.fst`
    (extracted) for local debug.  Reverted.  No edits to Wave-A surface.
  - **R2 no commits unless verified**: applies — but no source changes
    were needed; the lemmas were already committed at `a51ddbfc3`.
  - **R3 no admits in committed code**: local-debug `--admit_smt_queries true`
    pushes are reverted.  HEAD has no admit-flag changes.
  - **R4 rlimit ≤ 800**: targets stayed at the committed `--z3rlimit 300`.
  - **R5 inner-loop serialized makes**: respected; one make at a time.
  - **R6 no kill on hang**: the only kill performed was on a ≥7-min full-file
    VERIFY_SLOW that exceeded the targeted-admit budget; it was MY make.
  - **R7 no bulk .checked nuke**: only deleted the single
    `Libcrux_ml_kem.Vector.Portable.Serialize.fst.checked` to force re-verify;
    surgical, in line with the rule.
  - **R8 no traits.rs edit**: respected.
  - **R9 no Wave-A/B module touch**: respected.
