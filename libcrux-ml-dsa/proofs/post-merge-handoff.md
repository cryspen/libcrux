# Post-merge handoff — single-lane ML-DSA proofs

**Branch**: `ml-dsa-proofs` (the `ml-dsa-above-trait` lane has been
merged in; tip after merge: `dd0fb629c`; tip after rlimit bumps:
`43c8d40dd`).

**Worktree**: `/Users/karthik/libcrux-ml-dsa-proofs/`.  The
`~/libcrux-ml-dsa-above-trait/` worktree should now be considered
**stale** — all future work happens here.

**Empirical baseline** (commit `43c8d40dd`):
- 99 modules invoked, [CHECK]=76, [ADMIT]=23, 0 F\* errors,
  0 make-level failures.
- All 23 admits are pre-budgeted (see "Pre-budgeted admits" below).

The lane-split protocol is no longer active.  Any agent in this
worktree may now edit any source file.  Trait pre/post changes
should be made directly here without a cherry-pick handshake.

## Quick start (any session)

```bash
cd /Users/karthik/libcrux-ml-dsa-proofs/libcrux-ml-dsa
git rev-parse HEAD                                # 43c8d40dd or descendant
proofs/agent-status/touch-unchanged-checked.sh snapshot
JOBS=2 ./hax.sh extract
proofs/agent-status/touch-unchanged-checked.sh skip-unchanged
JOBS=2 ./hax.sh prove 2>&1 > /tmp/baseline.log
grep -E "Modules invoked|F\* errors|^\* Error" /tmp/baseline.log
# Expect: 99 invoked, [CHECK]=76, [ADMIT]=23, 0 F* errors.
```

If the baseline isn't clean, **stop and diagnose** before editing.

## What's verified (76 CHECK modules)

Trait contract:
- `Libcrux_ml_dsa.Simd.Traits.{fsti,Specs.fst,fst}` — the
  `Operations` trait + spec helpers (`is_i32b_array_opaque`,
  `is_i32b_strict_lower_array_opaque`, `is_pos_array_opaque`,
  per-method `*_lane_post`, etc.).

Below-trait impls (was below-trait lane):
- `Simd.Portable.{fst, Vector_type, Sample, Arithmetic, Ntt, Invntt,
  Encoding.{Commitment,Error,Gamma1,T0,T1}}`.
- `Simd.Avx2.{fst, Vector_type, Arithmetic, Ntt, Invntt,
  Encoding.{Commitment,Error,Gamma1,T0,T1}}`.

Above-trait modules (was above-trait lane):
- `Constants`, `Types`.
- `Arithmetic` (with bumped rlimit on `make_hint`).
- `Polynomial`, `Polynomial.Spec`.
- `Ntt` (top-level, distinct from `Simd.*.Ntt`).
- `Encoding.{T0, T1, Commitment, Error, Gamma1, Verification_key,
  Signing_key, Signature}` — all closed.
- `Matrix` (with bumped rlimit on `add_vectors`).
- `Sample`, `Pre_hash`.
- `Hash_functions.{Shake128, Shake256, Portable, Simd256, Neon}`.
- `Ml_dsa_generic`, `Ml_dsa_generic.Ml_dsa_{44,65,87}_`,
  `Ml_dsa_generic.Multiplexing.{44,65,87}_`,
  `Ml_dsa_generic.Instantiations.{Portable,Avx2,Neon}.Ml_dsa_{44,65,87}_`.

Hacspec / spec:
- `Hacspec_ml_dsa.Commute.Chunk.fst` — per-lane commute lemmas
  bridging Hacspec semantics to per-lane post predicates.
- `Spec.Intrinsics.fst`, `Spec.MLDSA.Math.fst`, `Spec.MLDSA.Ntt.fst`.

## Pre-budgeted admits (23 modules, intentionally NOT verified yet)

Listed in `proofs/fstar/extraction/Makefile`'s `ADMIT_MODULES`
filter (i.e., everything not in `VERIFIED_MODULES`).

User-facing API wrappers (12):
- `Libcrux_ml_dsa.Ml_dsa_{44,65,87}_.fst` and the
  `.{Avx2,Neon,Portable}` variants.

These are the public entry points (`generate_key_pair`, `sign`,
`verify`).  They thread through the verified core via
`Ml_dsa_generic.*` (which IS verified).  Closing them requires
top-level functional-correctness specs that don't exist yet.
**Stretch goal** for a future sprint.

Type-level glue (3):
- `Libcrux_ml_dsa.Constants.Ml_dsa_{44,65,87}_.fst` — per-parameter
  set constant collections.  Just consts; should verify trivially.

Sample dispatchers (4):
- `Libcrux_ml_dsa.Samplex4.{Avx2,Neon,Portable}.fst`,
  `Libcrux_ml_dsa.Samplex4.fst` — X4-parallel matrix sampling.
  Requires trait-method panic-freedom on the underlying X4 Xof
  hash functions.

AVX2 rejection sample shuffle table + samplers (3):
- `Simd.Avx2.Rejection_sample.{Less_than_eta,Less_than_field_modulus,Shuffle_table}.fst`.
- The shuffle table is pure data; the samplers are admit-only
  pending bit-vec body proofs (similar shape to the Step 13 Track A
  AVX2 closures).

Spec dispatcher (1):
- `Libcrux_ml_dsa.Specs.Simd.Portable.Sample.fst` — internal spec
  helper; admit-only.

## Outstanding admits (within VERIFIED modules)

Top-level body admits (function-level `hax_lib::fstar!("admit ()")`)
and `panic_free` annotations remain in CHECKed modules.  The
catalog is `proofs/outstanding-admits.md`.  Highlights:

**Ml_dsa_generic.* — 10+ functions body-admitted** (`sign_internal`,
`verify_internal`, `generate_key_pair_internal`, ...).  These are
the orchestrator — closing them is the largest remaining proof
effort.  Each carries strong wrapper pre/post (the surrounding
contracts hold), but the body's chain of calls is admitted.

**Sample.fst — 9 of 10 functions body-admit**.  Above-trait closed
5 of 10 in commit `09d0743d3`; the remaining are the rejection
sampling state machines + Xof-trait-dependent flows.

**Matrix.fst — 6 wrappers admit-bodied**:
`compute_as1_plus_s2`, `compute_matrix_x_mask`,
`vector_times_ring_element`, `add_vectors`, `subtract_vectors`,
`compute_w_approx`.  Strong pre/post; bodies admit.

**Encoding.* wrappers — admit bodies**:
`Verification_key.{generate_serialized,deserialize}`,
`Signing_key.generate_serialized`, `Signature.{serialize,deserialize}`.
F-13 / F-14 / F-15 closures (above-trait `577a112cf`,
`8fa040756`, `65940351b`, `743956689`) closed several but others
remain.

**Arithmetic.fst** — `power2round_vector` body admit (hax IndexMut
quirk, see `outstanding-admits.md`).

**Hash_functions.{Portable,Simd256,Neon}** — Xof impls have
opaque admit bodies (5 modules verify their trait declarations
without body verification).

## Pre-budgeted "USER lane" admits (non-Z3 SIMD)

These are pre-known to require manual proof refactoring:
- `Simd.Portable.Ntt.{layer_*}` and `Simd.Avx2.Ntt.{layer_1,layer_2}`
  — wide SIMD layer Z3 timeouts.
- `Simd.{Portable,Avx2}.Invntt.{layer_3,layer_4}` — same.
- `Hacspec_ml_dsa.Commute.Chunk.lemma_ntt_full_commute` — Tier-3
  composition admit.

See `proofs/outstanding-admits.md` Pre-budgeted section.

## Recommended next sessions

### Session A: Close Ml_dsa_generic.* function bodies
Largest remaining proof effort.  Each function in
`src/ml_dsa_generic.rs` is body-admitted with strong wrapper
pre/post.  Closing requires threading the per-call posts through
the orchestrator's call chain.  Start with the smallest
(`generate_key_pair_internal`?), then `sign_internal`,
`verify_internal`.  Per-function 1-2hr each.  ~10 functions total.

### Session B: Close encoding wrappers
`src/encoding/{verification_key,signing_key,signature}.rs` body
admits.  These are mostly offset-arithmetic and copy_from_slice
threading.  Above-trait proved this is tractable (commits
`8fa040756`, `743956689`).  Per-function 30-60 min.

### Session C: AVX2 Rejection_sample.{Less_than_eta,Less_than_field_modulus}
Promote the shuffle-table + samplers to CHECK.  Shape similar to
Step 13 Track A AVX2 closures.  Per-fn 1-2hr.

### Session D: Sample.fst remaining 5 admits
Above-trait did 5 of 10; finish the other 5.  Many are Xof-trait
flows — may need Hash_functions.Shake128.fst trait method
strengthening too.

### Session E: USER-lane pre-budgeted (NTT/Invntt SIMD layers)
Refactor each AVX2 layer body into 4 per-zeta sub-functions to
split Z3 obligations.  Long-running USER work; not for a 2-hour
session.  See `proofs/manual-proof-targets.md` for ML-KEM analog.

### Session F (one-shot): clean up duplicated lane-split-protocol
entries
The merge resolved conflicts by taking HEAD; some F-N entries
appear twice (open + resolved).  Mostly cosmetic but worth a
~30 min pass to dedupe.  Don't do this and Session A in the same
day — context-switch cost.

## Active F-N findings (open)

From `proofs/agent-status/lane-split-protocol.md`:
- **F-3** — encoding `*_serialize` trait pres signed-vs-non-negative
  mismatch.  Above-trait fix landed (`cdb6e946e`); below-trait
  mirror landed (`027fc57b5`).  Mostly resolved; some downstream
  cleanups remain.
- **F-4** — `compute_hint_lane_post` divergence.  Resolved by
  switching post to cite `compute_one_hint` directly.
- **F-5** — `reduce_lane_post` to FIELD_MID — open finding;
  decision pending (option (a) impl-side correction step vs option
  (b) accept looser `is_i32b 4194303` bound).
- **F-13** — `decompose` strict-lower bound RESOLVED (revert).
- **F-14** — `error_deserialize` trait post FIPS BitUnpack range
  RESOLVED (FIPS-correct asymmetric range).
- **F-15** — `Encoding.Error.deserialize_to_vector_then_ntt`
  length-pres + admit RESOLVED (above-trait).

The **F-N numbering is stable**; new findings should pick up at
F-16.  Both lanes' duplicated F-N text (F-12, F-8/9/10/11 batch
re-entered) was resolved by taking HEAD's text — some duplicate
entries remain in the doc and are flagged as a Session F cleanup.

## Sanity-check checklist for next session

```bash
# 1. Confirm tip:
git log --oneline -5

# 2. Confirm clean state:
git status

# 3. Snapshot + extract + skip-unchanged + prove:
proofs/agent-status/touch-unchanged-checked.sh snapshot
JOBS=2 ./hax.sh extract
proofs/agent-status/touch-unchanged-checked.sh skip-unchanged
JOBS=2 ./hax.sh prove 2>&1 > /tmp/baseline.log

# 4. Confirm baseline:
grep -E "Modules invoked|F\* errors" /tmp/baseline.log
# Expect:
#   Modules invoked:        99  ([CHECK]=76  [ADMIT]=23)
#   F* errors reported:     0
```

If the baseline drifts (CHECK count drops or errors appear), the
first task of the session is to find what regressed.  Likely
suspects: rlimit-fragile queries (the Step 13/14 work pushed
several modules close to their rlimit budgets — see
`proofs/agent-status/fstar-perf-top20.md`).

## Useful pointers

- `proofs/outstanding-admits.md` — admit catalog with diagnosis +
  mitigation per item.
- `proofs/agent-status/lane-split-protocol.md` — F-N findings ledger
  (still useful as historical record even though the lane split is
  no longer active).
- `proofs/agent-status/fstar-perf-top20.md` — Z3 hot-path tracking;
  refresh after any prove that touches NTT/Invntt to catch
  regressions.
- `proofs/agent-status/touch-unchanged-checked.sh` — incremental
  build helper; use snapshot/skip-unchanged for fast iteration.
- `MLDSA_STATUS.md` — high-level status; pre-merge per-lane
  history retained at the bottom for context.
