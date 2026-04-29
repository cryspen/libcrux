# Handoff — 2026-04-29 end-of-day (post-Wave-B parallel fanout)

**Branch**: `trait-opacify`
**Tip**: `cf9e06da7` (`agent-coord: bug-demo-prompt — standalone Rust+hax+F* demo of two real bugs`)
**Last clean baseline**: take-6 in `~/libcrux-ml-kem-above-trait/` at HEAD,
`FINAL_EXIT=0`, ~9 min cold (see `/tmp/wave-b-baseline-take6.log`).
**Snapshot of perf top-20**: `proofs/agent-status/fstar-perf-top20.md`
"Snapshot 3" (post-Wave-B-merge).
**111 commits ahead of `origin/trait-opacify`.**  Push origin is the
user's call — no test gating it.

---

## What's done (✅)

### Phase 0 / H / 1 / 2 (Waves before today)

  - Phase 0 — empirical edit-check loop study (canonical: `make check/<Mod>.fst`).
  - Phase H — opaque arithmetic (`Hacspec_ml_kem.ModQ`) at trait boundary.
  - Phase 1 — trait pre/post fixes (Cluster 1 ✅, Cluster 3 partial → USER-9 closed; Cluster 2/4 → USER-8/10).
  - Phase 2 (Wave-A) — below-trait B6 closed (USER-1 / A8 4-case Barrett).
  - Wave-A continuation — B1 partial + B3 full + USER-9a closed (commits `f87e9a8cf`, `e5c4a6f49`, `2deb01199`).

### USER-N closed today (2026-04-29)

  - **USER-1** ✅ (Wave-A B6) — `lemma_compress_ciphertext_coefficient_fe_commute` 4-case Barrett, commit `2f96abe99`.
  - **USER-7** ✅ (Wave-B A3) — `subtract_reduce` body discharge.  Resolution: hypothesis (b) array-form bridge **+ parameter unshadowing trick** (rename `mut b` → `let mut b_acc = b` so the parameter name stays nameable in post-loop F* fragments).  Commits `0f247d2d4`, `666e355d0`.  See memory `feedback_for_loop_param_unshadowing`.
  - **USER-9a + USER-9b** ✅ — trait `serialize_5/11` and `deserialize_5/11` posts wired (4 trait methods strengthened, AVX2 SIMD↔BitVec via existing `bit_vec_of_int_t_array_vec256_as_i16x16_lemma` axiom — no new axioms).  Commits `2deb01199`, `107c76641`.
  - **A1** (Phase 7c partial, Wave-B) — dropped `panic_free` on `to_unsigned_field_modulus` (commit `f322d99eb`).  3 fns reverted under cap on Phase 7c hacspec citation gap.

### USER-N partial / strategic (🔶)

  - **USER-6 (invert_ntt_montgomery)** — Wave-B A5 strengthened the post chain via DRIVE-TO-THE-TOP spike.  Commits `14a9a34d5`, `5634829cc`, `44646f0cd`.  See memory `feedback_drive_to_top_spike`.
    - Step 3.3 (`mont_to_spec_poly_256` / `zetas_8` helpers in Chunk.fst): ✅ closed.
    - Step 4 layer_4_plus post: ✅ strengthened citing `IN.ntt_inverse_layer`; body → **USER-14** (admitted).
    - Step 5 `invert_ntt_montgomery` post: ✅ strengthened citing `IN.ntt_inverse_butterflies`; body → **USER-15** (admitted).
    - Layer_2 body: pre-existing Z3 wall now NEW TEMP admit (`--admit_smt_queries true`) → **USER-13** carry-over.
    - Q101 fix on `inv_ntt_layer_int_vec_step_reduce`: rlimit 200→400 + 2 `mod_q_eq_unfold` calls in aux0/aux1.
    - **CRITICAL**: post propagates cleanly to `Polynomial.fst` (77 s) and `Bridges.fst` (183 s).  Wave-C does NOT need spec redesign.
  - **USER-8 (from_bytes/to_bytes)** — S1 (trait wire-up) ✅ closed (commit `bb6f740a2`).  S2/S3 (impl bodies) ADMITTED.  4 admits filed under USER-14.

---

## Open (⏸) — USER-N priority order

| # | Task | Files | Effort | Path |
|---|------|-------|--------|------|
| **USER-15 (NEW)** | `invert_ntt_montgomery` body discharge | `src/invert_ntt.rs:invert_ntt_montgomery` | 2-3 hr | Definitional unfolding of `IN.ntt_inverse_butterflies` — see "Step 5 strategy" below |
| **USER-14 (carry-over)** | `from_bytes/to_bytes` impl bodies + `layer_4_plus` body | `src/vector/portable.rs:957-983`, `src/vector/avx2.rs:1051-1073`, `src/invert_ntt.rs:invert_ntt_at_layer_4_plus` | 4-6 hr | See "Step 4 strategy" + "Path 1a/1b" in MLKEM_STATUS USER-14 |
| **USER-13** | layer_2 body + B1 chunk wrappers (compress_1, compress\<D\>, decompress_d) | `src/vector/portable/compress.rs:170/222/347`, `src/invert_ntt.rs:invert_ntt_at_layer_2` | 2-3 hr | SD3 opaque-wrapper pattern (forward layer_2 unlock at `b7b49c358`) |
| **USER-12** | portable NTT layer 1 admit_smt_queries | `src/vector/portable.rs:422, 661` | 2 hr | Mirror `b7b49c358` — 4 per-branch helpers + per-lane wrapper + split_queries |
| **USER-11** | `op_ntt_multiply` panic_free (both backends) | `src/vector/portable.rs:899`, `src/vector/avx2.rs:571` | 2 hr | Per-branch decomposition — see MLKEM_STATUS USER-11 |
| **USER-10** | rej_sample wire-up + drop `lax` on `sample_from_uniform_distribution_next` | `src/sampling.rs:51` | 1-2 hr (smtprofiling) | `--smtencoding.elim_box`, body refactor making `update_at_usize` opaque to invariant |
| **USER-4** | AVX2 NTT layers 1/2 bridges | `src/vector/avx2.rs` | 2 hr | Sister of USER-12 |
| **USER-2** | full forward NTT composition (Tier-3) | `Hacspec_ml_kem.Commute.Chunk.fst` (NEW lemma) | 1-2 hr | Template for USER-5 |
| **USER-5** | `ntt_multiply` Tier-3 (after USER-2) | `src/polynomial.rs` | 1 hr | Mechanical after USER-2 |
| **USER-3** | `to_standard_domain` Mont-inverse identity | `src/polynomial.rs:711-809` | 1 hr | Standalone modular arithmetic |

### Phase 7 remaining (above-trait):

  - **Phase 7c (Serialize migration)** — 13 panic_free + 4 lax remaining on `src/serialize.rs`.  Each function is its own session (Wave-B A1 closed 1, found 3 more need hacspec citations to land first).
  - **Phase 7d (Matrix)** — gated on Wave-C kickoff; `Libcrux_ml_kem.Matrix.fst` admitted via SLOW_MODULES.
  - **Phase 7j-m (Spec.MLKEM teardown)** — sequential cleanup: 7j Ind_cpa/Ind_cca migration → 7k drop redundant conjuncts → 7l delete Spec.MLKEM module → 7m Spec.Utils → Proof_utils rename.

---

## Sprint critical path (post-Wave-B)

A6 (Matrix) → A7 (Ind_cpa) → A8 (Ind_cca) consumer chain is **unblocked** by USER-6's strengthened post.  Recommended order:

1. **USER-13 first** (layer_2 body) — proven SD3 pattern, ~2 hr; clears the Wave-A baseline regression that's been around since 2026-04-28.
2. **USER-15** (`invert_ntt_montgomery` body) — definitional unfold; ~2 hr.
3. **USER-14** (path 1a from MLKEM_STATUS — Vector_type body refactor + Tactics.GetBit cycle break) — ~2 hr.
4. **A6 (Matrix)** — start Wave-C.  Matrix consumes the strengthened invert_ntt_montgomery post; A5 verified propagation is clean.
5. **A7, A8** — Ind_cpa, Ind_cca — sequentially after A6.

USER-2/5 (forward NTT compositions) can run in parallel with anything; USER-10/11/12/3/4 are independent.

---

## Step 4 / 5 body discharge strategies (for USER-13/14/15)

(Detailed in chat 2026-04-29 evening; copying here for handoff.)

### USER-15 — `invert_ntt_montgomery` body

Chains 7 layer calls (`invert_ntt_at_layer_1` through `_4_plus` × 4) into `IN.ntt_inverse_butterflies`.  Strategies:

  1. **Definitional unfolding lemma** in `Hacspec_ml_kem.Commute.Bridges.fst`:
     ```
     lemma_ntt_inverse_butterflies_unfold:
       IN.ntt_inverse_butterflies p ==
         IN.ntt_inverse_layer (... (IN.ntt_inverse_layer p 1) ...) 7
     ```
     Body applies this after the 7 layer calls.
  2. **Step-by-step reveal** inside body: reveal `ntt_inverse_butterflies` definition after each layer; accumulate the 7-fold composition.

  Path (1) is cleanest; the unfold lemma is structural (`= refl` modulo definitions).

### USER-14 — `invert_ntt_at_layer_4_plus` body

Chains 16 chunk-pair calls of `inv_ntt_layer_int_vec_step_reduce` into the polynomial-level claim.  The chunk-pair bridge already exists (`lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec`); gap is lifting 16 chunk-pair eqs to one polynomial eq.  Strategies:

  1. **Per-chunk-pair bridge + post-loop `Classical.forall_intro`** in `Bridges.fst` (NEW lemma `lemma_inv_ntt_layer_int_vec_to_poly`).  Estimated 1-2 sess; mirrors USER-7's pattern.
  2. **Loop invariant in `inv_butterfly` form** using `mont_to_spec_poly_256_lane` unfold helper.

### USER-13 — `invert_ntt_at_layer_2` body

Pre-existing Z3 wall.  Strategies (in priority order):

  1. **Per-chunk opaque predicate** (SD3 pattern from `lane-split-protocol.md`) — same trick that closed forward layer_2 in `b7b49c358`.  Wrap the loop invariant's per-chunk post in `[@@ "opaque_to_smt"]`.  See memory `feedback_layer2_branch_post_z3_unlock`.
  2. **Per-iteration helper lemma** that takes a single chunk-pair and produces the post-step equation.
  3. **smtprofiling-driven SMT-encoding tweaks** (`--smtencoding.elim_box`, `--using_facts_from`).

Path (1) is the proven pattern (forward layer_2 closed via this exact trick).  Cost: 1-2 hr.

---

## Lane worktrees preserved (next-session resources)

```
/Users/karthik/libcrux-ml-kem-above-trait/  trait-opacify (cf9e06da7)
/Users/karthik/libcrux-ml-kem-lane-A1       agent/lane-A1 (f322d99eb, A1 closed)
/Users/karthik/libcrux-ml-kem-lane-A2       agent/lane-A2 (ccf098682, A2 doc only)
/Users/karthik/libcrux-ml-kem-lane-A3       agent/lane-A3 (666e355d0, A3 closed)
/Users/karthik/libcrux-ml-kem-lane-A5       agent/lane-A5 (44646f0cd, A5 closed)
```

Wave-B local Makefile (with TEMP admits on Vector.{Portable,Avx2}.* + Wave-C surface) is in working-tree of `~/libcrux-ml-kem-above-trait/` (uncommitted).

---

## Known gotchas (memory-saved 2026-04-29)

  - `feedback_panic_free_vs_lax` — only `verification_status(lax)` emits `--admit_smt_queries true`.  `panic_free` is full SMT verification.  No middle step.
  - `feedback_for_loop_param_unshadowing` — for `mut <param>: T` + `for` loop, hax shadows the parameter.  Rename loop accumulator (`let mut acc = <param>`) so post-loop F* fragments can name `<param>`.
  - `feedback_drive_to_top_spike` — strengthen post chain top-down with `--admit_smt_queries true` on bodies; verify spec via consumer propagation BEFORE discharging.
  - **hax codegen bug — duplicate `noeq`** on `Vector.Neon.Vector_type.fsti.t_SIMD128Vector`.  Local fix in above-trait worktree's gitignored .fsti via `sed`; re-emerges after every `python3 hax.py extract`.  File as new USER-N if not already tracked.
  - **layer_2 perf regression** — `lemma_inv_ntt_layer_2_step_lane_bridge` 3.4 s → 146 s after Wave-B's Chunk.fst additions.  Hint re-record didn't fix (1 query truly walls).  USER-13 strategy (1) is the closure.

---

## Shippable state — push origin?

`origin/trait-opacify` is 111 commits behind local.  Last clean full-tree make was `cf9e06da7` (take-6 today, FINAL_EXIT=0).  Net admit-count delta from session-baseline:

  - **PROGRESS**: -1 (USER-1, B6) -2 (B1 partial), -13 (B3) -1 (A1), -1 (A3 USER-7), -2 (USER-9a/b) = ~-20 admits removed and proofs closed for real.
  - **SIDEWAYS**: ~+5 (USER-9b axioms reused, no new SIDEWAYS axioms; USER-8 wired to USER-14 admits; A5 strengthened posts with bodies admitted).
  - **FAIR GAME**: USER-13/14/15 newly filed (with concrete strategies).

Push if you're comfortable with the snapshot.  No regressions in upstream-clean Makefile-state full make.
