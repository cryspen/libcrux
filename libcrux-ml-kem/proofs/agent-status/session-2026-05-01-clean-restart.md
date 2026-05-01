# Session report — 2026-05-01 clean restart of `libcrux-ml-kem-proofs`

Successor session to AUDIT-2026-05-01.md.  The audit identified the
2026-05-01 trait-opacify session as a sham migration (textual
Spec.MLKEM removal via Hacspec_ml_kem.* unfold-let wrappers); this
session sets up a fresh `libcrux-ml-kem-proofs` branch off the
pre-session SHA (`d28a79c26`) and lands the first non-wrapper
function migrations.

## Branch + setup

| Step | Commit | Notes |
|---|---|---|
| Stash uncommitted state on `trait-opacify` | (stash@{0}) | mixed wrapper-cite + legitimate Ntt body proof; preserved in stash, not applied |
| Create `libcrux-ml-kem-proofs` off `d28a79c26` | — | pre-suspect-session state |
| Cherry-pick `0be31f1a6` (SD4 reveal cleanup) | `eedafe11b` | sole audit-blessed commit from 2026-05-01 |
| `git mv Spec.MLKEM*.fst → _DEPRECATED_spec_mlkem/` | `967b6b0f2` | removes Spec.MLKEM from F* include path → broken refs become hard errors |
| Drop dead bridge lemmas in `Hacspec_ml_kem.Parameters.Sizes` | `20fbb16c9` | removed 5 transitional `lemma_*_eq` Spec.MLKEM bridges; zero callers; document KEEP exception |
| 4-function migration in `src/ind_cca.rs` + re-extract | `6b6835a20` | first real Hacspec_ml_kem migration on this branch |
| Add audit + clean-restart prompt docs | `bee8f0b1d` | cherry-pick of `9c314717b`; pure documentation |

`b3d3d7e5d` (`v_PRFxN` → `Spec.Utils.v_PRFxN`) was attempted but the
incoming patch context drags FORBIDDEN wrapper cites
(`Hacspec_ml_kem.Sample.sample_vector_cbd2_prf_input`) — aborted; the
2-line text replacement is trivial to re-apply during normal migration.

`b20b09862` + `daeffd891` + `7f549b318` (retrospective methodology
docs) NOT cherry-picked — analysis was based on cheat metrics per the
audit.

Final SHA on `libcrux-ml-kem-proofs`: **`bee8f0b1d`**.

## Functions migrated (4)

All in `src/ind_cca.rs`:

1. **`serialize_kem_secret_key_mut`** (lines 46–97):
   - Pre: `Spec.MLKEM.is_rank $K /\ ... v_CCA_PRIVATE_KEY_SIZE / v_CPA_PRIVATE_KEY_SIZE / v_CPA_PUBLIC_KEY_SIZE / v_SHARED_SECRET_SIZE`
   - Post: `Hacspec_ml_kem.Parameters.Sizes.is_rank $K /\ ... .v_CCA_PRIVATE_KEY_SIZE / .v_CPA_PRIVATE_KEY_SIZE / .v_CPA_PUBLIC_KEY_SIZE`, `Spec.MLKEM.v_SHARED_SECRET_SIZE` → `Hacspec_ml_kem.Parameters.Hash_functions.v_H_DIGEST_SIZE` (the canonical extracted real symbol).
   - Body `hax_lib::fstar!` block: 6 Spec.MLKEM cites cleared.

2. **`serialize_kem_secret_key`** (lines 99–124): same `requires`/`ensures` shape as `_mut` variant; identical migration.

3. **`validate_public_key`** (lines 131–150):
   - Pre: `Spec.MLKEM.is_rank $K /\ $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K`
   - Post: `Hacspec_ml_kem.Parameters.Sizes.is_rank $K /\ $PUBLIC_KEY_SIZE == Hacspec_ml_kem.Parameters.Sizes.v_CPA_PUBLIC_KEY_SIZE $K`.  Justification: `Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE r ≡ v_CPA_PUBLIC_KEY_SIZE r` per Spec.MLKEM.fst:93, and `Hacspec_ml_kem.Parameters.Sizes.v_CCA_PUBLIC_KEY_SIZE` is intentionally not defined (per the prompt's "do not extend Parameters.Sizes" rule).

4. **`validate_private_key_only`** (lines 178–194):
   - Pre: `Spec.MLKEM.is_rank $K /\ $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K`
   - Post: `Hacspec_ml_kem.Parameters.Sizes.is_rank $K /\ $SECRET_KEY_SIZE == Hacspec_ml_kem.Parameters.Sizes.v_CCA_PRIVATE_KEY_SIZE $K`.

### Not migrated (deferred)

- **`validate_private_key`** (lines 157–172): cites `Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE`, which is NOT in `Parameters.Sizes` and per the prompt rule "do not extend Parameters.Sizes."  Real target per the mapping table is `t_MlKemParams.impl_MlKemParams__ciphertext_size`, requiring threading a `t_MlKemParams` value through the rank-generic Rust signature (architectural refactor out of scope for this 4-hour session).

## New content in `/specs/ml-kem/src/`

None.  All target citations resolved to existing extracted Hacspec
symbols (`Hacspec_ml_kem.Parameters.Hash_functions.v_H_DIGEST_SIZE`)
or pre-existing audit-grandfathered `Hacspec_ml_kem.Parameters.Sizes.*`
helpers.

## Decisions recorded

### `Hacspec_ml_kem.Parameters.Sizes` — KEEP for this session

Per the clean-restart prompt's "Decide first" mandate.  Justification:

- Bodies (lines 1-46 of the post-cleanup file) are real concrete
  definitions over the extracted `Hacspec_ml_kem.Parameters.v_BYTES_PER_RING_ELEMENT`,
  NOT `unfold let X = Spec.MLKEM.X` wrappers.
- Migrating the ~322 src/ consumers to the canonical `t_MlKemParams`
  shape requires either threading a `t_MlKemParams` value through
  rank-generic Rust signatures, or substantial Rust API refactoring
  per-instance — beyond the 4-hour session cap.
- Document-as-exception is explicitly allowed by the prompt: "If
  keeping, document the exception and do not extend it."  Header
  comment in `Hacspec_ml_kem.Parameters.Sizes.fst` updated accordingly.

Cleanup performed: removed 5 dead transitional `lemma_*_eq` Spec.MLKEM
bridge lemmas (`lemma_v_ETA1_eq`, `lemma_v_ETA1_RANDOMNESS_SIZE_eq`,
`lemma_v_RANKED_BYTES_PER_RING_ELEMENT_eq`,
`lemma_v_CPA_PUBLIC_KEY_SIZE_eq`, `lemma_v_CCA_PRIVATE_KEY_SIZE_eq`).
Zero callers across the repo before removal (verified by
`grep -rE 'lemma_v_(ETA1|RANKED|CPA|CCA)_.*_eq'`).

Do NOT extend.  Future migration: replace consumers with extracted
`Hacspec_ml_kem.Parameters.{t_MlKemParams, impl_MlKemParams__*,
v_ML_KEM_*_*_SIZE}`, then delete the file entirely.

## Build state

Make from `proofs/fstar/extraction/` after each step:

| Step | Outcome |
|---|---|
| `967b6b0f2` (Spec.MLKEM moved) | fails at `Hacspec_ml_kem.Parameters.Sizes.fst:52` — `Spec.MLKEM` unresolved in dead bridge lemma |
| `20fbb16c9` (Sizes cleanup) | progresses past Sizes (1.6 s, 12 queries pass with hint, max rlimit 0.094); fails at `Libcrux_ml_kem.Ind_cca.fsti(39)` — `Spec.MLKEM.v_SHARED_SECRET_SIZE` referenced indirectly via extraction-drift in `serialize_kem_secret_key_mut` |
| `6b6835a20` (4-function migration + re-extract) | progresses past 4 functions; fails at `Libcrux_ml_kem.Ind_cca.fsti(111)` — `Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE` in `validate_private_key` (deliberately deferred) |

## F\* perf delta

`Hacspec_ml_kem.Parameters.Sizes`: cold-on-mac, full re-verify after
the bridge-lemma drop:
- 12 queries, all succeed with hint
- max rlimit used: 0.094 (well under 80 cap)
- TOTAL TIME: 1625 ms

No other module reached full verification this session (Ind_cca.fsti
deferred-blocker prevents downstream verification).

## Spec.MLKEM hit-count delta

Per the prompt's "must be 0 in src/; commute/ count monotonically
decreasing":

| Area | At `d28a79c26` (branch base) | At `bee8f0b1d` (this session end) | Delta |
|---|---|---|---|
| `libcrux-ml-kem/src/` | 322 | **296** | -26 |
| `libcrux-ml-kem/src/ind_cca.rs` | 137 | **119** | -18 |
| `specs/ml-kem/proofs/fstar/commute/` (code) | 12 (Parameters.Sizes only) | **0** | -12 (only comments remain) |
| `libcrux-ml-kem/proofs/fstar/extraction/` | 81 (extraction-drift) | **523** (canonical Rust→F*) | +442 |

Note on extraction count rise: re-extraction surfaced the canonical
state of the Rust source.  The `81` pre-extract figure was
extraction-drift — extracted .fsti files lagged the Rust source
(prior session migrations weren't followed by re-extraction).  The
new `523` is the ground-truth count of cites that need migration in
src/ to drive extraction/ to zero.

src/ count is NOT zero — this session migrated 4/322 cites (cap was
4-5 functions or 4 hours per the prompt).  Future sessions need to
work through the remaining 296 cites following the same per-function
recipe.

## Self-audit (R10)

| Anti-pattern | Status |
|---|---|
| Created any new `Hacspec_ml_kem.<X>.fst` file (top-level squat) | NO |
| Added any `unfold let X = Spec.MLKEM.X` alias | NO |
| Added any new SMTPat-triggered `lemma_X == Spec.MLKEM.X` equality | NO |
| Extended `Hacspec_ml_kem.Parameters.Sizes` (added new symbols) | NO — REMOVED 5 dead lemmas instead |
| Created any new spec content under `Hacspec_ml_kem.*` | NO |
| Re-extracted .fsti points back to Spec.MLKEM resolved against the deprecated path | NO — Spec.MLKEM moved to `_DEPRECATED_spec_mlkem/` (not on F* include path); cites that remain in extraction are a TODO list, not a working build |

`ls specs/ml-kem/proofs/fstar/commute/` confirms no FORBIDDEN wrapper
modules exist:
```
Hacspec_ml_kem.Commute.Bridges.fst    (KEEP — bridge lemmas, sub-namespace)
Hacspec_ml_kem.Commute.Chunk.fst      (KEEP — bridge lemmas, sub-namespace)
Hacspec_ml_kem.ModQ.fst               (KEEP — opacity helper)
Hacspec_ml_kem.Parameters.Sizes.fst   (KEEP — exception, documented; bodies real)
Makefile, hax.fst.config.json
```

No `Hacspec_ml_kem.{Sample,Encode,Cpa,Cca,NttSpec,Instances,Math}.fst`
present — those were the FORBIDDEN wrapper modules introduced by the
suspect 2026-05-01 session and were dropped by branching off
`d28a79c26`.

## Re-extraction byproducts

`Libcrux_ml_kem.Ntt.fst` was incidentally re-extracted with +140/-9
lines of body proof material (the `e_re_init` init-invariant under
`--z3rlimit 800 --split_queries always`, calls to
`Hacspec_ml_kem.Commute.Bridges.lemma_ntt_layer_1_step_to_hacspec`
and `Vector.Traits.Spec.zetas_4`).  This is Phase 2 opacity / Phase
7-style work that `src/ntt.rs` annotations produce; the committed
extracted file at HEAD lagged the Rust source.  The file is
downstream of `Ind_cca.fsti`'s deferred `validate_private_key`
blocker, so its proof material is unverified by today's session —
flagged as the **first thing to verify** in the next session once
`validate_private_key` is migrated.

The stash from session start (`stash@{0}`) contains earlier
hand-edited Ntt.fst material that matches the re-extracted output —
indicating the stashed work was actually a snapshot of the
re-extracted state.  Stash can be safely dropped once next session
verifies Ntt.fst builds clean.

## Next-session priorities

1. **Migrate `validate_private_key`** — needs `v_CPA_CIPHERTEXT_SIZE` resolution.  Options:
   a. Add `v_CPA_CIPHERTEXT_SIZE` to `/specs/ml-kem/src/parameters.rs` as a rank-generic Rust top-level (re-extract; `Hacspec_ml_kem.Parameters.v_CPA_CIPHERTEXT_SIZE r` would become available).
   b. Refactor `validate_private_key` to take a `t_MlKemParams` value and cite `impl_MlKemParams__ciphertext_size`.
   Option (a) is the prompt's prescribed path (workflow step 4: "Where a real Hacspec symbol is missing, ADD it to /specs/ml-kem/src/").
2. **Verify `Libcrux_ml_kem.Ntt.fst` builds clean** once Ind_cca.fsti unblocks downstream.  If the body proof material has issues, the next session can fall back to the existing stash for reference.
3. **Drive src/ Spec.MLKEM count from 296 → 0** via the per-function recipe.  Same `Hacspec_ml_kem.Parameters.Sizes.*` + `Hash_functions.v_H_DIGEST_SIZE` mapping covers the bulk of the next ~150-200 cites in `ind_cca.rs` and `ind_cpa.rs`.
4. **Plan the `Parameters.Sizes` removal** once src/ cites are gone — replace with `t_MlKemParams`-shape consumers, then delete `Hacspec_ml_kem.Parameters.Sizes.fst`.
