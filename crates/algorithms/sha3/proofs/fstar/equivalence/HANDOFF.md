# SHA-3 equivalence proof — session handoff

Date: 2026-04-20
Working dir: `crates/algorithms/sha3/proofs/fstar/equivalence/`
Branch: `proofs-cleanup`

## TL;DR

The 12 top-level hasher theorems (sha{224,256,384,512}_{portable,arm64} +
shake{128,256}_{portable,arm64}) in `EquivImplSpec.Sponge.{Portable,Arm64}.API`
are proved modulo **5 load-bearing `assume val` / `admit ()`** and 3
non-load-bearing upstream utility admits. The proof structure is sound;
no closure-equality `fold_range` problems remain.

`make` passes cleanly.

## Remaining admits / assumes

### Load-bearing (5)

| # | File | Line | Kind | What it assumes |
|---|------|------|------|-----------------|
| 1 | `EquivImplSpec.Sponge.Portable.API.fst` | 249 | `admit ()` | Slice-identity bridge inside `lemma_absorb_portable_aux` inductive branch: one unfold step of spec `absorb_rec`. Helper `lemma_absorb_rec_step` (same file) encodes the fact; calling it **triggers a Z3 4.13.3 LP-solver internal-assertion bug** at `lar_solver.cpp:1066` on fresh hint generation. `--z3refresh` works around per-query but exceeds `make` timeout. |
| 2 | `EquivImplSpec.Sponge.Portable.SqueezeAPI.fst` | 185 | `assume val lemma_squeeze_portable_middle` | One-iteration middle-loop bridge for the `fold_range 1 blocks` in Portable squeeze. Attempted proof produced 258 cascading Error 19 subtyping failures on the extractor's inline lambdas. 3 supporting helpers (`lemma_squeeze_once_portable`, `lemma_squeeze_state_grow_slice`, `lemma_squeeze_middle_one_step`) are **proved** in the same module. |
| 3 | `EquivImplSpec.Sponge.Portable.SqueezeAPI.fst` | 245 | `assume val lemma_squeeze_portable` | Driver: full Portable squeeze ≡ `Hacspec_sha3.Sponge.squeeze`. Depends on #2. |
| 4 | `EquivImplSpec.Sponge.Arm64.API.fst` | 63 | `assume val lemma_absorb2_arm64` | Per-lane driver absorb at N=2: `extract_lane l (absorb2 rate delim data).f_st ≡ Hacspec_sha3.Sponge.absorb rate delim (data[l])`. Black-box form over the extracted `Libcrux_sha3.Generic_keccak.Simd128.absorb2` function. |
| 5 | `EquivImplSpec.Sponge.Arm64.API.fst` | 82 | `assume val lemma_squeeze2_arm64` | Per-lane driver squeeze2 at N=2: lane-`l` output of `squeeze2 rate s out0 out1` ≡ `Hacspec_sha3.Sponge.squeeze outlen (extract_lane l s.f_st) rate`. Black-box form. |

`lemma_keccak2_arm64` itself is **fully proved** (5-line composition of #4 + #5).

### Non-load-bearing (3, upstream)

All in `Proof_Utils.Lemmas.fst`, flagged with `TODO` comments:

| Line | Lemma | Target |
|------|-------|--------|
| 26 | `logand_commutative` | hax-lib / core-models |
| 33 | `lemma_rotate_left_zero` | hax-lib / core-models |
| 54 | `lemma_index_update_at_range` | pure `Seq` — still used by proofs |

These don't affect spec-equivalence correctness; leave as upstream targets.

## Structural overview

```
12 top-level hasher theorems  (API.fst files)
  ↓
lemma_keccak1_portable  [PROVED]         lemma_keccak2_arm64  [PROVED]
  = lemma_absorb_portable                 = lemma_absorb2_arm64 per lane
  ; lemma_squeeze_portable                ; lemma_squeeze2_arm64 per lane
     │                │                           │        │
     ▼                ▼                           ▼        ▼
 lemma_absorb_   lemma_squeeze_               [assume 4] [assume 5]
  portable [PROVED  portable [assume 3]
  modulo admit 1]   in SqueezeAPI.fst
     │                │
     │          needs lemma_squeeze_portable_middle
     │                │ [assume 2]
     ▼                ▼
 Steps.fst + Generic.{Core,Squeeze}.fst + per-backend sc_* records [ALL PROVED]
```

## File inventory (equivalence/)

**Proof modules (all build cleanly):**
- `Proof_Utils.Lemmas.fst` — 3 upstream admits
- `Proof_Utils.NatFold.fst`, `Proof_Utils.FoldRange.fst`
- `EquivImplSpec.Keccakf.ChiFold.fst`
- `EquivImplSpec.Keccakf.Generic.fst` — closed (rho_offsets_values, keccak_f_is_rounds)
- `EquivImplSpec.Keccakf.Portable.fst`, `EquivImplSpec.Keccakf.Arm64.fst`
- `EquivImplSpec.Keccakf.SpecRounds.fst`
- `EquivImplSpec.Sponge.Generic.Core.fst`
- `EquivImplSpec.Sponge.Generic.Squeeze.fst`
- `EquivImplSpec.Sponge.Portable.fst` — sc_load_block / sc_load_last / sc_store_block all PROVED
- `EquivImplSpec.Sponge.Arm64.fst` — sc_load_block / sc_load_last / sc_store_block all PROVED
- `EquivImplSpec.Sponge.Portable.Steps.fst` — per-step absorb/squeeze lemmas
- `EquivImplSpec.Sponge.Arm64.Steps.fst` — per-step absorb/squeeze lemmas
- `EquivImplSpec.Sponge.Portable.SqueezeAPI.fst` — NEW MODULE, 3 proved helpers + assumes 2 & 3
- `EquivImplSpec.Sponge.Portable.API.fst` — re-exports from SqueezeAPI; assume 1
- `EquivImplSpec.Sponge.Arm64.API.fst` — assumes 4 & 5, `lemma_keccak2_arm64` PROVED

**Cleanup still pending (non-functional):**
- `equivalence/plan.md`, `equivalence/plan-simd.md`, `equivalence/Proofs.md` — stale plan notes
- `../extraction/Utils.fsti~` — editor backup

## Rust-side state

The Rust codebase has been refactored:
- `crates/algorithms/sha3/src/generic_keccak/simd128.rs` — `keccak2` split into named `absorb2` / `squeeze2` / `keccak2` matching Portable's `absorb` / `squeeze` / `keccak1` structure. This lets the Arm64 F* assume_vals refer to the named functions as a black box (mirroring Portable's style).
- No other Rust changes are needed for any remaining gap.

## How to close the remaining gaps

### Assume 1 (Portable.API.fst:249, slice-identity admit)

**Blocked by Z3 LP bug**, not a proof-strategy problem. Options:
- Wait for a Z3 version where the `lar_solver` bug is fixed.
- Rewrite `lemma_absorb_rec_step` so the inductive step can run without the inline lambdas that trigger the LP assertion (e.g. factor every `Seq.slice` into a named term; avoid nested typeclass-dispatched `.[RangeFrom]`).
- Apply `--z3refresh` per-query and raise the `make` timeout.

### Assumes 2–3 (Portable squeeze: middle + driver)

The 3 proved helpers in `SqueezeAPI.fst` provide the pieces; what's missing is the induction that glues them across `fold_range 1 blocks`. Prior attempt blew up on subtyping of the extractor's inline lambdas. Likely tactics:
- Factor the middle-loop step into a named `let`-bound state update so Z3 sees a simpler term.
- Use `Classical.forall_intro (Classical.move_requires aux)` instead of trying to prove the fold invariant directly.
- If still stuck, split into a per-index pointwise lemma + `Seq.lemma_eq_intro` as the final bridge (matching the pattern used in `lemma_squeeze_state_grow_slice`).

### Assumes 4–5 (Arm64 per-lane absorb2 / squeeze2)

Symmetric with Portable's `lemma_absorb_portable` / `lemma_squeeze_portable`. Strategy:
1. Mirror `lemma_absorb_portable_aux` at N=2, parameterised over lane `l ∈ {0,1}`. Uses closed Arm64 `sc_load_block` / `sc_load_last` records + the `lemma_arm64_lane_eq_get_lane_u64` SMTPat (already committed) for extract_lane indexing.
2. Mirror the squeeze induction (same as gap 2–3) at N=2 per lane, using the closed Arm64 `sc_store_block` record.

Expected: reuse the Portable proof scaffolding once gap 2 is solved — the only difference is `v_N = mk_usize 2` and the lane parameter.

## Verification commands

```bash
# Clean rebuild (remove only specific .checked files — DO NOT wipe the cache):
rm -f /Users/karthik/libcrux-proofs-cleanup/.fstar-cache/checked/EquivImplSpec.Sponge.*.fst.checked
cd /Users/karthik/libcrux-proofs-cleanup/crates/algorithms/sha3/proofs/fstar/equivalence
make

# Status check (should list exactly the 5 load-bearing + 3 upstream):
rg -n "^(assume val|.* admit \(\))" *.fst Proof_Utils.Lemmas.fst

# Re-extract F* from Rust (only if the Rust side changes):
bash /Users/karthik/libcrux-proofs-cleanup/crates/algorithms/sha3/hax.sh extract
```

## Key context / pitfalls

- **Z3 `z3rlimit` ≤ 300** — do not raise higher.
- **Never clear the F* cache** — delete only specific `.checked` files.
- **Rust changes require re-extraction** via `hax.sh extract`.
- **`cargo fmt` the touched Rust crates** before committing.
- **Heavy F* proofs** — factor into separate modules (done for `SqueezeAPI`) to control Z3 context.
- **`lemma_fold_range_step`** requires syntactic match with the extractor's inline lambdas — that's what killed prior attempts at assumes 2–3.
- **The fold_range closure-equality axioms are gone** — earlier versions of the proof had 6 ineliminable closure-equality assumes; these were all removed by the `absorb_rec` rewrite. Don't re-introduce them.

## Related project memories

See `~/.claude/projects/-Users-karthik-libcrux-proofs-cleanup/memory/`:
- `project_sha3_proof_status.md`
- `feedback_fstar_proof_patterns.md`
- `feedback_fstar_factor_modules.md`
- `feedback_fold_range_closure_equality.md`
- `feedback_no_cache_clear.md`
- `feedback_ask_before_killing.md`
