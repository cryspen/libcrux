# Above-trait / Below-trait lane split

As of cherry-pick `a331580ec` (mirroring above-trait `94e933eb1`),
verification work is split across two parallel branches that meet at
the `Libcrux_ml_dsa.Simd.Traits.{fsti,fst}` + `…Specs.fst` contract:

| Lane | Worktree | Branch | Verifies |
|---|---|---|---|
| **Above-trait** | `~/libcrux-ml-dsa-above-trait/` | (TBD by other agent) | `Arithmetic`, `Polynomial`, `Matrix`, `Sample`, `Encoding.*` (top-level), `Ml_dsa_generic.*`, `Ntt`, etc. |
| **Below-trait** | `~/libcrux-ml-dsa-proofs/` (this) | `ml-dsa-proofs` | `Simd.Portable.*`, `Simd.Avx2.*`, plus the trait `.fsti` / `.fst` / `Specs.fst` themselves |

Both lanes share the same trait pre/post.  The Makefile in each lane
keeps the *other* lane's modules in `ADMIT_MODULES`.

## Synchronisation protocol

1. **Trait pre/post changes are owned by the above-trait lane.**  This
   branch never edits `src/simd/traits.rs` or `src/simd/traits/specs.rs`
   pre/post conjuncts.  We only edit the impl bodies in
   `src/simd/{portable,avx2,portable/*,avx2/*}.rs` and the commute
   lemmas in `specs/ml-dsa/proofs/fstar/commute/`.
2. **Cherry-pick the trait commit** (taking only `traits.rs`, never the
   above-trait Makefile change) when the above-trait lane updates the
   contract.  Last cherry-pick: `a331580ec` (from `94e933eb1`).
3. **Mismatches must be flagged early** in this file under "Open
   findings" below — not silently fixed by tightening the impl post.
   The above-trait lane will rebase / amend.

## Findings to flag

When this lane discovers that the impl side cannot discharge a trait
post conjunct (or that a trait pre is too weak to drive the panic-free
body), record it here with:
- File / line of the failing conjunct.
- The minimal counter-example or stuck-query stack.
- Recommended fix on the above-trait side (relax post / tighten pre /
  add normalisation step) — but do not apply it; the other agent
  decides.

### Open findings

(none — F-1 and F-2 both resolved 2026-04-28; see "Resolved findings" below)

(Append future findings above this line, numbered F-3, F-4, ...)

### Resolved findings

#### F-1 (2026-04-28) — `use_hint` trait pre too weak — RESOLVED

- **Original gap:** trait pre `is_i32b_array_opaque (FIELD_MAX)` gives
  `-(q-1) ≤ v input ≤ q-1`, but `use_hint_lane_post` is `[0, q)`-conditional
  on `v input`.  Same gap on `decompose` and `compute_hint`.
- **Above-trait verdict (commit `7a4dc28df`, mirrored from this file):**
  option (d) — no contract change.  The lane posts are already
  `==>`-conditional on `v input ∈ [0, q)`; the impl-side commute
  lemmas just need to match that conditional shape.
- **Below-trait obligation (this commit forward):** restructure the
  per-method commute lemmas in `Hacspec_ml_dsa.Commute.Chunk.fst` as
  pairs:
  1. **Unconditional bound lemma** — `∀ input. v out_future ∈ [0, m)`.
     Discharges the new bound conjuncts (e.g.
     `is_i32b_array_opaque 44 hint_future` for `use_hint` at γ₂=95232,
     and `is_i32b_array_opaque (pow2 10) t1_future` for `power2round`)
     from the impl's internal `if r < 0 then r + q` normalize step.
  2. **Conditional equation lemma** — `input ∈ [0, q) ⇒ equation`.
     Matches the lane post's `==>` shape.  Use F\*'s `introduce ... with`
     hypothesis-introduction syntax to produce the implication shape.
- **Affected methods:** `use_hint` (Step 9.7), `decompose` (Step 9.5),
  `compute_hint` (Step 9.8 AVX2 / Portable already lifted).
  `power2round`'s t1 bound is unconditional already — no impl change
  needed there beyond the existing `lemma_power2round_t1_bound` in
  Track A.
- **Trait sha:** `36fe89b18` (above-trait) is final for these methods
  unless a concrete stuck-query reappears under (d), at which point
  re-flag as F-1'.

#### F-2 (2026-04-28) — `decompose` post `v gamma2` cast fails type-check — RESOLVED

- **Original gap:** cherry-picked
  `is_i32b_array_opaque (v $gamma2) low_future` doesn't typecheck
  (`v gamma2 :: int`, not `nat`).  F\* error 19 at
  `Simd.Traits.fst:158,44-54`.
- **Above-trait fix (commit `36fe89b18`):** restate the conjunct as
  the gamma2-conditional combined block (matching the existing
  `high_future` shape):
  ```rust
  ((v $gamma2 == v GAMMA2_V95_232 ==>
      is_i32b_array_opaque 95232 (f_repr ${low}_future) /\
      is_i32b_array_opaque 44 (f_repr ${high}_future)) /\
   (v $gamma2 == v GAMMA2_V261_888 ==>
      is_i32b_array_opaque 261888 (f_repr ${low}_future) /\
      is_i32b_array_opaque 16 (f_repr ${high}_future)))
  ```
- **Below-trait synced (this commit):** Track A's F-2 workaround used
  a logically-equivalent four-case split; resync to the canonical
  combined form to keep `traits.rs` byte-identical between lanes.
  Impl-side `#[ensures]` on both Portable and AVX2 also synced.
- **Status:** closed; no outstanding gap.
