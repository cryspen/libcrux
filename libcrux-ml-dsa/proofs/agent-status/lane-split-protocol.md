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

#### F-1 (2026-04-28) — `use_hint` trait pre too weak

- **Conjunct that fails to discharge:** the post `use_hint_lane_post`
  is `[0, q)`-conditional on `v input`, but the pre is
  `is_i32b_array_opaque (FIELD_MAX) (f_repr simd_unit)` which gives
  `-(q-1) ≤ v input ≤ q-1`.  An impl-side commute lemma needs
  `v input >= 0`, which isn't there.
- **Recommended fix (above-trait side, pick one):**
  - (a) tighten the trait pre to `is_i32b_array_opaque (q-1)` *and*
    a positivity tag (e.g. dedicated `is_normalised_array_8_opaque`),
    OR
  - (b) declare in the post that whenever input is *not* in `[0, q)`,
    the post is trivially `True` (essentially what
    `use_hint_lane_post` already does — so the impl's job becomes
    just propagating that).  Document the "valid representative"
    convention as an opaque invariant the above-trait callers
    establish via a prior `reduce` / `add_q_if_negative` step.
- **Cross-method scope:** same gap likely affects `decompose` (lane
  post is also `[0, q)`-conditional) and `compute_hint`.  The
  cherry-picked commit `a331580ec` strengthened `compute_hint`'s pre
  with a FIELD_MAX bound on `low,high` but not a positivity tag —
  same issue likely surfaces during `compute_hint` impl close.
- **Below-trait artefact:** `lemma_use_hint_lane_commute` was
  written and verified standalone in
  `Hacspec_ml_dsa.Commute.Chunk.fst`, but reverted because its
  `requires v input >= 0 /\ v input < q` cannot be discharged from
  the trait pre alone.  Recoverable from the git history of branch
  `ml-dsa-proofs` if the pre tightens.

(Append future findings above this line, numbered F-2, F-3, ...)
