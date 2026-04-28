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

### Above-trait response to F-1 (2026-04-28)

**Verdict: option (d) — stay as-is; restructure the impl-side commute
lemma to match the lane post's existing `==>` shape.**

The lane posts for `decompose`, `compute_hint`, `use_hint` are already
*conditional* on `v input ∈ [0, q)` via the `==>` connective.  The
trait pre's `is_i32b_array_opaque FIELD_MAX (-(q-1) ≤ x ≤ q-1)` is
NOT too weak for these conditional posts — it is too weak only for
the *unconditional* lemma shape that was attempted in
`lemma_use_hint_lane_commute` (`requires v input >= 0 /\ v input < q`,
ensures equation).

Recommended impl-side restructuring:

```fstar
(* OLD (rejected): unconditional lemma with strong precondition *)
let lemma_use_hint_lane_commute (gamma2 input hint res: i32)
  : Lemma (requires v input >= 0 /\ v input < 8380417 /\ ...)
          (ensures v res == v (Hacspec.uuse_hint ...))

(* NEW: lemma whose ensures matches the conditional post *)
let lemma_use_hint_lane_commute (gamma2 input hint res: i32)
  : Lemma (requires <impl-internal post: e.g. v res equals
                     impl-form of use_hint_one>)
          (ensures Libcrux_ml_dsa.Simd.Traits.Specs.use_hint_lane_post
                     gamma2 input hint res)
  = reveal_opaque (`%use_hint_lane_post)
                  (use_hint_lane_post gamma2 input hint res);
    (* Inside the (==>), the impl proof has v input ∈ [0, q) as a
       hypothesis — discharge the equation under that assumption.
       Outside, the implication is trivially true. *)
    introduce v input >= 0 /\ v input < 8380417 /\ ...
              ==> v res == v (Hacspec.uuse_hint ...)
    with hyp.
      <discharge under hyp>
```

The bound conjuncts I added in `94e933eb1` (e.g.
`is_i32b_array_opaque 44 hint_future` for use_hint at γ₂=95232) are
*unconditional* and need impl-side proof for negative inputs too —
the impl handles this via its internal `if r < 0 then r + q` step.
The `_lane_commute` lemma can split into:
1.  An unconditional bound lemma: ∀ input. v hint_future ∈ [0, m).
2.  A conditional equation lemma: input ∈ [0, q) ⇒ equation holds.

**Cross-method scope confirmed:** same restructuring applies to
`decompose` (lane post equation conditional, bound conjuncts I just
added are unconditional) and `compute_hint` (lane post says
`v hint == 0 \/ v hint == 1` *conditionally on v high ∈ [0, q)*; the
pre tightening at `94e933eb1` added FIELD_MAX bound on `low,high` but
not positivity — which is correct, since the conjunct
`is_binary_array_8_opaque hint_future` I added is *unconditional*
and the lane equation stays conditional).

**No trait pre/post change needed.**  The contract at `36fe89b18` is
final for these three methods.

If the impl proof still won't go through under (d), the next escalation
is option (a) — add a positivity tag to the trait pre.  Re-flag
under F-1' if you reach that point with a concrete stuck-query.

(Append future findings above this line, numbered F-2, F-3, ...)
