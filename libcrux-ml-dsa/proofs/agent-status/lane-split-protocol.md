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

#### F-3 (2026-04-28) — encoding `*_serialize` trait pres use signed
bound where free fns require non-negative

- **Affected methods:** `commitment_serialize`, `gamma1_serialize`,
  `t0_serialize`, `error_serialize` — all four trait pres carry
  `Spec.Utils.is_i32b_array_opaque (pow2 d) (f_repr simd_unit)` (or a
  variant), which is the **signed**-bound predicate
  `forall i. -pow2 d ≤ v values[i] ≤ pow2 d`.
- **Gap:** the Portable free fns
  (`src/simd/portable/encoding/commitment.rs::serialize`,
  `error.rs::serialize`, `t0.rs::serialize`, `gamma1.rs::serialize`)
  each require `forall i. bounded values[i] d`, where
  `Rust_primitives.BitVectors.bounded x d` is defined as
  `v x >= 0 /\ v x < pow2 d` — the **non-negative** range
  `[0, pow2 d)`.  The trait pre allows e.g. `values[i] = -1`, which
  violates the free fn pre.
- **Why this matters:** the Portable trait method body
  (`src/simd/portable.rs:569` for commitment, similar lines for the
  others) currently `admit ()`s past this gap.  The free fn's pre
  `bounded` is required because the body's `as u8` cast on a negative
  value followed by `coefficient << 4 | other` would overflow at
  runtime (debug panic) when `coefficient ≥ pow2 d`.
- **Note about specs.rs comment:** `src/simd/traits/specs.rs:64-69`
  asserts that "is_i32b_array_opaque (pow2 d) is the same opaque form
  as ML-KEM's bounded_pos_i16_array d v.  No new predicate needed."
  This is **incorrect**: ML-KEM's `bounded_pos_i16_array d v` (in
  `libcrux-ml-kem/src/vector/traits.rs:109`) unfolds to
  `bounded_i16_array (mk_i16 0) (mk_i16 (pow2 d - 1)) x`, which is
  **non-negative** `[0, pow2 d)`.  The ML-DSA `is_i32b_array_opaque`
  is **signed** `[-pow2 d, pow2 d]`.  These differ by sign convention.
- **Recommended fix on the above-trait side:** for each
  `*_serialize` method, replace the trait pre's signed bound with a
  non-negative variant.  Two options:
  (a) introduce a new opaque predicate `is_pos_array_opaque (l: nat)
      (x: t_Slice i32)` mirroring `bounded_pos_i16_array`'s shape,
      with intro/lookup SMTPats; replace `is_i32b_array_opaque (pow2 d)`
      with `is_pos_array_opaque (pow2 d)` in the four pres.
  (b) keep `is_i32b_array_opaque` but add a `forall i. v values[i] >= 0`
      conjunct (plus opacity intro/lookup updates).
- **AVX2 unaffected:** the AVX2 encoding free fns (e.g.
  `src/simd/avx2/encoding/commitment.rs::serialize`) require only
  length on `out`, no bound on the input lanes.  Track 0c
  (commit `87a71ccc4`) closed AVX2 `commitment_serialize` cleanly;
  Portable cannot be closed until F-3 lands.

#### F-4 (2026-04-28) — `compute_hint_lane_post` inconsistent at
`low = -gamma2, high != 0` boundary

- **Affected predicate:** `Libcrux_ml_dsa.Simd.Traits.Specs.compute_hint_lane_post`
  (`src/simd/traits/specs.rs:137-142`) — claims, under `v high ∈ [0, q)`,
  the impl-side hint bit equals `Hacspec_ml_dsa.Arithmetic.make_hint low high gamma2`.
- **Gap:** the impl actually computes
  `Spec.MLDSA.Math.compute_one_hint (v low) (v high) (v gamma2)`
  (Portable `arithmetic::compute_one_hint` body returns
  `(low > g) || (low < -g) || (low = -g && high != 0)` per FIPS 204
  optimized form).  This does **not** equal Hacspec's `make_hint` for
  all `low ∈ i32`.  Concrete counter-example with `gamma2 = 95232`,
  `high = 1` (in `[0, q)`), `low = -gamma2 = -95232`:
  - Spec: `low = -g && high != 0` → returns `1`.
  - Hacspec: `r1 = high_bits 1 g = 0`; mod_q-sum `= mod_q (1 + (-g)) = 8285186`;
    `high_bits 8285186 g`: decompose hits special case
    (`r_q - r_g = q-1`), so `r1 = 0`.  `make_hint = (0 ≠ 0) = false`.
  - Spec returns 1, Hacspec returns false → trait post claims they're
    equal, contradiction.
- **Root cause:** the Spec `compute_one_hint` is the FIPS 204 ML-DSA
  signing-flow optimized form (which intentionally diverges from raw
  MakeHint at the boundary to mark certain hint bits for the
  protocol's correctness guarantees).  Hacspec `make_hint` is the
  literal FIPS 204 algorithm definition.  The two are NOT equal at
  `low = -g, high ≠ 0`.
- **Why this matters:** the `lemma_compute_hint_lane_commute_conditional`
  body (`Hacspec_ml_dsa.Commute.Chunk.fst:573-599`) currently `admit ()`s
  the `==>`-branch of `compute_hint_lane_post`.  No real proof exists
  because the equivalence is FALSE at the boundary.
- **Recommended fix on the above-trait side:** replace
  `compute_hint_lane_post`'s `make_hint`-citing right-hand side with a
  citation that matches the implementation.  Two options:
  (a) cite `Spec.MLDSA.Math.compute_one_hint` directly (mirroring
      the impl-side call), losing the cross-spec connection to FIPS 204
      `MakeHint`.
  (b) introduce a Hacspec-side helper `compute_one_hint_optimized`
      that exactly mirrors the Spec form (or strengthen `make_hint`
      to add the boundary marker) — then the existing post can cite
      that instead.
- **Note:** `use_hint`'s analogous `lemma_use_hint_lane_commute_conditional`
  (closed in F-1 Track 1) does NOT have this gap because Hacspec's
  `uuse_hint` already operates on `(r1, r0)` from `decompose` directly,
  matching the Spec's bucket-arithmetic exactly.

#### F-5 (2026-04-28) — `reduce_lane_post` cannot be tightened to
FIELD_MID without an extra correction step in the impl

- **Above-trait request:** tighten `reduce_lane_post` in
  `src/simd/traits/specs.rs:88` from
  `is_i32b 8380416 result` (FIELD_MAX, |x| ≤ q-1) to
  `is_i32b 4190208 result` (FIELD_MID, |x| ≤ q/2) so the
  `reduce → ntt` chain composes (ntt's pre is `NTT_BASE_BOUND = FIELD_MID`).
- **Empirical result:** below-trait verified — change does not hold.
  F* error at `specs/ml-dsa/proofs/fstar/commute/Hacspec_ml_dsa.Commute.Chunk.fst:29`
  (`lemma_reduce_lane_commute`).  Z3 reports `incomplete quantifiers`
  on the tightened conclusion, hint-cached prior body fails.
- **Root cause:** the centered Barrett reduction
  `quotient = (fe + 2^22) >> 23; result = fe - quotient * q`
  used by both `src/simd/portable/arithmetic.rs::reduce_element` and
  `src/simd/avx2/arithmetic.rs::reduce` produces output in
  `(-2^22, 2^22] = (-4194304, 4194304]`, **NOT** `(-q/2, q/2)`.
  The discrepancy is ~4096 above q/2.  Concretely, for `fe = 2^22 - 1
  = 4194303` (a valid input under the trait's
  `is_i32b_array_opaque 2143289343` pre):
    - quotient = (4194303 + 4194304) >> 23 = 8388607 >> 23 = 0 (since
      8388607 < 2^23 = 8388608).
    - result = 4194303 - 0 = 4194303.
    - |result| = 4194303 > 4190208 = q/2.  Violates the tightened bound.
- **Recommended fix on the above-trait side / impl side:** to make
  the chain `reduce → ntt` actually compose, an impl-side change is
  needed.  Two options:
  (a) Add a final centered correction to `reduce_element` (and the
      AVX2 SIMD analog):
      ```rust
      let result = fe - quotient * FIELD_MODULUS;
      // Centered correction: bring result into (-q/2, q/2)
      let mask_pos = if result > FIELD_MODULUS / 2 { FIELD_MODULUS } else { 0 };
      let mask_neg = if result < -(FIELD_MODULUS / 2) { -FIELD_MODULUS } else { 0 };
      result - mask_pos - mask_neg
      ```
      Then the post `is_i32b (q/2 - 1)` (or `is_i32b q/2` if boundary
      is OK) is provable.  Behavior change: existing tests that
      observe the Barrett residue would see different (canonical-
      centered) values.
  (b) Use a tighter constant `is_i32b 4194303` (= `2^22 - 1`).  This
      is provable from the existing impl (since the Barrett output is
      strictly in `(-2^22, 2^22)` for typical inputs, with the open
      bound from the impl's rounding).  Then NTT_BASE_BOUND (and
      ntt's pre) would also need updating to 4194303.  Slightly looser
      than q/2 but no impl change.
- **Decision needed:** whether (a) or (b).  Option (a) preserves the
  cleaner FIELD_MID = q/2 constant at the cost of impl change + test
  diff; option (b) keeps the impl as-is at the cost of a slightly
  looser bound (4194303 vs 4190208).

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
