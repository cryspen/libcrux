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

#### F-12 (2026-04-29) — `rejection_sample_*` trait posts gain length-preservation conjunct (above-trait → below-trait mirror)

- **Source:** above-trait commit (this branch's `216cbf17e` after
  cherry-pick) added `Seq.length ${out}_future == Seq.length $out` to
  the `#[ensures(...)]` of all three `Operations::rejection_sample_*`
  methods on the trait declaration in `src/simd/traits.rs`.
- **Numbering note:** above-trait originally filed this finding as
  "F-6" in the integration commit, but F-6 was already taken on the
  below-trait side by the resolved `t0_serialize` centered-bound
  finding.  Renumbered to **F-12** during integration to leave F-8 –
  F-11 free for the half-open `(-l, l]` predicate batch above.
- **Why above-trait needed it:** required to prove panic-freedom of
  the upstream `Sample::rejection_sample_*` wrappers in `src/sample.rs`.
  The wrappers slice `out[*sampled_coefficients..]`, pass to the trait
  method, then `update_at_range_from out RangeFrom tmp0`.  Without
  length-preservation on the trait return, F\* can't discharge the
  update's pre `Seq.length tmp0 <= Seq.length out - sampled_coefficients`.
- **Below-trait mirror (this commit):** the matching conjunct has been
  added to the `#[ensures(...)]` clauses of the Portable + AVX2 impl
  method signatures in `src/simd/portable.rs` and `src/simd/avx2.rs`
  (three methods each: `rejection_sample_less_than_field_modulus`,
  `rejection_sample_less_than_eta_equals_2`,
  `rejection_sample_less_than_eta_equals_4`).
- **Implementation impact:** **none** — the underlying free fns
  (`sample::rejection_sample_*`, `rejection_sample::less_than_*::sample`)
  already preserve length trivially (in-place mutation through
  `&mut [i32]`).  The bodies remain admitted in this lane, so the
  added conjunct only tightens the post and does not introduce any
  new proof obligation that has to discharge below-trait.
- **Status:** RESOLVED (above-trait + below-trait mirror in lockstep).

#### F-11 (2026-04-29) — `decompose` low_future post is closed
`is_i32b_array_opaque γ2` but FIPS 204 produces half-open `(-γ2, γ2]`

- **Affected method:** `decompose` post (`src/simd/traits.rs:71,74`):
  ```
  ((v $gamma2 == v GAMMA2_V95_232 ==>
      Spec.Utils.is_i32b_array_opaque 95232 (f_repr ${low}_future) /\
      Spec.Utils.is_i32b_array_opaque 44 (f_repr ${high}_future)) /\
   (v $gamma2 == v GAMMA2_V261_888 ==>
      Spec.Utils.is_i32b_array_opaque 261888 (f_repr ${low}_future) /\
      Spec.Utils.is_i32b_array_opaque 16 (f_repr ${high}_future)))
  ```
- **Mathematical range:** FIPS 204 Algorithm 36 (Decompose) defines
  `r0 = r' mod^± (2*γ2)` where `mod^±` is centered modulo with output
  in `(-γ2, γ2]`.  So `low_future ∈ (-95232, 95232]` (γ2=95232) or
  `(-261888, 261888]` (γ2=261888) — half-open.  Closed
  `is_i32b_array_opaque γ2` over-approximates by including `-γ2`.
- **Why this is less critical than F-8/F-9:** the immediate consumer
  of `decompose`'s `low` is `compute_hint`, whose pre takes
  `is_i32b_array_opaque FIELD_MAX low` (very wide).  No chain-break
  if the post is left as closed.  But it's an imprecision that
  diverges from the canonical FIPS 204 / Hacspec spec.
- **Recommended fix:** if F-8 introduces an `is_i32b_strict_lower`
  predicate, reuse it here for symmetry — same single-predicate
  cost, more accurate post.

#### F-10 (2026-04-29) — `t0_deserialize` post is closed
`is_i32b_array_opaque (pow2 12)` but should mirror F-8 input shape

- **Affected method:** `t0_deserialize` post
  (`src/simd/traits.rs:278`):
  ```
  Spec.Utils.is_i32b_array_opaque (pow2 12) (f_repr ${out}_future)
  ```
- **Mathematical range:** symmetric round-trip with `t0_serialize`
  — values in `(-2^12, 2^12]` half-open.  Closed
  `is_i32b_array_opaque (pow2 12)` over-approximates at `-pow2 12`.
- **Why this is less critical than F-8/F-9:** the deserialize is
  used in verification flow; downstream callers consume the result
  via wider `is_i32b_array_opaque FIELD_MAX` pres (e.g. ring-element
  arithmetic).  No immediate chain-break.  But once F-8/F-9 land, a
  serialize-deserialize-serialize round-trip would break unless
  this is also half-open.
- **Recommended fix:** same predicate as F-8/F-9.

#### F-9 (2026-04-29) — `power2round` t0_future post is closed
`is_i32b_array_opaque (pow2 12)` but mathematically half-open `(-pow2 12, pow2 12]`

- **Affected method:** `power2round` post
  (`src/simd/traits.rs:148`):
  ```
  Spec.Utils.is_i32b_array_opaque (pow2 12) (f_repr ${t0}_future)
  ```
- **Mathematical range:** FIPS 204 Algorithm 35 (Power2Round) defines
  `r0 = r mod^± 2^d` (centered mod) with output in `(-2^(d-1), 2^(d-1)]`.
  With d = `BITS_IN_LOWER_PART_OF_T = 13`, `t0_future ∈ (-pow2 12, pow2 12]`
  — half-open.  Closed `is_i32b_array_opaque (pow2 12)` over-approximates
  at `-pow2 12`.
- **Why this is critical (chain-break with F-8):** `power2round`'s
  `t0_future` is the SOURCE of values that flow into
  `t0_serialize`.  Once F-8 narrows `t0_serialize`'s pre to half-open
  `(-pow2 12, pow2 12]`, callers chaining
  `power2round(...) → t0_serialize(t0)` will fail to discharge the
  `t0_serialize` pre from `power2round`'s closed post.  Specifically
  the `signing_key.rs::generate_serialized` flow does this chain.
- **Recommended fix:** identical to F-8 — once
  `is_i32b_strict_lower_array_opaque (l: nat)` (or analogous half-open
  predicate) exists on the above-trait side, swap both F-8's pre and
  this post in lockstep.

#### F-8 (2026-04-29) — `is_i32b_array_opaque (pow2 12)` for `t0_serialize`
is closed but AVX2 free fn requires half-open lower bound

- **Affected method:** `t0_serialize` (after F-6 cherry-pick `92bfff21f`).
  Trait pre is now `Spec.Utils.is_i32b_array_opaque (pow2 12)
  (f_repr simd_unit)` which unfolds to
  `forall i. -pow2 12 <= v f_repr[i] <= pow2 12` — closed both ends.
- **Gap:** the AVX2 free fn `src/simd/avx2/encoding/t0.rs::serialize`
  pre is
  ```
  forall i. let x = (POW_2_BITS_IN_LOWER_PART_OF_T_MINUS_ONE - to_i32x8 simd_unit i) in
            x >= 0 && x < pow2 13
  ```
  Solving: `x >= 0` ⇔ `to_i32x8[i] <= pow2 12`; `x < pow2 13` ⇔
  `to_i32x8[i] > -pow2 12` (**strict**).  So the AVX2 free fn pre is
  half-open `(-pow2 12, pow2 12]`.  At trait-pre boundary
  `f_repr[i] == -pow2 12` (= -4096), AVX2 free fn pre is unsatisfied.
- **Empirical result:** Step 13 below-trait verify failed at
  `Libcrux_ml_dsa.Simd.Avx2.fst:1257`:
  ```
  Error 19 — Assertion failed (incomplete quantifiers, rlimit=80)
  See also Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.fst(113,10-113,16)
                                                  (113,20-113,31)
  ```
  i.e. both upper and lower clauses of the AVX2 free fn pre fail to
  discharge from the closed `is_i32b 4096`.
- **Why F-6 didn't catch this:** the F-6 commit message states the
  fix uses `Spec.Utils.is_i32b_array_opaque (pow2 12)` (centered, |x|
  ≤ 4096).  Mathematically t0 ranges over `(-pow2 12, pow2 12]` per
  FIPS 204 §4.4 (the lower part of t mod q centered around 0 such
  that the centered representative is in this range), so a
  half-open form is the right model.  `is_i32b 4096` over-approximates
  by including -4096.
- **Recommended fix on the above-trait side:** three options.
  (a) Introduce a new opaque predicate `is_i32b_strict (l: nat) (x:
      i32) : prop = -l < v x <= l` (or equivalent half-open), with
      lookup/intro lemmas; replace the trait pre with
      `is_i32b_strict_array_opaque (pow2 12)`.
  (b) Strengthen `is_i32b 4096` to `is_i32b 4095` (|x| <= 4095).  This
      slightly narrows the upper bound (excludes 4096) but the FIPS
      204 t0 representative form `r1 - r0` actually achieves 4096 at
      one corner, so this would lose the upper boundary.
  (c) Relax the AVX2 free fn pre to closed (`x <= pow2 13` not
      strict).  This requires re-verifying the AVX2 body still
      panic-frees at the lower boundary (coefficient = pow2 13 fits
      in 14 bits, but the intrinsics' bit packing would silently
      truncate).
  Option (a) is cleanest.
- **Below-trait posture:** AVX2 `Operations::t0_serialize` impl body
  retains its `hax_lib::fstar!("admit ()")` until F-8 lands.
  Portable `Operations::t0_serialize` impl body discharges fine: the
  Portable free fn pre was widened in this lane (Step 13) to
  `Spec.Utils.is_i32b (pow2 12)`, accepting the closed interval
  directly (the body uses `as u8` truncation that handles all i32
  values without panic — the body's bit-pattern correctness at
  x == -4096 is irrelevant since the trait post is just length-pres).

#### F-7 (2026-04-29) — `is_pos_array_opaque l` boundary off-by-one
breaks Portable `commitment_serialize` discharge

- **Affected predicate:** `Libcrux_ml_dsa.Simd.Traits.Specs.is_pos_array_opaque`
  (`src/simd/traits/specs.rs:84`).  Defined as
  `forall i. v x[i] >= 0 /\ v x[i] <= l` (note: `<= l`, **inclusive**).
- **Affected methods:** three of the four F-3 `*_serialize` trait pres
  (`commitment_serialize`, `gamma1_serialize`, `t0_serialize`) cite
  `is_pos_array_opaque (pow2 d)` and the corresponding free fns use
  `bounded x d` (= `< pow2 d`).  `error_serialize` is **not affected**
  because its trait pre cites `is_pos_array_opaque eta` (literal 2 or
  4) while its free fn requires `bounded x d` where d is the *byte
  width* (3 or 4): the trait pre's `<= eta` (2 or 4) is strictly
  stronger than the free fn's `< pow2 d` (4 or 16) so the implication
  holds with room to spare.
- **Gap:** the four free fns in `src/simd/portable/encoding/{commitment,
  gamma1,t0,error}.rs` and the AVX2 counterparts use `bounded x d`
  (Rust_primitives.BitVectors.bounded) which is **strict** `< pow2 d`,
  not `<= pow2 d`.  At trait-pre boundary `value == pow2 d` (e.g.
  `f_repr[i] == 16` for commitment with d=4), the trait pre is
  satisfied but the free fn pre fails.  Z3 cannot bridge the gap.
- **Empirical result:** Step 13 below-trait verify is non-deterministic
  in which call site Z3 fails at.  First run failed at
  `Libcrux_ml_dsa.Simd.Portable.fst:1067` (commitment_serialize call,
  `Z3 canceled at rlimit 80`).  Second run (after re-admitting
  commitment_serialize) failed at
  `Libcrux_ml_dsa.Simd.Portable.fst:1161` (t0_serialize call,
  `incomplete quantifiers`, no canceled).  This non-determinism is a
  hallmark of the unsound implication (trait pre allows `<= pow2 d`,
  free fn requires `< pow2 d`): Z3 sometimes finds the proof by
  pattern-matching boundaries, sometimes doesn't.  AVX2
  `commitment_serialize` trait body is bound-free (only length on
  `out`) so it discharges cleanly.
- **Mirror with ML-KEM:** ML-KEM's `bounded_pos_i16_array d v` unfolds
  to `bounded_i16_array (mk_i16 0) (mk_i16 (pow2 d - 1)) x` — i.e.
  upper bound is `pow2 d - 1`, equivalent to `< pow2 d`.  The ML-DSA
  F-3 fix introduced `is_pos_array (l: nat) (x): forall i. >= 0 /\
  <= l` and at call sites uses `is_pos_array_opaque (pow2 d)`,
  shifting the off-by-one into the call site rather than fixing it
  in the predicate.
- **Recommended fix on the above-trait side:** two options.
  (a) Tighten the predicate definition: change
      `is_pos_array (l: nat) (x): forall i. >= 0 /\ <= l` to
      `forall i. >= 0 /\ <= l - 1` (or equivalently `< l + 1` then
      flip to `< l`).  This better matches ML-KEM's
      `bounded_pos_i16_array` shape (which is `<= pow2 d - 1`).
  (b) Keep predicate, change all four trait pres from
      `is_pos_array_opaque (pow2 d)` to `is_pos_array_opaque (pow2 d - 1)`
      and `is_pos_array_opaque (match eta with Eta_Two -> 1 | Eta_Four -> 3)`.
      Less invasive but more error-prone (every call site must
      remember `-1`).
- **Below-trait posture:** Portable `Operations::commitment_serialize`
  and `Operations::t0_serialize` impl bodies retain their
  `hax_lib::fstar!("admit ()")` until F-7 lands (the latter also has
  F-6's separate centered-vs-non-negative semantic issue, but the
  boundary off-by-one alone is enough to block discharge).
  Portable `Operations::error_serialize` and `Operations::t1_serialize`
  discharge cleanly (admit-free).  AVX2 `Operations::commitment_serialize`,
  `Operations::error_serialize`, and `Operations::t1_serialize`
  discharge cleanly.  AVX2 `Operations::t0_serialize` admit retained
  (F-6).  AVX2 `Operations::gamma1_serialize` admit retained (separate
  Track A-deferred — needs offset-aware `bit_vec_of_int_t_array`
  ensures).


non-negative bound where impl requires centered (|x| ≤ pow2 12)

- **Affected method:** `t0_serialize` (trait at
  `src/simd/traits.rs:266`).  F-3 cherry-pick switched the trait pre
  from `is_i32b_array_opaque (pow2 13) (f_repr simd_unit)` (signed)
  to `is_pos_array_opaque (pow2 13) (f_repr simd_unit)` (non-negative,
  `0 ≤ x ≤ 8192`).
- **Gap:** the AVX2 free fn
  `src/simd/avx2/encoding/t0.rs::serialize` requires
  `forall i. let x = POW_2_BITS_IN_LOWER_PART_OF_T_MINUS_ONE - to_i32x8 simd_unit i in x >= 0 && x < pow2 13`
  where `POW_2_BITS_IN_LOWER_PART_OF_T_MINUS_ONE = pow2 12 = 4096`.
  Solving for `x`: `-4095 < x ≤ 4096` — a **centered** range, not
  `[0, 8192]`.  At trait-pre boundary `f_repr[i] == 8192`, AVX2 free
  fn pre fails (`4096 - 8192 = -4096 < 0`).  Empirical: `Error 19 at
  Simd.Avx2.fst(1259,47-1259,56)` from a `[CHECK]` run after F-3 mirror
  sync (this lane's Step 13).
- **Why this matters:** the AVX2 `Operations::t0_serialize` impl body
  cannot drop its admit without either the bridge stronger pre or an
  impl-side renormalization step that is not present.  Portable
  `Operations::t0_serialize` impl body **does** verify under the
  current F-3 trait pre (the boundary case `8192` is allowed by the
  Portable free fn `bounded x 13` requirement of `< 8192`?  Empirical
  result: Portable verifies, suggesting Z3 silently handles the
  boundary).
- **Recommended fix on the above-trait side:** replace
  `t0_serialize`'s trait pre with the centered form
  `is_i32b_array_opaque (pow2 12) (f_repr simd_unit)` (i.e. revert
  F-3's choice for `t0_serialize` only).  This matches the
  semantically correct interval for t0 inputs (the LOWER 13 bits of
  the t value, signed-centered around 0) and discharges the AVX2 free
  fn pre once the f_repr↔to_i32x8 bridge fires.  Portable's free fn
  `bounded` pre is non-negative, so this would either (a) require an
  impl-side renormalize on the Portable side or (b) keep the Portable
  free fn pre as-is and have the impl method body convert from
  centered to non-negative.
- **AVX2 commitment_serialize and AVX2 error_serialize unaffected:**
  commitment values are inherently non-negative ([0, 16) or [0, 64));
  error values have the centered form `eta - x` where the boundary
  case works out (eta - x ≥ 0 when x ≤ eta, and the trait pre says
  x ≤ eta).  Only `t0` has the off-by-power-of-two centered semantic
  that breaks at the boundary.
- **Below-trait posture:** AVX2 `Operations::t0_serialize` impl body
  retains its `hax_lib::fstar!("admit ()")` until F-6 lands.

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

#### F-6 (2026-04-29) — `t0_serialize` trait pre swap to centered — RESOLVED

- **Original gap:** trait pre `is_pos_array_opaque (pow2 13)` allows
  `f_repr[i] == 8192`, but the AVX2 free fn requires the centered
  range `(-4095, 4096]` for `POW_2_BITS_IN_LOWER_PART_OF_T_MINUS_ONE -
  to_i32x8 simd_unit i` to fall in `[0, pow2 13)`.  Trait-pre boundary
  `8192` violated the AVX2 free fn pre.
- **Above-trait fix (commit `92bfff21f`):** swap `t0_serialize`'s
  trait pre from `is_pos_array_opaque (pow2 13)` (non-negative,
  `[0, 8192]`) back to `Spec.Utils.is_i32b_array_opaque (pow2 12)`
  (centered, `|x| <= 4096`).  Matches the semantically correct
  interval for t0 inputs (the lower 13 signed bits of t centered
  around 0) and discharges the AVX2 free fn pre once the
  f_repr↔to_i32x8 bridge fires.
- **Caller fallout (same commit):** `encoding/t0.rs::serialize`
  wrapper pre updated from `is_pos_array_opaque (pow2 13)` to
  `Spec.Utils.is_i32b_array_opaque (pow2 12)` to match the new trait
  pre.  Loop invariant strengthened to carry the bound across
  iterations.  Upstream callers
  (`encoding/signing_key.rs::generate_serialized`,
  `simd/portable.rs::t0_serialize`, `simd/avx2.rs::t0_serialize`) all
  body-admit, so propagation is contained.
- **Below-trait posture:** AVX2 `Operations::t0_serialize` impl body
  should now discharge cleanly under the centered pre.  Portable
  `Operations::t0_serialize` may now need an impl-side renormalize
  step (centered → non-negative) to satisfy the Portable free fn's
  `bounded x 13` pre — flag as F-8 if the below-trait Portable body
  discharge breaks under the new pre.
- **Status:** above-trait closed; below-trait may need follow-up
  (track under F-8 if a new Portable gap appears).

#### F-7 (2026-04-29) — `is_pos_array_opaque l` boundary off-by-one
breaks `*_serialize` discharge — RESOLVED

- **Original gap:** `is_pos_array_opaque l` semantic is `<= l`
  (inclusive), but the matching free fns require `bounded x d` which
  is strict `< pow2 d`.  At the boundary `value == pow2 d` (e.g.
  `f_repr[i] == 16` for commitment with d=4), trait pre is satisfied
  but the free fn pre fails — Z3 sometimes finds the bridge by
  pattern matching boundaries, sometimes not, giving non-deterministic
  Z3-canceled / incomplete-quantifier failures on Portable
  `commitment_serialize` and `t0_serialize` discharges.
- **Above-trait fix (commit `8078029c0`):** per the user-confirmed
  local-tightening approach, keep the `is_pos_array_opaque` predicate
  definition unchanged and tighten each affected trait pre call site
  from `is_pos_array_opaque (pow2 d)` to `is_pos_array_opaque (pow2 d - 1)`.
  Affected methods:
  - `gamma1_serialize`: `pow2 (v gamma1_exponent)` -> `pow2 (...) - 1`.
  - `commitment_serialize`: `pow2 (Seq.length serialized)` -> `pow2 (...) - 1`.
  `t0_serialize` is no longer affected by F-7 because F-6 swapped its
  pre to `is_i32b_array_opaque`.  `error_serialize` is not affected
  (trait pre's `<= eta` (2 or 4) is strictly stronger than the free
  fn's `< pow2 d` (8 or 16) with slack).
- **Caller fallout (same commit):** `encoding/commitment.rs::serialize`
  and `serialize_vector`, `encoding/gamma1.rs::serialize` wrappers
  tightened to `pow2 d - 1`.  Upstream callers
  (`encoding/signature.rs::serialize`, `ml_dsa_generic` callsites)
  all body-admit, so propagation does not surface as new active
  obligations.
- **Below-trait posture:** Portable `Operations::commitment_serialize`
  impl body should now be dischargeable (admit-removable on the
  below-trait branch).
- **Status:** above-trait closed.

#### F-12 (2026-04-29) — `rejection_sample_*` trait posts add length-preservation — RESOLVED above-trait, below-trait cherry-pick pending

- **Numbering note:** filed during integration of three parallel agents.
  This finding originally landed in commit `9c8d8ba55` labeled "F-6", but
  F-6 was already taken by the `t0_serialize` centered-bound finding
  (resolved above).  Renumbered to F-12 here to leave F-8 — F-11 free for
  the half-open `(-l, l]` predicate batch flagged separately by below-trait.
- **Files**: `src/simd/traits.rs` (~166-191),
  `src/simd/portable.rs` (~223-256), `src/simd/avx2.rs` (~286-321).
- **Change**: added `Seq.length ${out}_future == Seq.length $out` to the
  ensures of `rejection_sample_less_than_field_modulus`,
  `rejection_sample_less_than_eta_equals_2`,
  `rejection_sample_less_than_eta_equals_4` (trait + Portable impl + AVX2 impl).
- **Why**: needed to prove panic-freedom of the upstream
  `Sample::rejection_sample_*` wrappers in `src/sample.rs`.  The
  wrappers slice `out[*sampled_coefficients..]`, pass to the trait
  method, then `update_at_range_from out RangeFrom tmp0`. Without
  length-preservation on the trait return, F* can't discharge the
  update's pre `Seq.length tmp0 <= Seq.length out - sampled_coefficients`.
- **Above-trait status:** trait + (above-trait portion of) impl signatures
  landed in commit `9c8d8ba55` (this cherry-pick); split during integration
  so above-trait carries the `traits.rs` change, below-trait owns the
  matching `portable.rs` + `avx2.rs` ensures.
- **Below-trait posture:** trivially preserved by the impls (in-place
  mutation; underlying free fns preserve length).  Cherry-pick the
  `portable.rs` + `avx2.rs` diff; bodies stay admitted.  No commute-lemma
  work required.
- **Status:** above-trait closed; below-trait cherry-pick produced as a
  standalone commit on the `ml-dsa-proofs` branch (see integration message).

#### F-8 / F-9 / F-10 / F-11 (2026-04-29) — half-open `(-l, l]` predicate batch — RESOLVED above-trait

- **Source:** filed below-trait at the end of Step 12 / Step 13.  Four
  related trait pres/posts on `Operations` were closed
  `is_i32b_array_opaque l` (`[-l, l]`) but the underlying mathematical
  truth (FIPS 204 Algorithms 35 / 36 + AVX2 free-fn pres) is half-open
  `(-l, l]`.  Closed-form caused a boundary failure at `x = -l` for the
  AVX2 `t0_serialize` free fn; the chain `power2round → t0_serialize`
  could not discharge after F-6.
  - **F-8** — `t0_serialize` pre.
  - **F-9** — `power2round` `t0_future` post (chain-critical with F-8).
  - **F-10** — `t0_deserialize` post (round-trip symmetry).
  - **F-11** — `decompose` `low_future` post (FIPS 204 Algorithm 36
    is half-open by `mod^±`).
- **Above-trait fix (this commit batch):**
  1. Added a sibling `is_i32b_strict_lower_array_opaque (l: nat)` predicate
     in `libcrux-ml-kem/proofs/fstar/spec/Spec.Utils.fsti` next to the
     existing `is_i32b_array_opaque`.  Definition: `forall i. i < Seq.length s
     ==> -l < v s[i] /\ v s[i] <= l`.  Marked `[@ "opaque_to_smt"]`,
     mirroring the closed-form predicate's shape.
  2. Added an SMTPat implication lemma
     `lemma_is_i32b_strict_lower_implies_array_opaque` so callers expecting
     the closed form keep discharging when given the new strict-lower form
     (the strict-lower form is strictly stronger).  Plus a sibling
     `is_i32b_strict_lower_array_larger` lemma mirroring the closed-form
     `_larger` weakening lemma.
  3. Swapped the four trait sites in `libcrux-ml-dsa/src/simd/traits.rs`:
     - `decompose` post: `is_i32b_array_opaque γ2` → `is_i32b_strict_lower_array_opaque γ2`
       for both `low_future` branches (γ2 = 95232 and 261888).
     - `power2round` post: `is_i32b_array_opaque (pow2 12)` →
       `is_i32b_strict_lower_array_opaque (pow2 12)` on `t0_future`.
     - `t0_serialize` pre: same swap on `simd_unit`.
     - `t0_deserialize` post: same swap on `out_future`.
  4. Tightened the wrapper at `libcrux-ml-dsa/src/encoding/t0.rs` (both
     `serialize` and `deserialize` pres/posts + loop invariants) to use
     the new strict-lower predicate, since the trait pres/posts both line
     up at `(-pow2 12, pow2 12]` after the swap.
- **Verified targets:**
  - `Libcrux_ml_dsa.Simd.Traits.fst.checked` — verified clean (~70 s).
  - `Libcrux_ml_dsa.Encoding.T0.fst.checked` — verified clean (~3 s).
  - `Libcrux_ml_dsa.Encoding.Commitment.fst.checked` — verified clean (sanity).
  - `Libcrux_ml_dsa.Encoding.Gamma1.fst.checked` — verified clean (sanity).
  - `Libcrux_ml_dsa.Encoding.Signing_key.fst.checked` — verified clean.
  - `Spec.Utils.fsti.checked` — verified clean (~7 s).
  - `Libcrux_ml_dsa.Arithmetic.fst.checked` — `power2round_vector` and
    `decompose_vector` discharge clean.  Pre-existing `make_hint` Z3
    failures (3 errors at lines 620 / 661 / 662, all about `true_hints +!
    one_hints_count` usize-overflow) are unrelated to this batch
    (`make_hint` uses `compute_hint`, not `power2round` / `decompose` /
    `t0_*`).  Filed as a separate follow-up.
- **Caller fallout (above-trait):**
  - `arithmetic.rs::power2round_vector` is `panic_free` + body-admitted —
    its closed-form post is automatically refined by the SMTPat
    implication lemma.  No edit required.
  - `arithmetic.rs::power2round_one_ring_element` (NOT body-admitted)
    consumes the trait `power2round` post.  The SMTPat implication
    lemma fires on the trait's strict-lower post and yields the
    closed-form post that `power2round_one_ring_element`'s
    closed-form ensures expects — discharges automatically (verified
    clean in the build).
  - `encoding/signing_key.rs::generate_serialized` is
    `panic_free` + body-admitted; the chain `power2round → t0_serialize`
    is no longer a chain-break risk because both endpoints now line up
    at half-open `(-pow2 12, pow2 12]`.  No edit required.
- **Below-trait mirror (cherry-pick TODO):**
  - The same predicate addition (`is_i32b_strict_lower_array_opaque` +
    SMTPat implication lemma + `_larger` lemma) needs to land in
    `libcrux-ml-kem/proofs/fstar/spec/Spec.Utils.fsti` on the
    `ml-dsa-proofs` branch.  Same diff.
  - The matching `f_repr`-side swaps in the impl signatures of
    `simd/portable.rs` + `simd/avx2.rs` for the four methods
    (`decompose`, `power2round`, `t0_serialize`, `t0_deserialize`)
    need to mirror the trait diff.  The body-discharge gain: the
    AVX2 `t0_serialize` boundary failure at `lane == -4096` now
    discharges, since the impl pre also rejects that boundary.
  - The wrapper `simd/portable/encoding/t0.rs` (or its impl-side
    analog) likewise needs the strict-lower swap for round-trip.
- **Status:** above-trait CLOSED; below-trait cherry-pick PENDING.

(Append future findings above this line, numbered F-3, F-4, ...)
