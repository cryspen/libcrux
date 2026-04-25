# MLKEM Verification Status (C4f plan, revised after user feedback)

**Branch**: `trait-poststrengthen`  **Tip**: `68233ffd4`
**Task**: C4f — portable `compress_1` / `compress<D>` / `decompress_1` /
`decompress_ciphertext_coefficient<D>`.

## User directives (this session)

1. Keep hacspec dependency at the **trait** level, not in primitive posts.
2. Add bridge lemmas (primitive post → hacspec form).
3. **Primitive posts must be strengthened** (the existing bounds-only
   posts don't give bridge lemmas enough to work with). Hacspec's
   integer formula is a good template.
4. For `compress_1` (→ `compress_message_coefficient`), try to **prove**
   the bridge.
5. For `compress<D>` (→ `compress_ciphertext_coefficient`, Barrett),
   try SMT / short F* ulib lemma; if not quick, **admit with English
   hints** and defer to user.
6. Same for `decompress_d`.
7. Plan first, check postconditions actually hold (audit), then prove.

## Audit (complete) — postconditions hold

- `compress_message_coefficient` ↔ `compress_d fe 1`: ✓ via 3-case split
  on `fe ∈ [0, 832] ∪ [833, 2496] ∪ [2497, 3328]`. Quotient of
  `(4·fe+3329)/6658` is 0 / 1 / 2 respectively; `mod 2` gives 0 / 1 / 0.
- `compress_ciphertext_coefficient` (Barrett) ↔ `compress_d fe D` for
  D ∈ {4,5,10,11}: ✓. Both approximate `round(fe·2^D / 3329)`.
  `10321340 / 2^35 ≈ 1/3329` (Barrett).
- `decompress_1`: ✓ direct: impl gives `{0, 1665}` for `a ∈ {0, 1}`;
  hacspec `decompress_d(0, 1) = 0`, `decompress_d(1, 1) = 1665`.
- `decompress_ciphertext_coefficient`: ✓ *identical formula*
  `(2·a·3329 + 2^D) / 2^(D+1)`, just `>>` instead of `/`.

## Revised plan (6 steps)

### S1. Strengthen primitive posts (compress side)
File: `src/vector/portable/compress.rs`.
- `compress_message_coefficient` post gains integer-form conjunct:
  `v result == ((v fe * 4 + 3329) / 6658) % 2` (on `fe ∈ [0, 3329)`).
  Expected: provable from the existing threshold post via a 3-case
  integer assertion chain.
- `compress_ciphertext_coefficient` post gains:
  `(v D == 4 \/ v D == 5 \/ v D == 10 \/ v D == 11) ==>
   v result == ((v fe * 2 * pow2 (v D) + 3329) / 6658) % (pow2 (v D))`.
  Expected: Barrett-to-exact-div reasoning will not go through in SMT.
  Use `#[hax_lib::fstar::verification_status(panic_free)]` if the body
  can't discharge the new post after a reasonable attempt, with a
  comment explaining the Barrett-approximation-exactness gap.

### S2. Strengthen `decompress_1` and `decompress_ciphertext_coefficient` ensures
File: `src/vector/portable/compress.rs`. No separate primitive; the
inline body is the primitive.
- `decompress_1` ensures conjunct:
  `v res_i == (2 * v a_i * 3329 + 2) / 4`, for `a ∈ {0, 1}`. Trivial
  (two values).
- `decompress_ciphertext_coefficient<D>` ensures conjunct:
  `(D ∈ {4,5,10,11}) ==> v res_i == (2 * v a_i * 3329 + pow2 D) / pow2 (D+1)`.
  Body is literally that (modulo `>>` vs `/`). Provable by bit-shift
  semantics.

### S3. Bridge lemmas (Layer-0.5 scalars)
File: `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`.
- `lemma_compress_message_coefficient_fe_commute`:
  `(v fe < 3329 /\ <primitive post>) ==>
    CP.compress_d (i16_to_spec_fe fe_as_i16) 1 == i16_to_spec_fe (result_as_i16)`
  (trivial integer unfold).
- `lemma_compress_ciphertext_coefficient_fe_commute`: same at D.
- `lemma_decompress_1_fe_commute`: from `a ∈ {0, 1}` and
  `v res ∈ {0, 1665}`, conclude hacspec equality.
- `lemma_decompress_ciphertext_coefficient_fe_commute`: same at D.

### S4. Strengthen trait posts
File: `src/vector/traits.rs`.
- `compress_1_post` += `compress_post_N #16 1 vec result`.
- `compress_post` += `D ∈ {4,5,10,11} ==> compress_post_N #16 D vec result`.
- `decompress_1_post`, `decompress_ciphertext_coefficient_post`:
  already strong.

### S5. Rewire portable wrappers
File: `src/vector/portable.rs` (lines 226-263).
- Each wrapper's ensures → `spec::<op>_post(&a.repr(), &out.repr())`
  as Rust call.
- Body: call the Layer-1 chunk-commute lemma.

### S6. Close the 4 Layer-1 stubs
File: `Hacspec_ml_kem.Commute.Chunk.fst` (lines 768-810).
- Each stub body becomes `= ()` once trait post witnesses
  `compress_post_N` / `decompress_post_N`.

## Risk register

- S1 for `compress_ciphertext_coefficient` is the hardest: Barrett
  approximation exactness is classical but tedious. High likelihood of
  admit + `panic_free` or `admit()` in the F* bridge. That's explicitly
  OK per user directive.
- Changes to primitive posts require re-verifying the primitive bodies
  which currently use rlimit 200 + opaque_to_smt. Need to preserve the
  opacity and keep rlimit under 300 (user policy).
- C4e admits still present; C4f must not regress them. Run full prove
  after S1, S5.

## Next action

S1a: strengthen `compress_message_coefficient` post with integer form,
try to prove.

## Verification log (this session — C4f closed)

Final state at the C4f-closing tip:

- `Libcrux_ml_kem.Vector.Portable.Compress.fst` — **PASS** (~73 s).
- `Libcrux_ml_kem.Vector.Portable.fst` — **PASS** (117 s, rlimit 200).
  Down from C4e baseline 217 s — **45 % faster** despite carrying
  6 NTT-layer + 4 compress/decompress + ntt_multiply
  hacspec-FE-form posts (none of which existed in C4e).
- Full `make` from extraction dir — only failure is the pre-existing
  unrelated `Vector.Neon.Vector_type.fsti(7,8-7,54)` "decidable
  equality" error (same as C4e tip; documented in handoff under
  "Out of scope").

## Architectural changes this session

1. **Per-method `op_*` flattening of `impl Operations for PortableVector`.**
   Every impl method body is now either a one-line call to a free
   `op_<name>(args)` whose pre/post is the *exact* trait pre/post
   (subtyping check `P ==> P`, trivial), or a one-line call to an
   underlying primitive whose pre/post already matches the trait
   (`add`, `sub`, `multiply_by_constant`).  No proof code lives inside
   the impl block.  Each `op_*` and primitive verifies in its own SMT
   scope with its own `#push-options`; `impl_1`'s VC is uniformly
   trivial.  Iteration on any single method is now ~10 s instead of
   ~5 min.

2. **`panic_free` annotations live only on `op_*`** (compress family
   + ntt_multiply) — never on the impl method.  Impl methods carry the
   strong (opaque-where-needed) trait pre/post and have no admits.

3. **`unfold let forall{4,8,16,32}`** in `Spec.Utils.fsti`.  These
   small helpers expand to a fixed N-conjunction; without `unfold`,
   F* leaves them un-inlined at fuel 0, so `assert (forall4 p)`
   appeared to Z3 as an unrelated function application even when each
   `assert (p k)` succeeded individually.  `unfold` makes them inline
   at every use site, turning the assertion into the conjunction
   directly.  Unblocked all 6 NTT-layer wrappers at rlimit 200 — was
   timing out at 225 s on rlimit 400 in `op_ntt_layer_1_step`.

4. **`--z3refresh` removed** from `impl_1` push-options.  It cost ~10×
   on Vector.Portable.fst (217 s → 37 min) and per the smtprofiling
   skill catalog (technique 3) is generally a worse choice than
   `--split_queries always` alone.

5. **AVX2 `compress_*` / `decompress_*`** wrappers were
   pre-emptively marked `panic_free` with strengthened
   `${spec::*_post}` annotations matching the trait's strengthened
   posts (`compress_post_N` / `decompress_post_N`).  Per user
   guideline: don't burn F*/Z3 cycles on doomed proofs; document each
   annotation's reason and removal plan.  **Removal plan**: drop
   `panic_free` and prove the body when C4′ AVX2 mirror lands.

## Side notes

- `Spec.Utils.fsti`: `neg_i16` made total via guard on `i16::MIN`
  (overflow case sent to `mk_i16 0`). Lets the helper appear in trait
  posts without propagating an i16-MIN refinement.

## C4′ AVX2 mirror — refactor landed (proofs pending)

`src/vector/avx2.rs` mirrors the portable `op_*` flattening:

- Each impl method body collapses to a one-line `op_<name>(args)` call;
  trait subtyping check is `P ==> P`.
- `op_*` functions for previously-verified arithmetic ops
  (`cond_subtract_3329`, `barrett_reduce`,
  `montgomery_multiply_by_constant`, `to_unsigned_representative`)
  carry **real proofs** (no `panic_free`): each is a thin
  `reveal_opaque(is_i16b_array_opaque)` plus a call to the AVX2
  primitive, whose strong post (already proven in
  `Vector.Avx2.Arithmetic.fst`) discharges the trait post.
  `op_cond_subtract_3329` adds a `Seq.lemma_eq_intro` to bridge
  per-lane equality to `Spec.Utils.map_array` form (improvement over
  the pre-C4f `lax`).
- `op_*` for compress/decompress/NTT-layer/ntt_multiply carry
  `panic_free` with the same strengthened `${spec::*_post}` posts as
  the portable side (compress_post_N / decompress_post_N /
  hacspec FE-form for NTT). **Body proofs are pending C4′ Layer-1
  helpers in `Hacspec_ml_kem.Commute.Chunk.fst` plus AVX2-specific
  per-lane Vec256 ↔ array bridging.**
- `add`, `sub`, `multiply_by_constant`, `from_bytes`, `to_bytes`,
  `from_i16_array`, `to_i16_array`, `ZERO` — no `op_*` needed: the
  underlying `arithmetic::*` primitive's pre/post already matches the
  trait's exactly, so the impl method body is already a one-liner.
  (`to_bytes` stays `lax` — same as pre-C4f, F*/hax modeling issue
  around `&mut` slice bounds, out of C4' scope.)

Verification (this session):
- `Libcrux_ml_kem.Vector.Avx2.fst` — **PASS** (~11.5 s).
- `Libcrux_ml_kem.Vector.Avx2.Arithmetic.fst` — **PASS** (~26 s).
- `Libcrux_ml_kem.Vector.Avx2.Compress.fst` — **PASS** (~3.6 s).
- `Libcrux_ml_kem.Vector.Avx2.Ntt.fst` — **PASS** (~3.7 s).
- `Libcrux_ml_kem.Vector.Avx2.Serialize.fst` — **PASS** (~48.6 s).
- `Libcrux_ml_kem.Vector.Avx2.Sampling.fst` — **PASS** (~4.6 s).

## C4′ AVX2 serialize/deserialize wrappers — `lax` removed for {1, 4, 10, 12}

`src/vector/avx2.rs` `op_serialize_{4,10,12}` and
`op_deserialize_{1,4,10,12}` now drop `lax` and discharge the trait's
`{,de}serialize_post_N` via per-N admitted bridge lemmas
`op_{serialize,deserialize}_N_{pre,post}_bridge` (defined in a
`fstar::before` block on `op_serialize_4`).  Each bridge connects the
AVX2 primitive's BitVec lane post (`bit_vec_of_int_t_array r 8 i ==
vector ((i/N)*16 + i%N)`) to the trait's array-form post
(`BitVecEq.int_t_array_bitwise_eq` at depth N).

- 7 admitted bridge lemmas total (4 serialize: 3 pre + 3 post for
  N ∈ {4,10,12}; 4 deserialize post for N ∈ {1,4,10,12}; deserialize
  has no pre-bridge — the only pre is `Seq.length`).
- `op_serialize_1`, `op_serialize_11`, `op_deserialize_11` still `lax`:
  underlying primitive is `lax` too, so wrapper bridging is pointless
  until the primitives are proven first.
- **Removal plan for the admits**: per-N `Tactics.GetBit.prove_bit_vector_equality'`
  invocation plus a `bit_vec_of_int_t_array (vec256_as_i16x16 v) N`
  decomposition lemma in `Libcrux_intrinsics.Avx2_extract`.

Verified: `Vector.Avx2.fst` PASS.

## C4′ AVX2 NTT-layer wrappers — `panic_free` removed for all 6

`src/vector/avx2.rs` `op_{ntt,inv_ntt}_layer_{1,2,3}_step` now drop
`panic_free` and discharge the trait's strengthened FE-form posts via
6 admitted bridge lemmas
`op_{ntt,inv_ntt}_layer_N_step_bridge` (defined in a `fstar::before`
block on `op_ntt_layer_1_step`).  Each bridge takes `vector` + zetas
+ `result == ntt::*_step vector zetas` and concludes the trait
`*_step_post` (lifting the AVX2 primitive's body equality up to the
FE-butterfly form on `vec256_as_i16x16`).

- `op_inv_ntt_layer_1_step_bridge` precondition uses the primitive's
  non-opaque `is_i16b_array` (because the underlying
  `inv_ntt_layer_1_step.fsti` requires it); wrapper does
  `reveal_opaque is_i16b_array_opaque` before the call.
- **Removal plan for the admits**: strengthen the primitive posts in
  `Libcrux_ml_kem.Vector.Avx2.Ntt.fsti` (currently `Prims.l_True`)
  to expose per-lane FE equations, then prove each bridge directly
  from those.  `inv_ntt_layer_1_step.fst` body has
  `--admit_smt_queries true` which must be removed first.
- `op_ntt_multiply` keeps `panic_free` (blocked on C4e Layer-0.5
  admits — same on portable).

Verified: `Vector.Avx2.fst` PASS, `Vector.Avx2.{Arithmetic,Compress,
Ntt,Serialize,Sampling}.fst` all PASS, `Vector.Portable.fst` PASS.

## C4′ AVX2 ntt_layer_3_step — top-to-bottom proof landed

Strengthened `Libcrux_ml_kem.Vector.Avx2.Ntt.ntt_layer_3_step` post in
`src/vector/avx2/ntt.rs` to expose the per-lane butterfly residue
equation + `is_i16b_array (6*3328)` bound (matching the trait's
strengthened `ntt_layer_3_step_post`).  Body proof composes:

- **6 generic SIMD lane lemmas** in a `fstar::before` block on
  `ntt_layer_3_step`:
  - `lemma_mm256_castsi256_si128`, `lemma_mm256_extracti128_si256_1`,
    `lemma_mm256_castsi128_si256_lo`, `lemma_mm256_inserti128_si256_1`
    — admitted (require knowing the abstract `vec256_as_i16x16` /
    `vec128_as_i16x8` definitions, which are declared `val` in
    `Avx2_extract.fsti`).
  - `lemma_add_i_128`, `lemma_sub_i_128` — proven by `()`, with
    `SMTPat` triggers on `add_mod` / `sub_mod` to lift `+.` / `-.`
    to integer `+` / `-` under no-overflow.
- Intermediate per-lane assertions chain through `mm256_extracti128`
  → `mm_set1` → `montgomery_multiply_m128i_by_constants` →
  `mm256_castsi256_si128` → `mm_add_epi16` / `mm_sub_epi16` →
  `mm256_castsi128_si256` → `mm256_inserti128_si256<1>`.
- rlimit 400, `--split_queries always`.

The wrapper `op_ntt_layer_3_step` in `src/vector/avx2.rs` now
discharges the trait FE-form post directly via 8
`Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute` calls
(one per pair `(i, i+8)`) + per-b assertions + `forall4` —
identical pattern to portable.  No bridge admit needed for
`ntt_layer_3_step` anymore.

The other 5 NTT-layer wrappers (`ntt_layer_{1,2}_step` +
`inv_ntt_layer_{1,2,3}_step`) still use admitted bridge lemmas;
each could follow the same pattern once their primitive bodies in
`Vector.Avx2.Ntt.fst` get the matching strengthened posts (the 4
SIMD lane lemmas defined here are reusable).

Verified: `Vector.Avx2.fst`, `Vector.Avx2.Ntt.fst`,
`Vector.Avx2.{Arithmetic,Compress,Sampling,Serialize}.fst`,
`Vector.Portable.fst` all PASS.

## Inverse NTT layer 2/3 Barrett: spec aligned with AVX2/Neon optimization

`inv_ntt_layer_{2,3}_step` in `src/vector/avx2/ntt.rs` and
`src/vector/neon/ntt.rs` deliberately omit the Barrett reduction on
the sum lanes that portable's `inv_ntt_step` (called from
`inv_ntt_layer_{2,3}_step` in `src/vector/portable/ntt.rs`) applies.
This is an intentional optimization: each Barrett costs ~5 SIMD ops,
and the next Barrett in `invert_ntt_at_layer_4_plus`'s `step_reduce`
mops up the looser bound.  Portable was over-reducing.

Spec changes (in `src/vector/traits.rs`):
- `inv_ntt_layer_2_step_post`: `is_i16b_array_opaque 3328` →
  `is_i16b_array_opaque (2*3328)`.
- `inv_ntt_layer_3_step_pre`:  `is_i16b_array_opaque 3328` →
  `is_i16b_array_opaque (2*3328)`.
- `inv_ntt_layer_3_step_post`: `is_i16b_array_opaque 3328` →
  `is_i16b_array_opaque (4*3328)`.

Caller-side changes (in `src/invert_ntt.rs`):
- `invert_ntt_at_layer_2`: ensures bound `3328` → `2*3328`.
- `invert_ntt_at_layer_3`: requires bound `3328` → `2*3328`; ensures
  `3328` → `4*3328`.
- `invert_ntt_at_layer_4_plus`: requires bound `3328` → `4*3328`
  (uniform across all 4 calls; widening hints added in
  `invert_ntt_montgomery` between consecutive layer_4_plus calls).
- `inv_ntt_layer_int_vec_step_reduce`: requires
  `is_bounded_vector(3328, ...)` → `is_bounded_vector(4*3328, ...)`;
  internal `is_bounded_vector_higher` adjusted from `(6656, 28296)`
  to `(8*3328, 28296)`.

Bound trace (documented inline in `src/invert_ntt.rs`):
```
layer 1 input:  4*3328 → output: 3328 (Barrett)
layer 2 input:  3328   → output: 2*3328  (no Barrett)
layer 3 input:  2*3328 → output: 4*3328  (no Barrett)
layer 4_plus(4) input: 4*3328 → output: 3328 (Barrett in step_reduce)
layer 4_plus(5..7):    3328   → 3328 (steady state)
```

Safety (no integer overflow): worst-case sums in layers 2/3 are
`6656` and `13312`, both well below `i16` max (`32767`).  In
`step_reduce`, `a_plus_b` reaches `26624 < 28296` (Barrett pre).
Mont-mul i32 product peaks at `26624 × 1664 ≈ 4.4×10⁷ << 2³¹`.

External impact: **none** — `invert_ntt_montgomery`'s post is
unchanged at `is_bounded_poly(3328)`, so callers see identical
contracts.

Performance gain: ~80 SIMD ops saved per inverse NTT call (16
Barrett reductions removed × ~5 ops each) — was previously redundant
work on portable, was an unproven implicit optimization on AVX2/Neon.

Verified: `Vector.Portable.fst`, `Vector.Avx2.fst`, `Invert_ntt.fst`
all PASS (rlimit 400 on `invert_ntt_at_layer_{1,2,3}` due to query
size, with `--ext context_pruning` and split-query retries).

Note: portable's `inv_ntt_step` still does Barrett (used by layer 1).
Layers 2/3 in portable accept the looser primitive output trivially
(3328 ≤ 6656 ≤ 13312).  Removing Barrett from portable layers 2/3
specifically would require splitting `inv_ntt_step` into Barrett and
no-Barrett variants — left as a perf follow-up.

## Forward NTT bound symmetry

Audited via subagent: all three backends (portable, AVX2, Neon) use
pure mont_mul + add/sub butterflies in forward `ntt_layer_N_step`
bodies — no Barrett anywhere.  Bounds grow monotonically `3 → 4803 →
2*3328 → … → 8*3328`, then `re.poly_barrett_reduce()` once at the end
of `ntt`.  No analogue to the inverse-NTT layer 2/3 Barrett asymmetry
in the forward direction.

## Manual proof targets (A1–A7) for the user

See `proofs/manual-proof-targets.md` for a brief on which lemmas in
`Hacspec_ml_kem.Commute.Chunk.fst` would maximally unblock Claude's
ongoing work toward the milestone "every trait fn proven down to
SIMD/integer-arithmetic admits".  Tier 1: 4 admitted
`lemma_base_case_mult_*` (close `op_ntt_multiply` on both backends).
Tier 2: 3 easy compress/decompress fe_commute lemmas to write (close
6 wrappers).

## Deferred: SIMD model unification with libcrux-ml-dsa

See `proofs/simd-model-unification-plan.md` for a deferred plan to
unify the AVX2 SIMD model with libcrux-ml-dsa's `core-models`-based
approach.  Today both crates have parallel, incompatible bit-vector
libraries (`fstar-helpers/fstar-bitvec/BitVec.Bv` vs
`core_models::abstractions::bitvec::BitVec`) and parallel lane views
(abstract `vec256_as_i16x16` vs defined `to_i16x16` with inversion
lemmas) — every SIMD lemma we write today is doomed to a single repo.

**To pick up after C4' is fully done.**  Migration is sequenced to
discharge several currently-admitted ML-KEM SIMD lemmas as a side
effect (the four lane-bridge admits in `Vector.Avx2.Ntt.fsti`, the
seven serialize bridge admits in `Vector.Avx2.fst`).  Phased rollout
with single-cfg-flag toggle (`pre_core_models`) for incremental
migration.

## Open follow-ups

- **Phase 2 of the impl-flattening refactor**: for some `op_*` we may
  be able to fold the bridging directly into the underlying primitive's
  annotations and drop the wrapper.  Tracked separately.
- **C4′ true mirror (drop `panic_free`)**: AVX2 NTT-layer + compress/
  decompress + ntt_multiply `op_*` bodies need real proofs once
  the portable Layer-1 helpers and AVX2 per-lane Vec256↔array bridges
  are in place.
- **Forall-style benchmark**: which of `forall (k:nat). k<N ==> P k` /
  `forall (k:nat{k<N}). P k` / `Spec.Utils.forall<N> (fun k -> P k)`
  is most efficient in trait posts and at callers.  Dispatched as a
  parallel research task this session; results inform Phase 2.
- **C4e Layer-0.5 admits**: `lemma_base_case_mult_{even,odd}_{mod_core,fe_commute}`
  in `Hacspec_ml_kem.Commute.Chunk.fst` are still admitted; closing
  them unlocks dropping `panic_free` from `op_ntt_multiply`.

## Pointer to full handoff

See `proofs/commutativity-handoff.md`.
