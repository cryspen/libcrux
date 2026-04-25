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

## Pointer to full handoff

See `proofs/commutativity-handoff.md`.
