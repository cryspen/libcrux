# Manual Proof Targets — A1–A7

High-leverage manual proof opportunities in
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`.
Each closes one or more `panic_free` carriers on **both** the portable
and AVX2 backends.

After each lemma lands, the corresponding wrapper bridge admit in
`src/vector/avx2.rs` (and the `panic_free` flag on the same wrapper in
`src/vector/portable.rs`) is removed.

**Suggested order**: A3 → A4 → A6 → A5 → A1 → A2 → A7. (Easiest first;
A1 last because it has a Z3-divergence problem and benefits from
warm-up on A3.)

**Notation**: `mont_i16_to_spec_fe x = (x · 169) mod 3329`,
abbreviated `mont_fe x` below. `q = 3329`.

---

## A1–A4: Close existing admits

These all share the Z3-divergence root cause documented at
`Hacspec_ml_kem.Commute.Chunk.fst` line ~298:

> Z3 does not converge on this encoding at r-limit 300 with
> `--split_queries always`: queries 1-4 succeed in 14, 54, 123, 642 ms
> but query 5 runs 15+ minutes before timing out.

The math is correct — Z3 just won't converge on the encoded form.
Manual structural decomposition (split the residue chain, use
hand-picked `lemma_mod_*_distr` invocations, avoid letting Z3 explore
non-linear arithmetic) should close them.

### A1 — `lemma_base_case_mult_even_mod_core`

**Location**: `Hacspec_ml_kem.Commute.Chunk.fst` line ~309–315.

**Statement**:
```fstar
val lemma_base_case_mult_even_mod_core (a0 a1 b0 b1 z r: int) :
  Lemma (requires r % 3329 == ((a0 * b0 + a1 * b1 * z * 169) * 169) % 3329)
        (ensures  ((((a0 * 169) % 3329 * (b0 * 169) % 3329) % 3329)
                   + ((((a1 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                      * ((z * 169) % 3329)) % 3329) % 3329
                  == (r * 169) % 3329)
```

**Why it holds**: this is the "even lane" of `ntt_multiply_binomials_post`.
The impl computes `r ≡ (a0·b0 + a1·b1·z·169) · 169 (mod q)` (Montgomery
form). The hacspec FE post wants
`mont_fe r == (mont_fe a0 · mont_fe b0) + ((mont_fe a1 · mont_fe b1) · mont_fe z)`.
The lemma is the integer-level commutation. It composes 4 applications
of `lemma_mod_mul_distr_l/r` and 2 of `lemma_mod_add_distr` —
analogous to `lemma_butterfly_mod_core` (line 170–183) which is
already proven.

**Recommended proof structure** (mirrors `lemma_butterfly_mod_core`):

1. Push `% q` through inner muls:
   `((a1·169 % q) · (b1·169 % q)) % q == (a1·b1·169·169) % q`.
   Use `lemma_mod_mul_distr_l` then `lemma_mod_mul_distr_r`.
2. `((step 1) · (z·169 % q)) % q == (a1·b1·z·169·169·169) % q`.
   Use `lemma_mod_mul_distr_l` then `_r`.
3. Same for `a0·b0`:
   `((a0·169 % q) · (b0·169 % q)) % q == (a0·b0·169·169) % q`.
4. Add: `((step 3) + (step 2)) % q`. Use `lemma_mod_add_distr` twice.
5. Algebra:
   `a0·b0·169·169 + a1·b1·z·169·169·169 == (a0·b0 + a1·b1·z·169) · 169 · 169`.
6. Push `(... · 169) % q == (r · 169) % q` via the requires.
   Use `lemma_mod_mul_distr_l`.

**Likely Z3-divergence point**: step 5 (non-linear distributivity over
a sum of two terms each containing `169·169`).

**Fix**: write that step as an explicit `assert_norm`, or as a
separate `let _ = assert (...) by FStar.Tactics.canon ()`-style hint,
or break it into a sub-lemma proven over `int` (Z3 handles linear int
better when the non-linear bits are isolated).

### A2 — `lemma_base_case_mult_even_fe_commute`

**Location**: `Hacspec_ml_kem.Commute.Chunk.fst` line ~322 (already
admitted per status doc).

**Statement** (`P = Hacspec_ml_kem.Parameters`):
```fstar
val lemma_base_case_mult_even_fe_commute
    (a0 a1 b0 b1 zeta result: i16) :
  Lemma (requires v result % 3329
                  == ((v a0 * v b0 + v a1 * v b1 * v zeta * 169) * 169) % 3329)
        (ensures mont_i16_to_spec_fe result ==
                 P.impl_FieldElement__add
                   (P.impl_FieldElement__mul
                     (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b0))
                   (P.impl_FieldElement__mul
                     (P.impl_FieldElement__mul
                       (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b1))
                     (mont_i16_to_spec_fe zeta)))
```

**Why it holds**: lifts A1 from integers to FE via
`lemma_impl_mul_v_val` (3 applications, one per `__mul`) +
`lemma_impl_add_v_val` (1 application). Trivial *if* A1 lands.
Pattern is identical to `lemma_butterfly_fe_commute_plus`
(line 185–198).

**Recommended proof**:
```fstar
= let prod_a  = P.impl_FieldElement__mul
                  (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b0) in
  let prod_b  = P.impl_FieldElement__mul
                  (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b1) in
  let prod_bz = P.impl_FieldElement__mul prod_b (mont_i16_to_spec_fe zeta) in
  lemma_impl_mul_v_val (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b0);
  lemma_impl_mul_v_val (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b1);
  lemma_impl_mul_v_val prod_b (mont_i16_to_spec_fe zeta);
  lemma_impl_add_v_val prod_a prod_bz;
  lemma_base_case_mult_even_mod_core
    (v a0) (v a1) (v b0) (v b1) (v zeta) (v result)
```

### A3 — `lemma_base_case_mult_odd_mod_core`

**Location**: `Hacspec_ml_kem.Commute.Chunk.fst` (analogous to A1, also
admitted).

**Statement** (the "odd lane" Montgomery): the impl computes
`r ≡ (a0·b1 + a1·b0) · 169 (mod q)`.

```fstar
val lemma_base_case_mult_odd_mod_core (a0 a1 b0 b1 r: int) :
  Lemma (requires r % 3329 == ((a0 * b1 + a1 * b0) * 169) % 3329)
        (ensures  ((((a0 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                   + (((a1 * 169) % 3329 * (b0 * 169) % 3329) % 3329)) % 3329
                  == (r * 169) % 3329)
```

**Why it holds**: simpler than A1 — only two `mul` chains, no extra
`z·169` factor. Direct mod-distr chain without the non-linear pile-up
that breaks A1's query 5. **Should be much easier than A1.**

**Recommended proof**: 4 `lemma_mod_mul_distr_l/r` + 2
`lemma_mod_add_distr` + the final pull-out
`(... · 169) == ((a0·b1 + a1·b0) · 169)`.

### A4 — `lemma_base_case_mult_odd_fe_commute`

**Statement**: lifts A3 to FE. Same pattern as A2 (3
`lemma_impl_mul_v_val` + 1 `lemma_impl_add_v_val` + invoke A3).

```fstar
val lemma_base_case_mult_odd_fe_commute
    (a0 a1 b0 b1 result: i16) :
  Lemma (requires v result % 3329 == ((v a0 * v b1 + v a1 * v b0) * 169) % 3329)
        (ensures mont_i16_to_spec_fe result ==
                 P.impl_FieldElement__add
                   (P.impl_FieldElement__mul
                     (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b1))
                   (P.impl_FieldElement__mul
                     (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b0)))
```

---

## A5–A7: Write new lemmas (don't exist yet)

All three are integer / case-analysis arguments — no Z3 divergence
risk. Easy to land.

### A5 — `lemma_compress_message_coefficient_fe_commute`

**To create in**: `Hacspec_ml_kem.Commute.Chunk.fst`, near the
`compress` family of lemmas (or a new section).

**Approximate signature** (settle exact phrasing against
`op_compress_1` in `vector/portable.rs` and `vector/avx2.rs`):
```fstar
val lemma_compress_message_coefficient_fe_commute
    (fe: i16) (result: i16) :
  Lemma (requires v fe >= 0 /\ v fe < 3329 /\
                  v result == ((v fe * 4 + 3329) / 6658) % 2)
        (ensures Hacspec_ml_kem.Compress.compress_d
                   (i16_to_spec_fe fe) (mk_usize 1)
                 == i16_to_spec_fe result)
```

**Why it holds (case analysis from `MLKEM_STATUS.md:24–26`)**:
For `fe ∈ [0, 3329)`, the impl computes
`result = ((4·fe + 3329) / 6658) mod 2`. Three cases:

| `fe` range     | `4·fe + 3329`  | `÷ 6658` | `mod 2` | `compress_d fe 1` |
|----------------|----------------|----------|---------|-------------------|
| `[0, 832]`     | `[3329, 6657]` | `0`      | `0`     | `0` ✓             |
| `[833, 2496]`  | `[6661, 13313]`| `1`      | `1`     | `1` ✓             |
| `[2497, 3328]` | `[13317, 16641]`| `2`     | `0`     | `0` ✓             |

`compress_d fe 1` (per Hacspec) maps `fe` to `1` if
`fe ∈ [833, 2496]` else `0`.

**Recommended proof**: 3-case split via
`if v fe <= 832 then ... else if v fe <= 2496 then ... else ...`,
each case discharged by `assert` with explicit bounds + a
`Math.Lemmas.lemma_div_lt`-style invocation (or `assert_norm` if the
constants are concrete enough).

### A6 — `lemma_decompress_1_fe_commute`

**To create in**: same file.

**Approximate signature**:
```fstar
val lemma_decompress_1_fe_commute (a result: i16) :
  Lemma (requires v a >= 0 /\ v a <= 1 /\
                  v result == (if v a = 0 then 0 else 1665))
        (ensures Hacspec_ml_kem.Compress.decompress_d
                   (i16_to_spec_fe a) (mk_usize 1)
                 == i16_to_spec_fe result)
```

**Why it holds**: trivial 2-value enumeration.
`decompress_d 0 1 == 0` and `decompress_d 1 1 == 1665` (per Hacspec
spec, formula `(2·a·3329 + 2)/4`):
- `a = 0`: `(0 + 2)/4 = 0`
- `a = 1`: `(6658 + 2)/4 = 6660/4 = 1665`

**Recommended proof**:
```fstar
= if v a = 0 then assert_norm (v result == 0)
  else (assert (v a == 1); assert_norm (v result == 1665))
```
plus whatever `i16_to_spec_fe` reductions F* needs (probably free).
Body should fit in 3–5 lines.

### A7 — `lemma_decompress_ciphertext_coefficient_fe_commute`

**To create in**: same file.

**Approximate signature** (parameterized by `D ∈ {4, 5, 10, 11}`):
```fstar
val lemma_decompress_ciphertext_coefficient_fe_commute
    (a result: i16) (d: usize) :
  Lemma (requires (v d == 4 \/ v d == 5 \/ v d == 10 \/ v d == 11) /\
                  v a >= 0 /\ v a < pow2 (v d) /\
                  v result == (2 * v a * 3329 + pow2 (v d)) / pow2 (v d + 1))
        (ensures Hacspec_ml_kem.Compress.decompress_d
                   (i16_to_spec_fe a) d
                 == i16_to_spec_fe result)
```

**Why it holds (per `MLKEM_STATUS.md:30–31`)**: spec and impl use the
*same* formula `(2·a·3329 + 2^D) / 2^(D+1)` — only difference is `>>`
(impl) vs `/` (spec). Bit-shift = floor-div for non-negative operands.

**Recommended proof**: assert `pow2 (v d + 1) == 2 * pow2 (v d)`, then
the impl formula matches the spec by congruence. Body 5–10 lines.

---

## Once each lands

| You land    | Claude drops                                                                  |
|-------------|-------------------------------------------------------------------------------|
| A1+A2+A3+A4 | `panic_free` on `op_ntt_multiply` (both backends) + bridge admit in `avx2.rs` |
| A5          | `panic_free` on `op_compress_1` (both backends) + bridge admit                |
| A6          | `panic_free` on `op_decompress_1` (both backends) + bridge admit              |
| A7          | `panic_free` on `op_decompress_ciphertext_coefficient<D>` + bridge admit      |

A8 (Barrett compress, `lemma_compress_ciphertext_coefficient_fe_commute`)
can be admitted with English hints — full proof is very tedious and
the C4f plan explicitly noted this.

---

## Notes on signatures

The exact lemma signatures above are approximate. Before drafting,
double-check against:

- `src/vector/traits.rs` for the strengthened
  `compress_*_post` / `decompress_*_post` predicates.
- `src/vector/portable.rs` (`op_compress_1`, `op_decompress_1`,
  `op_decompress_ciphertext_coefficient`) and `src/vector/avx2.rs`
  for the wrapper requires/ensures shape.
- Existing primitives in `src/vector/portable/compress.rs` and
  `src/vector/avx2/compress.rs` for the Montgomery / Barrett residue
  forms the wrappers receive.
- `Hacspec_ml_kem.Compress.compress_d` / `decompress_d` for the FE
  side.

The primitive posts in `Vector.{Portable,Avx2}.Compress.fsti` already
expose the integer/residue equation. The wrappers feed that into the
new lemma to derive the FE equality.
