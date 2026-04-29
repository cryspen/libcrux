# ML-DSA Proof Milestones

Hand-curated tracker of *meaningful* proof outcomes, complementing the
mechanical `verification_status.md` tier counts. Each row is a named
proof goal; status is judged by inspecting the owning function's
`#[ensures(...)]` text and body annotations on `ml-dsa-proofs`
(HEAD `9d724080f`).

## Status legend

- ✅ **Proven** — ensures cites `Hacspec_ml_dsa.*` (or `Spec.MLDSA.*`),
  body verifies (no admits).
- 🔶 **Spec stated, body admitted** — ensures shape correct but body
  has an admit.
- ⚠️ **Bounds only** — ensures proves a range/interval predicate; no
  hacspec equivalence.
- ❌ **No claim** — function has no ensures or is unverified at any tier.

## Distance bands

- *(done)* — proof complete.
- *1 user-task* — known scope, ~0.5-1 sprint each.
- *~1 sprint* — needs spec definition + ensures + proof for a single function.
- *~2-3 sprints* — multi-component (whole module).
- *many sprints* — needs design + spec + multi-fn proof.

---

## Layer 1 — NTT (forward & inverse)

The ml-dsa NTT operates on `PolynomialRingElement` of 32 SIMD units of
8 i32 lanes each (256 coefficients total). Hacspec equivalence would
cite `Hacspec_ml_dsa.Ntt.ntt` / `.ntt_inverse` if such a spec module
existed — currently it does NOT (no `Hacspec_ml_dsa.*` references
anywhere in src/).

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 1 | Top-level forward NTT correct vs hacspec | `src/ntt.rs:15 ntt` | ⚠️ bounds only — pre/post are `is_i32b_array_opaque NTT_BASE_BOUND → FIELD_MAX`; no hacspec citation | **many sprints** — `Hacspec_ml_dsa.Ntt.*` spec module does not exist; need to (a) write the spec, (b) write per-layer Bridges lemmas, (c) connect at the function level |
| 2 | Top-level inverse NTT correct vs hacspec | `src/ntt.rs:28 invert_ntt_montgomery` | ⚠️ bounds only — same shape | gated on (1)'s spec design; once Hacspec_ml_dsa.Ntt is in place, ~2-3 sprints to mirror what ml-kem did with `invert_ntt_at_layer_*` |
| 3 | NTT multiply correct vs hacspec | `src/ntt.rs:57 ntt_multiply_montgomery` | ⚠️ bounds only | ~1 sprint after (1) |
| 4 | Top-level Barrett reduce correct | `src/ntt.rs:44 reduce` | ⚠️ bounds only | ~1 sprint — modular-arithmetic spec |
| 5 | Per-SIMD-unit NTT layers (Portable) | `src/simd/portable/ntt.rs::simd_unit_ntt_at_layer_{0,1,2}` | ⚠️ bounds only — 11 fns in Portable/ntt all bounds-classified | ~1-2 sprints — needs `Hacspec_ml_dsa.Simd.Portable.Ntt.*` lemmas; today these are bounds-proven but not vs-spec |
| 6 | Per-SIMD-unit NTT layers (AVX2) | `src/simd/avx2/ntt.rs::simd_unit_ntt_at_layer_{0,1,2}` | ⚠️ bounds only | same as (5), AVX2 backend |
| 7 | Per-SIMD-unit inverse NTT (Portable & AVX2) | `src/simd/{portable,avx2}/invntt.rs` | ⚠️ bounds only | same |
| 8 | SIMD trait `ntt`/`invert_ntt` post | `src/simd/traits.rs` | ⚠️ bounds only via `is_i32b_array_opaque` | ~1 sprint — strengthen trait posts, then propagate |

## Layer 2 — Encoding / Serialization

ml-dsa has 8 encoding files for distinct field elements: `commitment`,
`error`, `gamma1`, `signature`, `signing_key`, `t0`, `t1`,
`verification_key`. Each is a (de)serialization of a fixed-width
field. The script-counted 'Hacspec' tier of 53 across the crate is
concentrated in `Simd/{Portable,Avx2}/Encoding/*` (the SIMD-level
helpers, not the high-level encoding).

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 9 | `encoding/t0::serialize/deserialize` correct vs hacspec | `src/encoding/t0.rs:30, 88` | ⚠️ bounds only — pre uses `is_i32b_strict_lower_array_opaque (pow2 12)`, ensures only `Seq.length`; no hacspec citation | ~1-2 sessions per file once `Hacspec_ml_dsa.Encoding.T0` exists (currently no `Hacspec_ml_dsa.*` references in any encoding file) |
| 10 | `encoding/t1::serialize/deserialize` correct vs hacspec | `src/encoding/t1.rs` | ⚠️ bounds only | same |
| 11 | `encoding/gamma1::serialize/deserialize` correct vs hacspec | `src/encoding/gamma1.rs` | ⚠️ bounds only | same |
| 12 | `encoding/error::serialize/deserialize` correct vs hacspec | `src/encoding/error.rs` | ⚠️ bounds only | same |
| 13 | `encoding/commitment::serialize/deserialize` correct vs hacspec | `src/encoding/commitment.rs` | ⚠️ bounds only | same |
| 14 | `encoding/signature::serialize/deserialize` correct vs hacspec | `src/encoding/signature.rs` | ⚠️ bounds only — `Encoding.Signature.deserialize` body recently closed (per HEAD commit) | per-file ~1-2 sessions |
| 15 | `encoding/signing_key`, `verification_key` correct vs hacspec | resp. files | ⚠️ bounds only | ~1-2 sessions each |
| 16 | SIMD-backend per-encoding helpers | `src/simd/{portable,avx2}/encoding/{commitment,error,gamma1,t0,t1}.rs` | partial — 28 hacspec in Portable/encoding, 17 in Avx2/encoding (per script) | the SIMD-level proofs are **the most advanced**; the gap is at the wrapping (Generic) `encoding/*.rs` layer connecting them to a top-level spec |

## Layer 3 — Top-level ML-DSA API

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 17 | `MlDsa44::generate_key_pair` panic-free | `src/ml_dsa_44.rs:16, 183` | ❌ — no ensures shown; 15 fns in this file are flagged as **Lax** by the script (admit-by-VERIFIED_MODULES exclusion) | ~1-2 sprints — gated on the per-variant Hacspec spec wiring + dropping the module from admits |
| 18 | `MlDsa44::sign` correct vs hacspec | `src/ml_dsa_44.rs:38, 208` | ❌ — wraps `ml_dsa_generic.sign`; no top-level spec citation | gated on (1)+(9-16); + `Hacspec_ml_dsa.sign` spec needed; **many sprints** |
| 19 | `MlDsa44::verify` correct vs hacspec | `src/ml_dsa_44.rs:131, 266` | ❌ same | same |
| 20 | `MlDsa65/87::*` (per-variant API) | `src/ml_dsa_65.rs`, `src/ml_dsa_87.rs` | ❌ same | ~1 session per variant once (18)/(19) lands for 44 (variants share `ml_dsa_generic` core) |
| 21 | `ml_dsa_generic::generate_key_pair` correct | `src/ml_dsa_generic.rs:57` | ❌ no ensures — has body-admit (per script's body-admit audit table, line 57) | gated on per-component sub-proofs |
| 22 | `ml_dsa_generic::sign_internal` correct | `src/ml_dsa_generic.rs:134` | ❌ — body admit (line 134 in audit table) | needs full sign-loop spec; **many sprints** |
| 23 | `ml_dsa_generic::verify_internal` correct | `src/ml_dsa_generic.rs:364` | ❌ — body admit (line 364) | same |
| 24 | `pre_hash` correct | `src/pre_hash.rs` | ⚠️ — included in Generic; check tier counts |  ~1 session |
| 25 | Hash functions correct (Shake128/256, Simd256/Portable/Neon backends) | `src/hash_functions.rs` (nested mods) | ⚠️ — ancestor-covered (the parent file maps to nested `Libcrux_ml_dsa.Hash_functions.{Portable,Neon,Simd256,Shake128,Shake256}.fst` files); per-mod hacspec needs verification | ~2 sprints to add `Hacspec_ml_dsa.Hash_functions.*` spec + per-mod proof |

## Headline interpretation

The script's "Hacspec: 53/577 (9.2%)" on ml-dsa is concentrated in:
- **Simd/Portable** (28 hacspec) — per-SIMD-unit encoding & arithmetic helpers
- **Simd/Avx2** (17 hacspec) — same, AVX2 backend
- **Generic** (8 hacspec) — scattered top-level lemmas

What the count does NOT reflect:
- The **Generic NTT** (rows 1-3) has zero hacspec — only bounds. No
  `Hacspec_ml_dsa.Ntt.*` spec module exists.
- The **Generic encoding** (rows 9-15) has zero hacspec — only bounds
  + length preservation. No `Hacspec_ml_dsa.Encoding.*` spec module.
- The **API surface** (rows 17-23) is mostly Lax (admitted) and has
  no top-level functional ensures.

## Comparison with ml-kem trajectory

The ml-dsa proof posture is roughly **where ml-kem was before
trait-opacify** in terms of hacspec coverage of the upper layers:

| Aspect | ml-dsa (today) | ml-kem (main, pre-trait-opacify) | ml-kem (trait-opacify) |
|---|---|---|---|
| SIMD trait posts cite hacspec | Partial (28+17 hacspec) | No | Yes (27+23 hacspec) |
| Generic NTT cites hacspec | No (bounds only) | No | Partial (4 inverse layers) |
| Generic encoding cites hacspec | No | No | No (panic_free) |
| Top-level API has functional ensures | No | No | No |
| `ADMIT_MODULES` discipline | Inverted (many extracted-but-admitted) | Explicit (few admits) | Same as main, +SD3/SD4 work |

The ml-dsa lift to ml-kem-trait-opacify-level would require an
analogous push: define the `Hacspec_ml_dsa` spec module hierarchy,
strengthen trait posts at the `Simd::Operations` boundary, then
propagate citations layer-by-layer through `Ntt`, `Encoding`,
`Sample`, `Matrix`, `Polynomial`.

## Next-priority order

1. **Drop `Ind_cpa`-equivalent module-level admits** — the inverted
   Makefile pattern means many extracted modules show as Lax even
   though their proofs may be partially in place. Audit `VERIFIED_MODULES`
   to see what's missing.
2. **Define `Hacspec_ml_dsa.Ntt.*` spec module** — gates rows 1-7. ~1
   sprint of spec design.
3. **Define `Hacspec_ml_dsa.Encoding.*` spec modules** — gates rows
   9-15. ~1 sprint per encoding (8 of them).
4. **Strengthen `simd::traits::Operations` posts to cite hacspec** —
   gates the propagation to higher layers (mirror of ml-kem trait-opacify).
5. **Top-level API specs (`Hacspec_ml_dsa.sign/verify`)** — last; many
   sprints; gates the entire correctness story.
