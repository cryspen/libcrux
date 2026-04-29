# Wave-A admit baseline (commit `047da6de8`, 2026-04-29)

Baseline established by grep — full `make` deferred until user's
serialize CLI processes (PIDs 50388, 65549) finish.

## In-scope (Wave-A movable) admits

| File | Lines | Count | Lane |
|---|---|---|---|
| `specs/.../Hacspec_ml_kem.Commute.Chunk.fst` | 985, 1069, 1083 | 3 | B6 (A8 only — line 985); 1069/1083 above-trait |
| `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Avx2.fst` (per-N bridge admits) | 316, 328, 348, 360, 564, 570, 581, 593, 599, 610, 622, 628, 639, 651 | 14 | B3 (serialize/deserialize bridges) |
| `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Avx2.fst` (`--admit_smt_queries true` regions) | 57, 653 | 2 (regions) | B3/B4 wrappers |
| `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Avx2.Ntt.fst` | 55, 62, 69, 83, 192, 332 | 6 | B4 (SIMD primitive bodies) |
| `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Avx2.Serialize.fst` (`--admit_smt_queries true`) | 13, 549, 567 | 3 (regions) | B3 partial (lax bodies) |
| `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Portable.fst` (`--admit_smt_queries true`) | 385, 620 | 2 (regions) | B1 / B5 |
| `src/vector/portable.rs` (panic_free) | 899 (op_ntt_multiply) | 1 | B5 |
| `src/vector/portable/compress.rs` (panic_free) | 27, 113, 170, 222, 289, 347 | 6 | B1 partial |
| `src/vector/avx2.rs` (panic_free) | 24, 33, 43, 269, 283, 297, 571 | 7 | B3 / B4 / B5 |
| `src/vector/avx2/sampling.rs` (panic_free) | 8 | 1 | n/a (out-of-scope) |
| `src/vector/avx2/arithmetic.rs` (panic_free) | 336 | 1 | n/a |

## Out-of-scope (above-trait, Wave-B/C own)

`src/serialize.rs`, `src/sampling.rs`, `src/polynomial.rs`,
`src/invert_ntt.rs`, `src/ind_cca.rs`, `src/mlkem512.rs`,
`src/mlkem1024.rs` panic_free + `--admit_smt_queries true` are all
above-trait. `Libcrux_ml_kem.Vector.Neon.*` is permanently admitted
per user directive (portable + AVX2 only).

## Tracking metric

Target reductions:
- B6: 1 admit (Chunk.fst line 985 / A8) → CLOSED.
- B1: -1 to -6 (compress/decompress portable.rs panic_free).
- B5: -2 (op_ntt_multiply portable + AVX2 panic_free).
- B3: ~7 bridge admits in Vector.Avx2.fst.
- B4: 0-6 (high-risk; descope on first wall).

PROGRESS counted as: existing admit removed and proof closes for real.
SIDEWAYS: relocated to new admitted lemma (note: factoring is OK if
new lemma is well-scoped USER-N).
FAIR GAME: NEW small (≤10-line) arithmetic/bitvec admit handed off
to USER-N.
