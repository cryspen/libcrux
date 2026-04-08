import Hax
import Stubs  -- from spec project (hacspec_sha3), provides coercions + core_models.num

/-! # Stubs for missing functions and instances (implementation-specific)

These fill gaps in the hax Lean backend extraction for the implementation.
Shared stubs (coercions, core_models.num) come from the spec's Stubs.
-/

/-! ## Bridge `core_models.ops.index.Index` → `GetElemResult`

The hax Lean backend emits `Index` instances for Rust `impl Index<I> for T`,
but translates indexing expressions `x[i]` to the `x[i]_?` syntax which
resolves via `GetElemResult`.  This generic instance bridges the two.
-/
instance instGetElemResultOfIndex
    (C : Type) (I : Type)
    [assoc : core_models.ops.index.Index.AssociatedTypes C I]
    [inst : core_models.ops.index.Index C I] :
    GetElemResult C I assoc.Output where
  getElemResult xs i := inst.index xs i

/-! ## `GetElemResult` instances for `RangeTo` and `RangeFrom`

The Hax prelude provides `GetElemResult` for `Range usize` but not for
`RangeTo` or `RangeFrom`.
-/
open core_models.ops.range in
instance RangeTo.instGetElemResultSeq {α : Type} :
    GetElemResult (rust_primitives.sequence.Seq α)
      (RangeTo usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk (0 : usize) i._end)

open core_models.ops.range in
instance RangeTo.instGetElemResultRustArray {α : Type} {n : usize} :
    GetElemResult (RustArray α n)
      (RangeTo usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk (0 : usize) i._end)

open core_models.ops.range in
instance RangeFrom.instGetElemResultSeq {α : Type} :
    GetElemResult (rust_primitives.sequence.Seq α)
      (RangeFrom usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk i.start (USize64.ofNat xs.val.size))

open core_models.ops.range in
instance RangeFrom.instGetElemResultRustArray {α : Type} {n : usize} :
    GetElemResult (RustArray α n)
      (RangeFrom usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk i.start n)

-- Coercions and core_models.num stubs are provided by the spec's Stubs.lean
-- (imported transitively via the spec project dependency).

/-! ## `rust_primitives.hax.monomorphized_update_at` — slice range update -/

namespace rust_primitives.hax.monomorphized_update_at

/-- Replace `s[r.start .. r.end]` with `v`. Requires matching lengths. -/
def update_at_range (s : rust_primitives.sequence.Seq α)
    (r : core_models.ops.range.Range usize) (v : rust_primitives.sequence.Seq α) :
    RustM (rust_primitives.sequence.Seq α) :=
  if h : r._end.toNat ≤ s.val.size ∧ r.start.toNat ≤ r._end.toNat ∧
      v.val.size = r._end.toNat - r.start.toNat then
    let arr := s.val
    let result := (arr.extract 0 r.start.toNat) ++ v.val ++ (arr.extract r._end.toNat arr.size)
    have ⟨h1, h2, h3⟩ := h
    have hsz : result.size = s.val.size := by
      simp only [result, arr, Array.size_append, Array.size_extract, Nat.min_self,
        Nat.min_eq_left (by omega : r.start.toNat ≤ s.val.size)]; omega
    pure ⟨result, by rw [hsz]; exact s.size_lt_usizeSize⟩
  else .fail .arrayOutOfBounds

@[irreducible] def update_at_range_from {S : Type}
    (s : S) (r : core_models.ops.range.RangeFrom usize) (v : S) :
    RustM S := sorry

end rust_primitives.hax.monomorphized_update_at

/-! ## `hax_lib.int` — integer-from-string literal -/

namespace hax_lib.int

@[irreducible] def Impl_7._unsafe_from_str (s : String) : RustM hax_lib.int.Int := sorry

end hax_lib.int
