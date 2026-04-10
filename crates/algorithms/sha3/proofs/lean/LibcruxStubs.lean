import Hax
import Std.Do.Triple
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

/-- Typeclass for `update_at_range`, overloaded for `Seq` and `RustArray`.
    The extraction emits `update_at_range` on both types; the `RustArray` overload
    threads the size proof so that the unsound `instCoeSeqRustArray` is not needed. -/
class UpdateAtRange (C : Type) (α : outParam Type) where
  doUpdateAtRange : C → core_models.ops.range.Range usize →
    rust_primitives.sequence.Seq α → RustM C

instance instUpdateAtRangeSeq {α : Type} :
    UpdateAtRange (rust_primitives.sequence.Seq α) α where
  doUpdateAtRange s r v :=
    if h : r._end.toNat ≤ s.val.size ∧ r.start.toNat ≤ r._end.toNat ∧
        v.val.size = r._end.toNat - r.start.toNat then
      let result := (s.val.extract 0 r.start.toNat) ++ v.val ++
        (s.val.extract r._end.toNat s.val.size)
      have hsz : result.size = s.val.size := by
        simp only [result, Array.size_append, Array.size_extract, Nat.min_self,
          Nat.min_eq_left (by omega : r.start.toNat ≤ s.val.size)]; omega
      pure ⟨result, by rw [hsz]; exact s.size_lt_usizeSize⟩
    else .fail .arrayOutOfBounds

instance instUpdateAtRangeArray {α : Type} {n : usize} :
    UpdateAtRange (RustArray α n) α where
  doUpdateAtRange s r v :=
    let arr := s.toVec.toArray
    if h : r._end.toNat ≤ arr.size ∧ r.start.toNat ≤ r._end.toNat ∧
        v.val.size = r._end.toNat - r.start.toNat then
      let result := (arr.extract 0 r.start.toNat) ++ v.val ++
        (arr.extract r._end.toNat arr.size)
      have harr : arr.size = n.toNat := s.toVec.size_toArray
      have hsz : result.size = n.toNat := by
        simp only [result, Array.size_append, Array.size_extract, Nat.min_self,
          Nat.min_eq_left (by omega : r.start.toNat ≤ arr.size)]; omega
      pure ⟨⟨result, hsz⟩⟩
    else .fail .arrayOutOfBounds

/-- Replace `s[r.start .. r.end]` with `v`. Requires matching lengths.
    Overloaded for `Seq` (returns `Seq`) and `RustArray` (returns `RustArray`). -/
def update_at_range {C : Type} {α : Type} [UpdateAtRange C α] (s : C)
    (r : core_models.ops.range.Range usize) (v : rust_primitives.sequence.Seq α) :
    RustM C :=
  UpdateAtRange.doUpdateAtRange s r v

@[irreducible] def update_at_range_from {S : Type}
    (s : S) (r : core_models.ops.range.RangeFrom usize) (v : S) :
    RustM S := sorry

end rust_primitives.hax.monomorphized_update_at

/-! ## `copy_from_slice` wrapper for specset "int"

The Hax library's `copy_from_slice` only has `@[hax_spec]` for specset "bv".
With specset "int", mvcgen cannot find a spec and falls back to unfolding,
causing OOM. This irreducible wrapper with `@[spec]` provides a spec that
mvcgen can use with any specset. Use `simp only [← copy_from_slice_u8_eq]`
before `hax_mvcgen` to substitute. -/

def copy_from_slice_u8 (s src : RustSlice u8) : RustM (RustSlice u8) :=
  core_models.slice.Impl.copy_from_slice u8 s src

theorem copy_from_slice_u8_eq (s src) :
    copy_from_slice_u8 s src = core_models.slice.Impl.copy_from_slice u8 s src := rfl

open Std.Do in
@[spec] theorem copy_from_slice_u8_spec (s src : RustSlice u8)
    (hlen : s.val.size = src.val.size) :
    ⦃ ⌜ True ⌝ ⦄ copy_from_slice_u8 s src ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  intro _; rw [copy_from_slice_u8_eq]
  unfold core_models.slice.Impl.copy_from_slice rust_primitives.mem.replace; simp

attribute [irreducible] copy_from_slice_u8

/-! ## `hax_lib.int` — integer-from-string literal -/

namespace hax_lib.int

@[irreducible] def Impl_7._unsafe_from_str (s : String) : RustM hax_lib.int.Int := sorry

end hax_lib.int
