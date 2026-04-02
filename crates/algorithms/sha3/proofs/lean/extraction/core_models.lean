
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import extraction.helpers
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace core_models.abstractions.bit

--  Represent a bit: `0` or `1`.
inductive Bit : Type
| Zero : Bit
| One : Bit

@[spec]
def Bit_cast_to_repr (x : Bit) : RustM isize := do
  match x with
    | (Bit.Zero ) => do (pure (0 : isize))
    | (Bit.One ) => do (pure (1 : isize))

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.clone.Clone Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.marker.Copy Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.marker.StructuralPartialEq Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Bit Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.cmp.PartialEq Bit Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.cmp.Eq Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.fmt.Debug Bit :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl.AssociatedTypes :
  core_models.convert.From.AssociatedTypes Bool Bit
  where

instance Impl : core_models.convert.From Bool Bit where
  _from := fun (bit : Bit) => do
    match bit with
      | (Bit.Zero ) => do (pure false)
      | (Bit.One ) => do (pure true)

@[reducible] instance Impl_8.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u8 Bit
  where

instance Impl_8 : core_models.convert.From u8 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM u8)

@[reducible] instance Impl_9.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u16 Bit
  where

instance Impl_9 : core_models.convert.From u16 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM u16)

@[reducible] instance Impl_10.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u32 Bit
  where

instance Impl_10 : core_models.convert.From u32 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM u32)

@[reducible] instance Impl_11.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u64 Bit
  where

instance Impl_11 : core_models.convert.From u64 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM u64)

@[reducible] instance Impl_12.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u128 Bit
  where

instance Impl_12 : core_models.convert.From u128 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM u128)

@[reducible] instance Impl_13.AssociatedTypes :
  core_models.convert.From.AssociatedTypes i8 Bit
  where

instance Impl_13 : core_models.convert.From i8 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM i8)

@[reducible] instance Impl_14.AssociatedTypes :
  core_models.convert.From.AssociatedTypes i16 Bit
  where

instance Impl_14 : core_models.convert.From i16 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM i16)

@[reducible] instance Impl_15.AssociatedTypes :
  core_models.convert.From.AssociatedTypes i32 Bit
  where

instance Impl_15 : core_models.convert.From i32 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM i32)

@[reducible] instance Impl_16.AssociatedTypes :
  core_models.convert.From.AssociatedTypes i64 Bit
  where

instance Impl_16 : core_models.convert.From i64 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM i64)

@[reducible] instance Impl_17.AssociatedTypes :
  core_models.convert.From.AssociatedTypes i128 Bit
  where

instance Impl_17 : core_models.convert.From i128 Bit where
  _from := fun (bit : Bit) => do
    (rust_primitives.hax.cast_op
      (← (core_models.convert.From._from Bool Bit bit)) :
      RustM i128)

@[reducible] instance Impl_1.AssociatedTypes :
  core_models.convert.From.AssociatedTypes Bit Bool
  where

instance Impl_1 : core_models.convert.From Bit Bool where
  _from := fun (b : Bool) => do
    match b with | false => do (pure Bit.Zero) | true => do (pure Bit.One)

--  A trait for types that represent machine integers.
class MachineInteger.AssociatedTypes (Self : Type) where

class MachineInteger (Self : Type)
  [associatedTypes : outParam (MachineInteger.AssociatedTypes (Self : Type))]
  where
  bits (Self) : (rust_primitives.hax.Tuple0 -> RustM u32)
  SIGNED (Self) : Bool

def ___2 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

end core_models.abstractions.bit


namespace core_models.abstractions.bitvec

def _ : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

--  An F* attribute that indiquates a rewritting lemma should be applied
def REWRITE_RULE : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

--  This function is useful only for verification in F*.
--  Used with `postprocess_rewrite`, this tactic:
--   1. Applies a series of rewrite rules (the lemmas marked with `REWRITE_RULE`)
--   2. Normalizes, bottom-up, every sub-expressions typed `BitVec<_>` inside the body of a function.
--  This tactic should be used on expressions that compute a _static_ permutation of bits.
@[spec]
def bitvec_postprocess_norm (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end core_models.abstractions.bitvec


namespace core_models.abstractions.bitvec.int_vec_interp

--  An F* attribute that marks an item as being an interpretation lemma.
def SIMPLIFICATION_LEMMA : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

def _ : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___1 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___2 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___3 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___4 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___5 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___6 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___7 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___8 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___9 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___10 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___11 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___12 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___13 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___14 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

def ___15 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

--  Normalize `from` calls that convert from one type to itself
def ___18 : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

end core_models.abstractions.bitvec.int_vec_interp


namespace core_models.abstractions.funarr

--  A fixed-size array wrapper with functional semantics and F* integration.
--
--  `FunArray<N, T>` represents an array of `T` values of length `N`, where `N` is a compile-time constant.
--  Internally, it uses a fixed-length array of `Option<T>` with a maximum capacity of 512 elements.
--  Unused elements beyond `N` are filled with `None`.
--
--  This type is integrated with F* through various `#[hax_lib::fstar::replace]` attributes to support
--  formal verification workflows.
structure FunArray (N : u64) (T : Type) where
  _0 : (RustArray (core_models.option.Option T) 512)

end core_models.abstractions.funarr


namespace core_models.abstractions.bitvec

--  A fixed-size bit vector type.
--
--  `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
--  stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
--
--  This type provides several utility methods for constructing and converting bit vectors:
--
--  The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
--  making the bit pattern more human-readable. The type also implements indexing,
--  allowing for easy access to individual bits.
structure BitVec (N : u64) where
  _0 :
    (core_models.abstractions.funarr.FunArray
      (N)
      core_models.abstractions.bit.Bit)

@[instance] opaque Impl_1.AssociatedTypes (N : u64) :
  core_models.clone.Clone.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 (N : u64) :
  core_models.clone.Clone (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes (N : u64) :
  core_models.marker.Copy.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl (N : u64) :
  core_models.marker.Copy (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes (N : u64) :
  core_models.marker.StructuralPartialEq.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 (N : u64) :
  core_models.marker.StructuralPartialEq (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes (N : u64) :
  core_models.cmp.PartialEq.AssociatedTypes (BitVec (N)) (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 (N : u64) :
  core_models.cmp.PartialEq (BitVec (N)) (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes (N : u64) :
  core_models.cmp.Eq.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 (N : u64) :
  core_models.cmp.Eq (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl_6.AssociatedTypes (N : u64) :
  core_models.ops.index.Index.AssociatedTypes (BitVec (N)) u64
  where
  Output := core_models.abstractions.bit.Bit

instance Impl_6 (N : u64) : core_models.ops.index.Index (BitVec (N)) u64 where
  index := fun (self : (BitVec (N))) (index : u64) => do
    (core_models.abstractions.funarr.Impl_5.get
      (N)
      core_models.abstractions.bit.Bit (BitVec._0 self) index)

@[spec]
def Impl_7.pointwise (self : (BitVec ((128 : u64)))) :
    RustM (BitVec ((128 : u64))) := do
  (Impl_9.from_fn ((128 : u64)) (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match i with
        | 0 => do self[(0 : u64)]_?
        | 1 => do self[(1 : u64)]_?
        | 2 => do self[(2 : u64)]_?
        | 3 => do self[(3 : u64)]_?
        | 4 => do self[(4 : u64)]_?
        | 5 => do self[(5 : u64)]_?
        | 6 => do self[(6 : u64)]_?
        | 7 => do self[(7 : u64)]_?
        | 8 => do self[(8 : u64)]_?
        | 9 => do self[(9 : u64)]_?
        | 10 => do self[(10 : u64)]_?
        | 11 => do self[(11 : u64)]_?
        | 12 => do self[(12 : u64)]_?
        | 13 => do self[(13 : u64)]_?
        | 14 => do self[(14 : u64)]_?
        | 15 => do self[(15 : u64)]_?
        | 16 => do self[(16 : u64)]_?
        | 17 => do self[(17 : u64)]_?
        | 18 => do self[(18 : u64)]_?
        | 19 => do self[(19 : u64)]_?
        | 20 => do self[(20 : u64)]_?
        | 21 => do self[(21 : u64)]_?
        | 22 => do self[(22 : u64)]_?
        | 23 => do self[(23 : u64)]_?
        | 24 => do self[(24 : u64)]_?
        | 25 => do self[(25 : u64)]_?
        | 26 => do self[(26 : u64)]_?
        | 27 => do self[(27 : u64)]_?
        | 28 => do self[(28 : u64)]_?
        | 29 => do self[(29 : u64)]_?
        | 30 => do self[(30 : u64)]_?
        | 31 => do self[(31 : u64)]_?
        | 32 => do self[(32 : u64)]_?
        | 33 => do self[(33 : u64)]_?
        | 34 => do self[(34 : u64)]_?
        | 35 => do self[(35 : u64)]_?
        | 36 => do self[(36 : u64)]_?
        | 37 => do self[(37 : u64)]_?
        | 38 => do self[(38 : u64)]_?
        | 39 => do self[(39 : u64)]_?
        | 40 => do self[(40 : u64)]_?
        | 41 => do self[(41 : u64)]_?
        | 42 => do self[(42 : u64)]_?
        | 43 => do self[(43 : u64)]_?
        | 44 => do self[(44 : u64)]_?
        | 45 => do self[(45 : u64)]_?
        | 46 => do self[(46 : u64)]_?
        | 47 => do self[(47 : u64)]_?
        | 48 => do self[(48 : u64)]_?
        | 49 => do self[(49 : u64)]_?
        | 50 => do self[(50 : u64)]_?
        | 51 => do self[(51 : u64)]_?
        | 52 => do self[(52 : u64)]_?
        | 53 => do self[(53 : u64)]_?
        | 54 => do self[(54 : u64)]_?
        | 55 => do self[(55 : u64)]_?
        | 56 => do self[(56 : u64)]_?
        | 57 => do self[(57 : u64)]_?
        | 58 => do self[(58 : u64)]_?
        | 59 => do self[(59 : u64)]_?
        | 60 => do self[(60 : u64)]_?
        | 61 => do self[(61 : u64)]_?
        | 62 => do self[(62 : u64)]_?
        | 63 => do self[(63 : u64)]_?
        | 64 => do self[(64 : u64)]_?
        | 65 => do self[(65 : u64)]_?
        | 66 => do self[(66 : u64)]_?
        | 67 => do self[(67 : u64)]_?
        | 68 => do self[(68 : u64)]_?
        | 69 => do self[(69 : u64)]_?
        | 70 => do self[(70 : u64)]_?
        | 71 => do self[(71 : u64)]_?
        | 72 => do self[(72 : u64)]_?
        | 73 => do self[(73 : u64)]_?
        | 74 => do self[(74 : u64)]_?
        | 75 => do self[(75 : u64)]_?
        | 76 => do self[(76 : u64)]_?
        | 77 => do self[(77 : u64)]_?
        | 78 => do self[(78 : u64)]_?
        | 79 => do self[(79 : u64)]_?
        | 80 => do self[(80 : u64)]_?
        | 81 => do self[(81 : u64)]_?
        | 82 => do self[(82 : u64)]_?
        | 83 => do self[(83 : u64)]_?
        | 84 => do self[(84 : u64)]_?
        | 85 => do self[(85 : u64)]_?
        | 86 => do self[(86 : u64)]_?
        | 87 => do self[(87 : u64)]_?
        | 88 => do self[(88 : u64)]_?
        | 89 => do self[(89 : u64)]_?
        | 90 => do self[(90 : u64)]_?
        | 91 => do self[(91 : u64)]_?
        | 92 => do self[(92 : u64)]_?
        | 93 => do self[(93 : u64)]_?
        | 94 => do self[(94 : u64)]_?
        | 95 => do self[(95 : u64)]_?
        | 96 => do self[(96 : u64)]_?
        | 97 => do self[(97 : u64)]_?
        | 98 => do self[(98 : u64)]_?
        | 99 => do self[(99 : u64)]_?
        | 100 => do self[(100 : u64)]_?
        | 101 => do self[(101 : u64)]_?
        | 102 => do self[(102 : u64)]_?
        | 103 => do self[(103 : u64)]_?
        | 104 => do self[(104 : u64)]_?
        | 105 => do self[(105 : u64)]_?
        | 106 => do self[(106 : u64)]_?
        | 107 => do self[(107 : u64)]_?
        | 108 => do self[(108 : u64)]_?
        | 109 => do self[(109 : u64)]_?
        | 110 => do self[(110 : u64)]_?
        | 111 => do self[(111 : u64)]_?
        | 112 => do self[(112 : u64)]_?
        | 113 => do self[(113 : u64)]_?
        | 114 => do self[(114 : u64)]_?
        | 115 => do self[(115 : u64)]_?
        | 116 => do self[(116 : u64)]_?
        | 117 => do self[(117 : u64)]_?
        | 118 => do self[(118 : u64)]_?
        | 119 => do self[(119 : u64)]_?
        | 120 => do self[(120 : u64)]_?
        | 121 => do self[(121 : u64)]_?
        | 122 => do self[(122 : u64)]_?
        | 123 => do self[(123 : u64)]_?
        | 124 => do self[(124 : u64)]_?
        | 125 => do self[(125 : u64)]_?
        | 126 => do self[(126 : u64)]_?
        | 127 => do self[(127 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def Impl_8.pointwise (self : (BitVec ((256 : u64)))) :
    RustM (BitVec ((256 : u64))) := do
  (Impl_9.from_fn ((256 : u64)) (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match i with
        | 0 => do self[(0 : u64)]_?
        | 1 => do self[(1 : u64)]_?
        | 2 => do self[(2 : u64)]_?
        | 3 => do self[(3 : u64)]_?
        | 4 => do self[(4 : u64)]_?
        | 5 => do self[(5 : u64)]_?
        | 6 => do self[(6 : u64)]_?
        | 7 => do self[(7 : u64)]_?
        | 8 => do self[(8 : u64)]_?
        | 9 => do self[(9 : u64)]_?
        | 10 => do self[(10 : u64)]_?
        | 11 => do self[(11 : u64)]_?
        | 12 => do self[(12 : u64)]_?
        | 13 => do self[(13 : u64)]_?
        | 14 => do self[(14 : u64)]_?
        | 15 => do self[(15 : u64)]_?
        | 16 => do self[(16 : u64)]_?
        | 17 => do self[(17 : u64)]_?
        | 18 => do self[(18 : u64)]_?
        | 19 => do self[(19 : u64)]_?
        | 20 => do self[(20 : u64)]_?
        | 21 => do self[(21 : u64)]_?
        | 22 => do self[(22 : u64)]_?
        | 23 => do self[(23 : u64)]_?
        | 24 => do self[(24 : u64)]_?
        | 25 => do self[(25 : u64)]_?
        | 26 => do self[(26 : u64)]_?
        | 27 => do self[(27 : u64)]_?
        | 28 => do self[(28 : u64)]_?
        | 29 => do self[(29 : u64)]_?
        | 30 => do self[(30 : u64)]_?
        | 31 => do self[(31 : u64)]_?
        | 32 => do self[(32 : u64)]_?
        | 33 => do self[(33 : u64)]_?
        | 34 => do self[(34 : u64)]_?
        | 35 => do self[(35 : u64)]_?
        | 36 => do self[(36 : u64)]_?
        | 37 => do self[(37 : u64)]_?
        | 38 => do self[(38 : u64)]_?
        | 39 => do self[(39 : u64)]_?
        | 40 => do self[(40 : u64)]_?
        | 41 => do self[(41 : u64)]_?
        | 42 => do self[(42 : u64)]_?
        | 43 => do self[(43 : u64)]_?
        | 44 => do self[(44 : u64)]_?
        | 45 => do self[(45 : u64)]_?
        | 46 => do self[(46 : u64)]_?
        | 47 => do self[(47 : u64)]_?
        | 48 => do self[(48 : u64)]_?
        | 49 => do self[(49 : u64)]_?
        | 50 => do self[(50 : u64)]_?
        | 51 => do self[(51 : u64)]_?
        | 52 => do self[(52 : u64)]_?
        | 53 => do self[(53 : u64)]_?
        | 54 => do self[(54 : u64)]_?
        | 55 => do self[(55 : u64)]_?
        | 56 => do self[(56 : u64)]_?
        | 57 => do self[(57 : u64)]_?
        | 58 => do self[(58 : u64)]_?
        | 59 => do self[(59 : u64)]_?
        | 60 => do self[(60 : u64)]_?
        | 61 => do self[(61 : u64)]_?
        | 62 => do self[(62 : u64)]_?
        | 63 => do self[(63 : u64)]_?
        | 64 => do self[(64 : u64)]_?
        | 65 => do self[(65 : u64)]_?
        | 66 => do self[(66 : u64)]_?
        | 67 => do self[(67 : u64)]_?
        | 68 => do self[(68 : u64)]_?
        | 69 => do self[(69 : u64)]_?
        | 70 => do self[(70 : u64)]_?
        | 71 => do self[(71 : u64)]_?
        | 72 => do self[(72 : u64)]_?
        | 73 => do self[(73 : u64)]_?
        | 74 => do self[(74 : u64)]_?
        | 75 => do self[(75 : u64)]_?
        | 76 => do self[(76 : u64)]_?
        | 77 => do self[(77 : u64)]_?
        | 78 => do self[(78 : u64)]_?
        | 79 => do self[(79 : u64)]_?
        | 80 => do self[(80 : u64)]_?
        | 81 => do self[(81 : u64)]_?
        | 82 => do self[(82 : u64)]_?
        | 83 => do self[(83 : u64)]_?
        | 84 => do self[(84 : u64)]_?
        | 85 => do self[(85 : u64)]_?
        | 86 => do self[(86 : u64)]_?
        | 87 => do self[(87 : u64)]_?
        | 88 => do self[(88 : u64)]_?
        | 89 => do self[(89 : u64)]_?
        | 90 => do self[(90 : u64)]_?
        | 91 => do self[(91 : u64)]_?
        | 92 => do self[(92 : u64)]_?
        | 93 => do self[(93 : u64)]_?
        | 94 => do self[(94 : u64)]_?
        | 95 => do self[(95 : u64)]_?
        | 96 => do self[(96 : u64)]_?
        | 97 => do self[(97 : u64)]_?
        | 98 => do self[(98 : u64)]_?
        | 99 => do self[(99 : u64)]_?
        | 100 => do self[(100 : u64)]_?
        | 101 => do self[(101 : u64)]_?
        | 102 => do self[(102 : u64)]_?
        | 103 => do self[(103 : u64)]_?
        | 104 => do self[(104 : u64)]_?
        | 105 => do self[(105 : u64)]_?
        | 106 => do self[(106 : u64)]_?
        | 107 => do self[(107 : u64)]_?
        | 108 => do self[(108 : u64)]_?
        | 109 => do self[(109 : u64)]_?
        | 110 => do self[(110 : u64)]_?
        | 111 => do self[(111 : u64)]_?
        | 112 => do self[(112 : u64)]_?
        | 113 => do self[(113 : u64)]_?
        | 114 => do self[(114 : u64)]_?
        | 115 => do self[(115 : u64)]_?
        | 116 => do self[(116 : u64)]_?
        | 117 => do self[(117 : u64)]_?
        | 118 => do self[(118 : u64)]_?
        | 119 => do self[(119 : u64)]_?
        | 120 => do self[(120 : u64)]_?
        | 121 => do self[(121 : u64)]_?
        | 122 => do self[(122 : u64)]_?
        | 123 => do self[(123 : u64)]_?
        | 124 => do self[(124 : u64)]_?
        | 125 => do self[(125 : u64)]_?
        | 126 => do self[(126 : u64)]_?
        | 127 => do self[(127 : u64)]_?
        | 128 => do self[(128 : u64)]_?
        | 129 => do self[(129 : u64)]_?
        | 130 => do self[(130 : u64)]_?
        | 131 => do self[(131 : u64)]_?
        | 132 => do self[(132 : u64)]_?
        | 133 => do self[(133 : u64)]_?
        | 134 => do self[(134 : u64)]_?
        | 135 => do self[(135 : u64)]_?
        | 136 => do self[(136 : u64)]_?
        | 137 => do self[(137 : u64)]_?
        | 138 => do self[(138 : u64)]_?
        | 139 => do self[(139 : u64)]_?
        | 140 => do self[(140 : u64)]_?
        | 141 => do self[(141 : u64)]_?
        | 142 => do self[(142 : u64)]_?
        | 143 => do self[(143 : u64)]_?
        | 144 => do self[(144 : u64)]_?
        | 145 => do self[(145 : u64)]_?
        | 146 => do self[(146 : u64)]_?
        | 147 => do self[(147 : u64)]_?
        | 148 => do self[(148 : u64)]_?
        | 149 => do self[(149 : u64)]_?
        | 150 => do self[(150 : u64)]_?
        | 151 => do self[(151 : u64)]_?
        | 152 => do self[(152 : u64)]_?
        | 153 => do self[(153 : u64)]_?
        | 154 => do self[(154 : u64)]_?
        | 155 => do self[(155 : u64)]_?
        | 156 => do self[(156 : u64)]_?
        | 157 => do self[(157 : u64)]_?
        | 158 => do self[(158 : u64)]_?
        | 159 => do self[(159 : u64)]_?
        | 160 => do self[(160 : u64)]_?
        | 161 => do self[(161 : u64)]_?
        | 162 => do self[(162 : u64)]_?
        | 163 => do self[(163 : u64)]_?
        | 164 => do self[(164 : u64)]_?
        | 165 => do self[(165 : u64)]_?
        | 166 => do self[(166 : u64)]_?
        | 167 => do self[(167 : u64)]_?
        | 168 => do self[(168 : u64)]_?
        | 169 => do self[(169 : u64)]_?
        | 170 => do self[(170 : u64)]_?
        | 171 => do self[(171 : u64)]_?
        | 172 => do self[(172 : u64)]_?
        | 173 => do self[(173 : u64)]_?
        | 174 => do self[(174 : u64)]_?
        | 175 => do self[(175 : u64)]_?
        | 176 => do self[(176 : u64)]_?
        | 177 => do self[(177 : u64)]_?
        | 178 => do self[(178 : u64)]_?
        | 179 => do self[(179 : u64)]_?
        | 180 => do self[(180 : u64)]_?
        | 181 => do self[(181 : u64)]_?
        | 182 => do self[(182 : u64)]_?
        | 183 => do self[(183 : u64)]_?
        | 184 => do self[(184 : u64)]_?
        | 185 => do self[(185 : u64)]_?
        | 186 => do self[(186 : u64)]_?
        | 187 => do self[(187 : u64)]_?
        | 188 => do self[(188 : u64)]_?
        | 189 => do self[(189 : u64)]_?
        | 190 => do self[(190 : u64)]_?
        | 191 => do self[(191 : u64)]_?
        | 192 => do self[(192 : u64)]_?
        | 193 => do self[(193 : u64)]_?
        | 194 => do self[(194 : u64)]_?
        | 195 => do self[(195 : u64)]_?
        | 196 => do self[(196 : u64)]_?
        | 197 => do self[(197 : u64)]_?
        | 198 => do self[(198 : u64)]_?
        | 199 => do self[(199 : u64)]_?
        | 200 => do self[(200 : u64)]_?
        | 201 => do self[(201 : u64)]_?
        | 202 => do self[(202 : u64)]_?
        | 203 => do self[(203 : u64)]_?
        | 204 => do self[(204 : u64)]_?
        | 205 => do self[(205 : u64)]_?
        | 206 => do self[(206 : u64)]_?
        | 207 => do self[(207 : u64)]_?
        | 208 => do self[(208 : u64)]_?
        | 209 => do self[(209 : u64)]_?
        | 210 => do self[(210 : u64)]_?
        | 211 => do self[(211 : u64)]_?
        | 212 => do self[(212 : u64)]_?
        | 213 => do self[(213 : u64)]_?
        | 214 => do self[(214 : u64)]_?
        | 215 => do self[(215 : u64)]_?
        | 216 => do self[(216 : u64)]_?
        | 217 => do self[(217 : u64)]_?
        | 218 => do self[(218 : u64)]_?
        | 219 => do self[(219 : u64)]_?
        | 220 => do self[(220 : u64)]_?
        | 221 => do self[(221 : u64)]_?
        | 222 => do self[(222 : u64)]_?
        | 223 => do self[(223 : u64)]_?
        | 224 => do self[(224 : u64)]_?
        | 225 => do self[(225 : u64)]_?
        | 226 => do self[(226 : u64)]_?
        | 227 => do self[(227 : u64)]_?
        | 228 => do self[(228 : u64)]_?
        | 229 => do self[(229 : u64)]_?
        | 230 => do self[(230 : u64)]_?
        | 231 => do self[(231 : u64)]_?
        | 232 => do self[(232 : u64)]_?
        | 233 => do self[(233 : u64)]_?
        | 234 => do self[(234 : u64)]_?
        | 235 => do self[(235 : u64)]_?
        | 236 => do self[(236 : u64)]_?
        | 237 => do self[(237 : u64)]_?
        | 238 => do self[(238 : u64)]_?
        | 239 => do self[(239 : u64)]_?
        | 240 => do self[(240 : u64)]_?
        | 241 => do self[(241 : u64)]_?
        | 242 => do self[(242 : u64)]_?
        | 243 => do self[(243 : u64)]_?
        | 244 => do self[(244 : u64)]_?
        | 245 => do self[(245 : u64)]_?
        | 246 => do self[(246 : u64)]_?
        | 247 => do self[(247 : u64)]_?
        | 248 => do self[(248 : u64)]_?
        | 249 => do self[(249 : u64)]_?
        | 250 => do self[(250 : u64)]_?
        | 251 => do self[(251 : u64)]_?
        | 252 => do self[(252 : u64)]_?
        | 253 => do self[(253 : u64)]_?
        | 254 => do self[(254 : u64)]_?
        | 255 => do self[(255 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM core_models.abstractions.bit.Bit)))

--  Folds over the array, accumulating a result.
--
--  # Arguments
--  * `init` - The initial value of the accumulator.
--  * `f` - A function combining the accumulator and each element.
@[spec]
def Impl_10.fold (N : u64) (A : Type)
    (self : (BitVec (N)))
    (init : A)
    (f : (A -> core_models.abstractions.bit.Bit -> RustM A)) :
    RustM A := do
  (core_models.abstractions.funarr.Impl_5.fold
    (N)
    core_models.abstractions.bit.Bit
    A (BitVec._0 self) init f)

end core_models.abstractions.bitvec


namespace core_models.abstractions.bitvec.int_vec_interp

-- i32 vectors of size 8
abbrev i32x8 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)

-- Conversion from i32 vectors of size 8to  bit vectors of size 256
opaque _.Impl.from_i32x8
    (iv : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to i32 vectors of size 8
opaque _.Impl.to_i32x8
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)

-- i64 vectors of size 4
abbrev i64x4 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)

-- Conversion from i64 vectors of size 4to  bit vectors of size 256
opaque ___1.Impl.from_i64x4
    (iv : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to i64 vectors of size 4
opaque ___1.Impl.to_i64x4
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)

-- i16 vectors of size 16
abbrev i16x16 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)

-- Conversion from i16 vectors of size 16to  bit vectors of size 256
opaque ___2.Impl.from_i16x16
    (iv : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to i16 vectors of size 16
opaque ___2.Impl.to_i16x16
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)

-- i128 vectors of size 2
abbrev i128x2 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((2 : u64)) i128)

-- Conversion from i128 vectors of size 2to  bit vectors of size 256
opaque ___3.Impl.from_i128x2
    (iv : (core_models.abstractions.funarr.FunArray ((2 : u64)) i128)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to i128 vectors of size 2
opaque ___3.Impl.to_i128x2
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i128)

-- i8 vectors of size 32
abbrev i8x32 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((32 : u64)) i8)

-- Conversion from i8 vectors of size 32to  bit vectors of size 256
opaque ___4.Impl.from_i8x32
    (iv : (core_models.abstractions.funarr.FunArray ((32 : u64)) i8)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to i8 vectors of size 32
opaque ___4.Impl.to_i8x32
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((32 : u64)) i8)

-- u32 vectors of size 8
abbrev u32x8 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)

-- Conversion from u32 vectors of size 8to  bit vectors of size 256
opaque ___5.Impl.from_u32x8
    (iv : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to u32 vectors of size 8
opaque ___5.Impl.to_u32x8
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)

-- u64 vectors of size 4
abbrev u64x4 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((4 : u64)) u64)

-- Conversion from u64 vectors of size 4to  bit vectors of size 256
opaque ___6.Impl.from_u64x4
    (iv : (core_models.abstractions.funarr.FunArray ((4 : u64)) u64)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to u64 vectors of size 4
opaque ___6.Impl.to_u64x4
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) u64)

-- u16 vectors of size 16
abbrev u16x16 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((16 : u64)) u16)

-- Conversion from u16 vectors of size 16to  bit vectors of size 256
opaque ___7.Impl.from_u16x16
    (iv : (core_models.abstractions.funarr.FunArray ((16 : u64)) u16)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

-- Conversion from bit vectors of size 256 to u16 vectors of size 16
opaque ___7.Impl.to_u16x16
    (bv : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) u16)

-- i32 vectors of size 4
abbrev i32x4 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((4 : u64)) i32)

-- Conversion from i32 vectors of size 4to  bit vectors of size 128
opaque ___8.Impl.from_i32x4
    (iv : (core_models.abstractions.funarr.FunArray ((4 : u64)) i32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to i32 vectors of size 4
opaque ___8.Impl.to_i32x4
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i32)

-- i64 vectors of size 2
abbrev i64x2 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((2 : u64)) i64)

-- Conversion from i64 vectors of size 2to  bit vectors of size 128
opaque ___9.Impl.from_i64x2
    (iv : (core_models.abstractions.funarr.FunArray ((2 : u64)) i64)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to i64 vectors of size 2
opaque ___9.Impl.to_i64x2
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i64)

-- i16 vectors of size 8
abbrev i16x8 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)

-- Conversion from i16 vectors of size 8to  bit vectors of size 128
opaque ___10.Impl.from_i16x8
    (iv : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to i16 vectors of size 8
opaque ___10.Impl.to_i16x8
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)

-- i128 vectors of size 1
abbrev i128x1 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((1 : u64)) i128)

-- Conversion from i128 vectors of size 1to  bit vectors of size 128
opaque ___11.Impl.from_i128x1
    (iv : (core_models.abstractions.funarr.FunArray ((1 : u64)) i128)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to i128 vectors of size 1
opaque ___11.Impl.to_i128x1
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((1 : u64)) i128)

-- i8 vectors of size 16
abbrev i8x16 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((16 : u64)) i8)

-- Conversion from i8 vectors of size 16to  bit vectors of size 128
opaque ___12.Impl.from_i8x16
    (iv : (core_models.abstractions.funarr.FunArray ((16 : u64)) i8)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to i8 vectors of size 16
opaque ___12.Impl.to_i8x16
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i8)

-- u32 vectors of size 4
abbrev u32x4 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((4 : u64)) u32)

-- Conversion from u32 vectors of size 4to  bit vectors of size 128
opaque ___13.Impl.from_u32x4
    (iv : (core_models.abstractions.funarr.FunArray ((4 : u64)) u32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to u32 vectors of size 4
opaque ___13.Impl.to_u32x4
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) u32)

-- u64 vectors of size 2
abbrev u64x2 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((2 : u64)) u64)

-- Conversion from u64 vectors of size 2to  bit vectors of size 128
opaque ___14.Impl.from_u64x2
    (iv : (core_models.abstractions.funarr.FunArray ((2 : u64)) u64)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to u64 vectors of size 2
opaque ___14.Impl.to_u64x2
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) u64)

-- u16 vectors of size 8
abbrev u16x8 :
  Type :=
  (core_models.abstractions.funarr.FunArray ((8 : u64)) u16)

-- Conversion from u16 vectors of size 8to  bit vectors of size 128
opaque ___15.Impl.from_u16x8
    (iv : (core_models.abstractions.funarr.FunArray ((8 : u64)) u16)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

-- Conversion from bit vectors of size 128 to u16 vectors of size 8
opaque ___15.Impl.to_u16x8
    (bv : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) u16)

@[spec]
def Impl.into_i32x8
    (self : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let value : i64 ←
        (core_models.abstractions.funarr.Impl_5.get ((4 : u64)) i64
          self
          (← (i /? (2 : u64))));
      (rust_primitives.hax.cast_op
        (← if (← ((← (i %? (2 : u64))) ==? (0 : u64))) then do
          (pure value)
        else do
          (value >>>? (32 : i32))) :
        RustM i32) :
      RustM i32)))

@[spec]
def Impl_1.into_i64x4
    (self : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let low : u64 ←
        (rust_primitives.hax.cast_op
          (← (rust_primitives.hax.cast_op
            (← (core_models.abstractions.funarr.Impl_5.get ((8 : u64)) i32
              self
              (← ((2 : u64) *? i)))) :
            RustM u32)) :
          RustM u64);
      let high : i64 ←
        (rust_primitives.hax.cast_op
          (← (core_models.abstractions.funarr.Impl_5.get ((8 : u64)) i32
            self
            (← ((← ((2 : u64) *? i)) +? (1 : u64))))) :
          RustM i64);
      ((← (high <<<? (32 : i32)))
        |||? (← (rust_primitives.hax.cast_op low : RustM i64))) :
      RustM i64)))

@[reducible] instance Impl_2.AssociatedTypes :
  core_models.convert.From.AssociatedTypes
  (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)
  (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)
  where

instance Impl_2 :
  core_models.convert.From
  (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)
  (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)
  where
  _from :=
    fun (vec : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) => do
    (Impl.into_i32x8 vec)

--  Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
--  yields the same result as directly converting the `i64x4` into an `i32x8`.
opaque lemma_rewrite_i64x4_bv_i32x8
    (bv : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM rust_primitives.hax.Tuple0

--  Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
--  yields the same result as directly converting the `i64x4` into an `i32x8`.
opaque lemma_rewrite_i32x8_bv_i64x4
    (bv : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM rust_primitives.hax.Tuple0

end core_models.abstractions.bitvec.int_vec_interp


namespace core_models.abstractions.funarr

@[instance] opaque Impl_1.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.clone.Clone T ] :
  core_models.clone.Clone.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (N : u64)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.clone.Clone T ] :
  core_models.clone.Clone (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.marker.Copy T ] :
  core_models.marker.Copy.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl
  (N : u64)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.marker.Copy T ] :
  core_models.marker.Copy (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes (N : u64) (T : Type) :
  core_models.marker.StructuralPartialEq.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 (N : u64) (T : Type) :
  core_models.marker.StructuralPartialEq (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    T
    T]
  [trait_constr_Impl_4_i0 : core_models.cmp.PartialEq T T ] :
  core_models.cmp.PartialEq.AssociatedTypes (FunArray (N) T) (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4
  (N : u64)
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    T
    T]
  [trait_constr_Impl_4_i0 : core_models.cmp.PartialEq T T ] :
  core_models.cmp.PartialEq (FunArray (N) T) (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    T]
  [trait_constr_Impl_2_i0 : core_models.cmp.Eq T ] :
  core_models.cmp.Eq.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2
  (N : u64)
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    T]
  [trait_constr_Impl_2_i0 : core_models.cmp.Eq T ] :
  core_models.cmp.Eq (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl_11.AssociatedTypes (N : u64) (T : Type) :
  core_models.ops.index.Index.AssociatedTypes (FunArray (N) T) u64
  where
  Output := T

instance Impl_11 (N : u64) (T : Type) :
  core_models.ops.index.Index (FunArray (N) T) u64
  where
  index := fun (self : (FunArray (N) T)) (index : u64) => do
    (Impl_5.get (N) T self index)

end core_models.abstractions.funarr


namespace core_models.abstractions.bitvec

def Impl_10.chunked_shift.chunked_shift (N : u64) (CHUNK : u64) (SHIFTS : u64)
    (bitvec : (BitVec (N)))
    (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128)) :
    RustM (BitVec (N)) := do
  (Impl_9.from_fn (N) (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      let nth_bit : u64 ← (i %? CHUNK);
      let nth_chunk : u64 ← (i /? CHUNK);
      let _ ←
        (hax_lib.assert_prop
          (← (hax_lib.prop.constructors.from_bool
            (← (rust_primitives.hax.int.le
              (← (rust_primitives.hax.int.from_machine nth_chunk))
              (← (rust_primitives.hax.int.sub
                (← (rust_primitives.hax.int.from_machine SHIFTS))
                (← (hax_lib.int.Impl_7._unsafe_from_str "1")))))))));
      let _ := rust_primitives.hax.Tuple0.mk;
      let _ ←
        (hax_lib.assert_prop
          (← (hax_lib.prop.constructors.from_bool
            (← (rust_primitives.hax.int.le
              (← (rust_primitives.hax.int.mul
                (← (rust_primitives.hax.int.from_machine nth_chunk))
                (← (rust_primitives.hax.int.from_machine CHUNK))))
              (← (rust_primitives.hax.int.mul
                (← (rust_primitives.hax.int.sub
                  (← (rust_primitives.hax.int.from_machine SHIFTS))
                  (← (hax_lib.int.Impl_7._unsafe_from_str "1"))))
                (← (rust_primitives.hax.int.from_machine CHUNK)))))))));
      let _ := rust_primitives.hax.Tuple0.mk;
      let shift : i128 ←
        if (← (nth_chunk <? SHIFTS)) then do
          shl[nth_chunk]_?
        else do
          (pure (0 : i128));
      let local_index : i128 ←
        (core_models.num.Impl_4.wrapping_sub
          (← (rust_primitives.hax.cast_op nth_bit : RustM i128))
          shift);
      if
      (← ((← (local_index
          <? (← (rust_primitives.hax.cast_op CHUNK : RustM i128))))
        &&? (← (local_index >=? (0 : i128))))) then do
        let local_index : u64 ←
          (rust_primitives.hax.cast_op local_index : RustM u64);
        let _ ←
          (hax_lib.assert_prop
            (← (hax_lib.prop.constructors.from_bool
              (← (rust_primitives.hax.int.lt
                (← (rust_primitives.hax.int.add
                  (← (rust_primitives.hax.int.mul
                    (← (rust_primitives.hax.int.from_machine nth_chunk))
                    (← (rust_primitives.hax.int.from_machine CHUNK))))
                  (← (rust_primitives.hax.int.from_machine local_index))))
                (← (rust_primitives.hax.int.mul
                  (← (rust_primitives.hax.int.from_machine SHIFTS))
                  (← (rust_primitives.hax.int.from_machine CHUNK)))))))));
        let _ := rust_primitives.hax.Tuple0.mk;
        bitvec[(← ((← (nth_chunk *? CHUNK)) +? local_index))]_?
      else do
        (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_10.chunked_shift.chunked_shift.spec
      (N : u64)
      (CHUNK : u64)
      (SHIFTS : u64)
      (bitvec : (BitVec (N)))
      (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128)) :
    Spec
      (requires := do
        ((← (CHUNK >? (0 : u64)))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.mul
              (← (rust_primitives.hax.int.from_machine CHUNK))
              (← (rust_primitives.hax.int.from_machine SHIFTS))))
            (← (rust_primitives.hax.int.from_machine N))))))
      (ensures := fun _ => pure True)
      (Impl_10.chunked_shift.chunked_shift
        (N : u64)
        (CHUNK : u64)
        (SHIFTS : u64)
        (bitvec : (BitVec (N)))
        (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_10.chunked_shift.chunked_shift] <;> bv_decide
}

def Impl_10.chunked_shift (N : u64) (CHUNK : u64) (SHIFTS : u64)
    (self : (BitVec (N)))
    (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128)) :
    RustM (BitVec (N)) := do
  (Impl_10.chunked_shift.chunked_shift (N) (CHUNK) (SHIFTS) self shl)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_10.chunked_shift.spec (N : u64) (CHUNK : u64) (SHIFTS : u64)
      (self : (BitVec (N)))
      (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128)) :
    Spec
      (requires := do
        ((← (CHUNK >? (0 : u64)))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.mul
              (← (rust_primitives.hax.int.from_machine CHUNK))
              (← (rust_primitives.hax.int.from_machine SHIFTS))))
            (← (rust_primitives.hax.int.from_machine N))))))
      (ensures := fun _ => pure True)
      (Impl_10.chunked_shift
        (N : u64)
        (CHUNK : u64)
        (SHIFTS : u64)
        (self : (BitVec (N)))
        (shl : (core_models.abstractions.funarr.FunArray (SHIFTS) i128))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_10.chunked_shift] <;> bv_decide
}

end core_models.abstractions.bitvec


namespace core_models.abstractions.funarr

@[spec]
def Impl_6.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : core_models.marker.Copy T ]
    (self : (FunArray ((4 : u64)) T)) :
    RustM (FunArray ((4 : u64)) T) := do
  (Impl_5.from_fn ((4 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => do self[(0 : u64)]_?
        | 1 => do self[(1 : u64)]_?
        | 2 => do self[(2 : u64)]_?
        | 3 => do self[(3 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

@[spec]
def Impl_7.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : core_models.marker.Copy T ]
    (self : (FunArray ((8 : u64)) T)) :
    RustM (FunArray ((8 : u64)) T) := do
  (Impl_5.from_fn ((8 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => do self[(0 : u64)]_?
        | 1 => do self[(1 : u64)]_?
        | 2 => do self[(2 : u64)]_?
        | 3 => do self[(3 : u64)]_?
        | 4 => do self[(4 : u64)]_?
        | 5 => do self[(5 : u64)]_?
        | 6 => do self[(6 : u64)]_?
        | 7 => do self[(7 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

@[spec]
def Impl_8.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : core_models.marker.Copy T ]
    (self : (FunArray ((16 : u64)) T)) :
    RustM (FunArray ((16 : u64)) T) := do
  (Impl_5.from_fn ((16 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => do self[(0 : u64)]_?
        | 1 => do self[(1 : u64)]_?
        | 2 => do self[(2 : u64)]_?
        | 3 => do self[(3 : u64)]_?
        | 4 => do self[(4 : u64)]_?
        | 5 => do self[(5 : u64)]_?
        | 6 => do self[(6 : u64)]_?
        | 7 => do self[(7 : u64)]_?
        | 8 => do self[(8 : u64)]_?
        | 9 => do self[(9 : u64)]_?
        | 10 => do self[(10 : u64)]_?
        | 11 => do self[(11 : u64)]_?
        | 12 => do self[(12 : u64)]_?
        | 13 => do self[(13 : u64)]_?
        | 14 => do self[(14 : u64)]_?
        | 15 => do self[(15 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

end core_models.abstractions.funarr


namespace core_models.core_arch.x86.interpretations.int_vec

@[spec]
def _mm256_set1_epi32 (x : i32) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32) (fun _ => (do (pure x) : RustM i32)))

@[spec]
def i32_extended64_mul (x : i32) (y : i32) : RustM i64 := do
  ((← (rust_primitives.hax.cast_op x : RustM i64))
    *? (← (rust_primitives.hax.cast_op y : RustM i64)))

@[spec]
def _mm256_mul_epi32
    (x : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (y : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      (i32_extended64_mul
        (← x[(← (i *? (2 : u64)))]_?)
        (← y[(← (i *? (2 : u64)))]_?)) :
      RustM i64)))

@[spec]
def _mm256_sub_epi32
    (x : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (y : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (core_models.num.Impl_2.wrapping_sub (← x[i]_?) (← y[i]_?)) : RustM i32)))

@[spec]
def _mm256_shuffle_epi32 (CONTROL : i32)
    (x : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  let indexes : (core_models.abstractions.funarr.FunArray ((4 : u64)) u64) ←
    (core_models.abstractions.funarr.Impl_5.from_fn
      ((4 : u64))
      u64
      (u64 -> RustM u64)
      (fun i =>
        (do
        (rust_primitives.hax.cast_op
          (← ((← (CONTROL >>>? (← (i *? (2 : u64))))) %? (4 : i32))) :
          RustM u64) :
        RustM u64)));
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (i <? (4 : u64))) then do
        x[(← indexes[i]_?)]_?
      else do
        x[(← ((4 : u64) +? (← indexes[(← (i -? (4 : u64)))]_?)))]_? :
      RustM i32)))

@[spec]
def _mm256_blend_epi32 (CONTROL : i32)
    (x : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (y : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← ((← (CONTROL >>>? i)) %? (2 : i32))) ==? (0 : i32))) then do
        x[i]_?
      else do
        y[i]_? :
      RustM i32)))

@[spec]
def _mm256_setzero_si256 (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun _ =>
      (do
      (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_set_m128i
    (hi : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (lo : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      if (← (i <? (128 : u64))) then do
        lo[i]_?
      else do
        hi[(← (i -? (128 : u64)))]_? :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_set1_epi16 (a : i16) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16) (fun _ => (do (pure a) : RustM i16)))

@[spec]
def _mm_set1_epi16 (a : i16) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16) (fun _ => (do (pure a) : RustM i16)))

@[spec]
def _mm_set_epi32 (e3 : i32) (e2 : i32) (e1 : i32) (e0 : i32) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => do (pure e0)
        | 1 => do (pure e1)
        | 2 => do (pure e2)
        | 3 => do (pure e3)
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

@[spec]
def _mm_add_epi16
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (core_models.num.Impl_1.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i16)))

@[spec]
def _mm256_add_epi16
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (core_models.num.Impl_1.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i16)))

@[spec]
def _mm256_add_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (core_models.num.Impl_2.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i32)))

@[spec]
def _mm256_add_epi64
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64))
    (b : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      (core_models.num.Impl_3.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i64)))

@[spec]
def _mm256_abs_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← a[i]_?) ==? core_models.num.Impl_2.MIN)) then do
        a[i]_?
      else do
        (core_models.num.Impl_2.abs (← a[i]_?)) :
      RustM i32)))

@[spec]
def _mm256_sub_epi16
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (core_models.num.Impl_1.wrapping_sub (← a[i]_?) (← b[i]_?)) : RustM i16)))

@[spec]
def _mm_sub_epi16
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (core_models.num.Impl_1.wrapping_sub (← a[i]_?) (← b[i]_?)) : RustM i16)))

@[spec]
def _mm_mullo_epi16
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (pure (rust_primitives.hax.Tuple2._0
        (← (core_models.num.Impl_1.overflowing_mul (← a[i]_?) (← b[i]_?))))) :
      RustM i16)))

@[spec]
def _mm256_cmpgt_epi16
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if (← ((← a[i]_?) >? (← b[i]_?))) then do
        (pure (-1 : i16))
      else do
        (pure (0 : i16)) :
      RustM i16)))

@[spec]
def _mm256_cmpgt_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← a[i]_?) >? (← b[i]_?))) then do
        (pure (-1 : i32))
      else do
        (pure (0 : i32)) :
      RustM i32)))

@[spec]
def _mm256_cmpeq_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← a[i]_?) ==? (← b[i]_?))) then do
        (pure (-1 : i32))
      else do
        (pure (0 : i32)) :
      RustM i32)))

@[spec]
def _mm256_sign_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← b[i]_?) <? (0 : i32))) then do
        if (← ((← a[i]_?) ==? core_models.num.Impl_2.MIN)) then do
          a[i]_?
        else do
          (-? (← a[i]_?))
      else do
        if (← ((← b[i]_?) >? (0 : i32))) then do a[i]_? else do (pure (0 : i32))
      :
      RustM i32)))

@[spec]
def _mm256_castsi256_ps
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (pure a)

@[spec]
def _mm256_castps_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (pure a)

@[spec]
def _mm256_movemask_ps
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM i32 := do
  let a0 : i32 ←
    if (← ((← a[(0 : u64)]_?) <? (0 : i32))) then do
      (pure (1 : i32))
    else do
      (pure (0 : i32));
  let a1 : i32 ←
    if (← ((← a[(1 : u64)]_?) <? (0 : i32))) then do
      (pure (2 : i32))
    else do
      (pure (0 : i32));
  let a2 : i32 ←
    if (← ((← a[(2 : u64)]_?) <? (0 : i32))) then do
      (pure (4 : i32))
    else do
      (pure (0 : i32));
  let a3 : i32 ←
    if (← ((← a[(3 : u64)]_?) <? (0 : i32))) then do
      (pure (8 : i32))
    else do
      (pure (0 : i32));
  let a4 : i32 ←
    if (← ((← a[(4 : u64)]_?) <? (0 : i32))) then do
      (pure (16 : i32))
    else do
      (pure (0 : i32));
  let a5 : i32 ←
    if (← ((← a[(5 : u64)]_?) <? (0 : i32))) then do
      (pure (32 : i32))
    else do
      (pure (0 : i32));
  let a6 : i32 ←
    if (← ((← a[(6 : u64)]_?) <? (0 : i32))) then do
      (pure (64 : i32))
    else do
      (pure (0 : i32));
  let a7 : i32 ←
    if (← ((← a[(7 : u64)]_?) <? (0 : i32))) then do
      (pure (128 : i32))
    else do
      (pure (0 : i32));
  ((← ((← ((← ((← ((← ((← (a0 +? a1)) +? a2)) +? a3)) +? a4)) +? a5)) +? a6))
    +? a7)

@[spec]
def _mm_mulhi_epi16
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (rust_primitives.hax.cast_op
        (← ((← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM i32))
            *? (← (rust_primitives.hax.cast_op (← b[i]_?) : RustM i32))))
          >>>? (16 : i32))) :
        RustM i16) :
      RustM i16)))

@[spec]
def _mm256_mullo_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (pure (rust_primitives.hax.Tuple2._0
        (← (core_models.num.Impl_2.overflowing_mul (← a[i]_?) (← b[i]_?))))) :
      RustM i32)))

@[spec]
def _mm256_mulhi_epi16
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (rust_primitives.hax.cast_op
        (← ((← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM i32))
            *? (← (rust_primitives.hax.cast_op (← b[i]_?) : RustM i32))))
          >>>? (16 : i32))) :
        RustM i16) :
      RustM i16)))

@[spec]
def _mm256_mul_epu32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) u64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    u64
    (u64 -> RustM u64)
    (fun i =>
      (do
      ((← (rust_primitives.hax.cast_op
          (← a[(← (i *? (2 : u64)))]_?) :
          RustM u64))
        *? (← (rust_primitives.hax.cast_op
          (← b[(← (i *? (2 : u64)))]_?) :
          RustM u64))) :
      RustM u64)))

@[spec]
def _mm256_and_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match (rust_primitives.hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(core_models.abstractions.bit.Bit.One ),
           (core_models.abstractions.bit.Bit.One )⟩ => do
          (pure core_models.abstractions.bit.Bit.One)
        | _ => do (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_or_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match (rust_primitives.hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(core_models.abstractions.bit.Bit.Zero ),
           (core_models.abstractions.bit.Bit.Zero )⟩ => do
          (pure core_models.abstractions.bit.Bit.Zero)
        | _ => do (pure core_models.abstractions.bit.Bit.One) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_testz_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM i32 := do
  let c : (core_models.abstractions.bitvec.BitVec ((256 : u64))) ←
    (core_models.abstractions.bitvec.Impl_9.from_fn
      ((256 : u64))
      (u64 -> RustM core_models.abstractions.bit.Bit)
      (fun i =>
        (do
        match (rust_primitives.hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
          | ⟨(core_models.abstractions.bit.Bit.One ),
             (core_models.abstractions.bit.Bit.One )⟩ => do
            (pure core_models.abstractions.bit.Bit.One)
          | _ => do (pure core_models.abstractions.bit.Bit.Zero) :
        RustM core_models.abstractions.bit.Bit)));
  let all_zero : Bool ←
    (core_models.abstractions.bitvec.Impl_10.fold ((256 : u64)) Bool
      c
      true
      (fun acc bit =>
        (do
        (acc
          &&? (← (core_models.cmp.PartialEq.eq
            core_models.abstractions.bit.Bit
            core_models.abstractions.bit.Bit
            bit
            core_models.abstractions.bit.Bit.Zero))) :
        RustM Bool)));
  if all_zero then do (pure (1 : i32)) else do (pure (0 : i32))

@[spec]
def _mm256_xor_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match (rust_primitives.hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(core_models.abstractions.bit.Bit.Zero ),
           (core_models.abstractions.bit.Bit.Zero )⟩ => do
          (pure core_models.abstractions.bit.Bit.Zero)
        | ⟨(core_models.abstractions.bit.Bit.One ),
           (core_models.abstractions.bit.Bit.One )⟩ => do
          (pure core_models.abstractions.bit.Bit.Zero)
        | _ => do (pure core_models.abstractions.bit.Bit.One) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_srai_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (15 : i32))) then do
        if (← ((← a[i]_?) <? (0 : i16))) then do
          (pure (-1 : i16))
        else do
          (pure (0 : i16))
      else do
        ((← a[i]_?) >>>? imm8) :
      RustM i16)))

@[spec]
def _mm256_srai_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (31 : i32))) then do
        if (← ((← a[i]_?) <? (0 : i32))) then do
          (pure (-1 : i32))
        else do
          (pure (0 : i32))
      else do
        ((← a[i]_?) >>>? imm8) :
      RustM i32)))

@[spec]
def _mm256_srli_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (15 : i32))) then do
        (pure (0 : i16))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u16))
            >>>? imm8)) :
          RustM i16) :
      RustM i16)))

@[spec]
def _mm256_srli_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (31 : i32))) then do
        (pure (0 : i32))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u32))
            >>>? imm8)) :
          RustM i32) :
      RustM i32)))

@[spec]
def _mm_srli_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((2 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((2 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (63 : i32))) then do
        (pure (0 : i64))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u64))
            >>>? imm8)) :
          RustM i64) :
      RustM i64)))

@[spec]
def _mm256_slli_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (core_models.num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (imm8 >? (31 : i32))) then do
        (pure (0 : i32))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u32))
            <<<? imm8)) :
          RustM i32) :
      RustM i32)))

@[spec]
def _mm256_permute4x64_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  let indexes : (core_models.abstractions.funarr.FunArray ((4 : u64)) u64) ←
    (core_models.abstractions.funarr.Impl_5.from_fn
      ((4 : u64))
      u64
      (u64 -> RustM u64)
      (fun i =>
        (do
        (rust_primitives.hax.cast_op
          (← ((← (IMM8 >>>? (← (i *? (2 : u64))))) %? (4 : i32))) :
          RustM u64) :
        RustM u64)));
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64) (fun i => (do a[(← indexes[i]_?)]_? : RustM i64)))

@[spec]
def _mm256_unpackhi_epi64
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64))
    (b : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => do a[(1 : u64)]_?
        | 1 => do b[(1 : u64)]_?
        | 2 => do a[(3 : u64)]_?
        | 3 => do b[(3 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

@[spec]
def _mm256_unpacklo_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => do a[(0 : u64)]_?
        | 1 => do b[(0 : u64)]_?
        | 2 => do a[(1 : u64)]_?
        | 3 => do b[(1 : u64)]_?
        | 4 => do a[(4 : u64)]_?
        | 5 => do b[(4 : u64)]_?
        | 6 => do a[(5 : u64)]_?
        | 7 => do b[(5 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

@[spec]
def _mm256_unpackhi_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => do a[(2 : u64)]_?
        | 1 => do b[(2 : u64)]_?
        | 2 => do a[(3 : u64)]_?
        | 3 => do b[(3 : u64)]_?
        | 4 => do a[(6 : u64)]_?
        | 5 => do b[(6 : u64)]_?
        | 6 => do a[(7 : u64)]_?
        | 7 => do b[(7 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

@[spec]
def _mm256_castsi128_si256
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      if (← (i <? (128 : u64))) then do
        a[i]_?
      else do
        (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_cvtepi16_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do (rust_primitives.hax.cast_op (← a[i]_?) : RustM i32) : RustM i32)))

@[spec]
def _mm_packs_epi16
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i8) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i8
    (u64 -> RustM i8)
    (fun i =>
      (do
      if (← (i <? (8 : u64))) then do
        if
        (← ((← a[i]_?)
          >? (← (rust_primitives.hax.cast_op
            core_models.num.Impl.MAX :
            RustM i16)))) then do
          (pure core_models.num.Impl.MAX)
        else do
          if
          (← ((← a[i]_?)
            <? (← (rust_primitives.hax.cast_op
              core_models.num.Impl.MIN :
              RustM i16)))) then do
            (pure core_models.num.Impl.MIN)
          else do
            (rust_primitives.hax.cast_op (← a[i]_?) : RustM i8)
      else do
        if
        (← ((← b[(← (i -? (8 : u64)))]_?)
          >? (← (rust_primitives.hax.cast_op
            core_models.num.Impl.MAX :
            RustM i16)))) then do
          (pure core_models.num.Impl.MAX)
        else do
          if
          (← ((← b[(← (i -? (8 : u64)))]_?)
            <? (← (rust_primitives.hax.cast_op
              core_models.num.Impl.MIN :
              RustM i16)))) then do
            (pure core_models.num.Impl.MIN)
          else do
            (rust_primitives.hax.cast_op
              (← b[(← (i -? (8 : u64)))]_?) :
              RustM i8) :
      RustM i8)))

@[spec]
def _mm256_packs_epi32
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if (← (i <? (4 : u64))) then do
        if
        (← ((← a[i]_?)
          >? (← (rust_primitives.hax.cast_op
            core_models.num.Impl_1.MAX :
            RustM i32)))) then do
          (pure core_models.num.Impl_1.MAX)
        else do
          if
          (← ((← a[i]_?)
            <? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_1.MIN :
              RustM i32)))) then do
            (pure core_models.num.Impl_1.MIN)
          else do
            (rust_primitives.hax.cast_op (← a[i]_?) : RustM i16)
      else do
        if (← (i <? (8 : u64))) then do
          if
          (← ((← b[(← (i -? (4 : u64)))]_?)
            >? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_1.MAX :
              RustM i32)))) then do
            (pure core_models.num.Impl_1.MAX)
          else do
            if
            (← ((← b[(← (i -? (4 : u64)))]_?)
              <? (← (rust_primitives.hax.cast_op
                core_models.num.Impl_1.MIN :
                RustM i32)))) then do
              (pure core_models.num.Impl_1.MIN)
            else do
              (rust_primitives.hax.cast_op
                (← b[(← (i -? (4 : u64)))]_?) :
                RustM i16)
        else do
          if (← (i <? (12 : u64))) then do
            if
            (← ((← a[(← (i -? (4 : u64)))]_?)
              >? (← (rust_primitives.hax.cast_op
                core_models.num.Impl_1.MAX :
                RustM i32)))) then do
              (pure core_models.num.Impl_1.MAX)
            else do
              if
              (← ((← a[(← (i -? (4 : u64)))]_?)
                <? (← (rust_primitives.hax.cast_op
                  core_models.num.Impl_1.MIN :
                  RustM i32)))) then do
                (pure core_models.num.Impl_1.MIN)
              else do
                (rust_primitives.hax.cast_op
                  (← a[(← (i -? (4 : u64)))]_?) :
                  RustM i16)
          else do
            if
            (← ((← b[(← (i -? (8 : u64)))]_?)
              >? (← (rust_primitives.hax.cast_op
                core_models.num.Impl_1.MAX :
                RustM i32)))) then do
              (pure core_models.num.Impl_1.MAX)
            else do
              if
              (← ((← b[(← (i -? (8 : u64)))]_?)
                <? (← (rust_primitives.hax.cast_op
                  core_models.num.Impl_1.MIN :
                  RustM i32)))) then do
                (pure core_models.num.Impl_1.MIN)
              else do
                (rust_primitives.hax.cast_op
                  (← b[(← (i -? (8 : u64)))]_?) :
                  RustM i16) :
      RustM i16)))

@[spec]
def _mm256_inserti128_si256 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((2 : u64)) i128))
    (b : (core_models.abstractions.funarr.FunArray ((1 : u64)) i128)) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i128) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      if (← ((← (IMM8 %? (2 : i32))) ==? (0 : i32))) then do
        match i with
          | 0 => do b[(0 : u64)]_?
          | 1 => do a[(1 : u64)]_?
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code")))
      else do
        match i with
          | 0 => do a[(0 : u64)]_?
          | 1 => do b[(0 : u64)]_?
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
      RustM i128)))

@[spec]
def _mm256_blend_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16))
    (b : (core_models.abstractions.funarr.FunArray ((16 : u64)) i16)) :
    RustM (core_models.abstractions.funarr.FunArray ((16 : u64)) i16) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if
      (← ((← ((← (IMM8 >>>? (← (i %? (8 : u64))))) %? (2 : i32)))
        ==? (0 : i32))) then do
        a[i]_?
      else do
        b[i]_? :
      RustM i16)))

@[spec]
def _mm256_blendv_ps
    (a : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32))
    (mask : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((8 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← ((← mask[i]_?) <? (0 : i32))) then do b[i]_? else do a[i]_? :
      RustM i32)))

@[spec]
def _mm_movemask_epi8
    (a : (core_models.abstractions.funarr.FunArray ((16 : u64)) i8)) :
    RustM i32 := do
  let a0 : i32 ←
    if (← ((← a[(0 : u64)]_?) <? (0 : i8))) then do
      (pure (1 : i32))
    else do
      (pure (0 : i32));
  let a1 : i32 ←
    if (← ((← a[(1 : u64)]_?) <? (0 : i8))) then do
      (pure (2 : i32))
    else do
      (pure (0 : i32));
  let a2 : i32 ←
    if (← ((← a[(2 : u64)]_?) <? (0 : i8))) then do
      (pure (4 : i32))
    else do
      (pure (0 : i32));
  let a3 : i32 ←
    if (← ((← a[(3 : u64)]_?) <? (0 : i8))) then do
      (pure (8 : i32))
    else do
      (pure (0 : i32));
  let a4 : i32 ←
    if (← ((← a[(4 : u64)]_?) <? (0 : i8))) then do
      (pure (16 : i32))
    else do
      (pure (0 : i32));
  let a5 : i32 ←
    if (← ((← a[(5 : u64)]_?) <? (0 : i8))) then do
      (pure (32 : i32))
    else do
      (pure (0 : i32));
  let a6 : i32 ←
    if (← ((← a[(6 : u64)]_?) <? (0 : i8))) then do
      (pure (64 : i32))
    else do
      (pure (0 : i32));
  let a7 : i32 ←
    if (← ((← a[(7 : u64)]_?) <? (0 : i8))) then do
      (pure (128 : i32))
    else do
      (pure (0 : i32));
  let a8 : i32 ←
    if (← ((← a[(8 : u64)]_?) <? (0 : i8))) then do
      (pure (256 : i32))
    else do
      (pure (0 : i32));
  let a9 : i32 ←
    if (← ((← a[(9 : u64)]_?) <? (0 : i8))) then do
      (pure (512 : i32))
    else do
      (pure (0 : i32));
  let a10 : i32 ←
    if (← ((← a[(10 : u64)]_?) <? (0 : i8))) then do
      (pure (1024 : i32))
    else do
      (pure (0 : i32));
  let a11 : i32 ←
    if (← ((← a[(11 : u64)]_?) <? (0 : i8))) then do
      (pure (2048 : i32))
    else do
      (pure (0 : i32));
  let a12 : i32 ←
    if (← ((← a[(12 : u64)]_?) <? (0 : i8))) then do
      (pure (4096 : i32))
    else do
      (pure (0 : i32));
  let a13 : i32 ←
    if (← ((← a[(13 : u64)]_?) <? (0 : i8))) then do
      (pure (8192 : i32))
    else do
      (pure (0 : i32));
  let a14 : i32 ←
    if (← ((← a[(14 : u64)]_?) <? (0 : i8))) then do
      (pure (16384 : i32))
    else do
      (pure (0 : i32));
  let a15 : i32 ←
    if (← ((← a[(15 : u64)]_?) <? (0 : i8))) then do
      (pure (32768 : i32))
    else do
      (pure (0 : i32));
  ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← (a0 +? a1)) +? a2))
                            +? a3))
                          +? a4))
                        +? a5))
                      +? a6))
                    +? a7))
                  +? a8))
                +? a9))
              +? a10))
            +? a11))
          +? a12))
        +? a13))
      +? a14))
    +? a15)

@[spec]
def _mm256_srlv_epi64
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64))
    (b : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      if
      (← ((← ((← b[i]_?) >? (63 : i64))) ||? (← ((← b[i]_?) <? (0 : i64)))))
      then do
        (pure (0 : i64))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u64))
            >>>? (← b[i]_?))) :
          RustM i64) :
      RustM i64)))

@[spec]
def _mm_sllv_epi32
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i32))
    (b : (core_models.abstractions.funarr.FunArray ((4 : u64)) i32)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i32) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if
      (← ((← ((← b[i]_?) >? (31 : i32))) ||? (← ((← b[i]_?) <? (0 : i32)))))
      then do
        (pure (0 : i32))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u32))
            <<<? (← b[i]_?))) :
          RustM i32) :
      RustM i32)))

@[spec]
def _mm256_slli_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let imm8 : i32 ← (IMM8 %? (256 : i32));
      if (← (imm8 >? (63 : i32))) then do
        (pure (0 : i64))
      else do
        (rust_primitives.hax.cast_op
          (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u64))
            <<<? imm8)) :
          RustM i64) :
      RustM i64)))

@[spec]
def _mm256_bsrli_epi128 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((2 : u64)) i128)) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i128) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      let tmp : i32 ← (IMM8 %? (256 : i32));
      let tmp : i32 ← (tmp %? (16 : i32));
      (rust_primitives.hax.cast_op
        (← ((← (rust_primitives.hax.cast_op (← a[i]_?) : RustM u128))
          >>>? (← (tmp *? (8 : i32))))) :
        RustM i128) :
      RustM i128)))

@[spec]
def _mm256_andnot_si256
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      match (rust_primitives.hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(core_models.abstractions.bit.Bit.Zero ),
           (core_models.abstractions.bit.Bit.One )⟩ => do
          (pure core_models.abstractions.bit.Bit.One)
        | _ => do (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def _mm256_set1_epi64x (a : i64) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64) (fun _ => (do (pure a) : RustM i64)))

@[spec]
def _mm256_set_epi64x (e3 : i64) (e2 : i64) (e1 : i64) (e0 : i64) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => do (pure e0)
        | 1 => do (pure e1)
        | 2 => do (pure e2)
        | 3 => do (pure e3)
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

@[spec]
def _mm256_unpacklo_epi64
    (a : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64))
    (b : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM (core_models.abstractions.funarr.FunArray ((4 : u64)) i64) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => do a[(0 : u64)]_?
        | 1 => do b[(0 : u64)]_?
        | 2 => do a[(2 : u64)]_?
        | 3 => do b[(2 : u64)]_?
        | _ => do
          (rust_primitives.hax.never_to_any
            (← (core_models.panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

@[spec]
def _mm256_permute2x128_si256 (IMM8 : i32)
    (a : (core_models.abstractions.funarr.FunArray ((2 : u64)) i128))
    (b : (core_models.abstractions.funarr.FunArray ((2 : u64)) i128)) :
    RustM (core_models.abstractions.funarr.FunArray ((2 : u64)) i128) := do
  (core_models.abstractions.funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      let control : i32 ← (IMM8 >>>? (← (i *? (4 : u64))));
      if
      (← ((← ((← (control >>>? (3 : i32))) %? (2 : i32))) ==? (1 : i32))) then
      do
        (pure (0 : i128))
      else do
        match (← (control %? (4 : i32))) with
          | 0 => do a[(0 : u64)]_?
          | 1 => do a[(1 : u64)]_?
          | 2 => do b[(0 : u64)]_?
          | 3 => do b[(1 : u64)]_?
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
      RustM i128)))

end core_models.core_arch.x86.interpretations.int_vec


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

--  An F* attribute that marks an item as being an lifting lemma.
def ETA_MATCH_EXPAND : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

opaque pointwise_i32x8
    (x : (core_models.abstractions.funarr.FunArray ((8 : u64)) i32)) :
    RustM rust_primitives.hax.Tuple0

opaque pointwise_i64x4
    (x : (core_models.abstractions.funarr.FunArray ((4 : u64)) i64)) :
    RustM rust_primitives.hax.Tuple0

--  An F* attribute that marks an item as being an lifting lemma.
def LIFT_LEMMA : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

def ___2 : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk (do (pure rust_primitives.hax.Tuple0.mk)) (by rfl)

--  F* tactic: specialization of `Tactics.Circuits.flatten_circuit`.
@[spec]
def flatten_circuit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86

def ___1 : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

--  256-bit wide integer vector type.
--  Models `core::arch::x86::__m256i` or `core::arch::x86_64::__m256i` (the __m256i type defined by Intel, representing a 256-bit SIMD register).
abbrev __m256i : Type := (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  128-bit wide integer vector type.
--  Models `core::arch::x86::__m128i` or `core::arch::x86_64::__m128i` (the __m128i type defined by Intel, representing a 128-bit SIMD register).
abbrev __m128i : Type := (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  256-bit wide vector type, which can be interpreted as 8 32 bit floating point values.
--  Models `core::arch::x86::__m256` or `core::arch::x86_64::__m256`, but since we do not have use and fully support floating points yet, it is treated the same as __m256i.
abbrev __m256 : Type := (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86


namespace core_models.core_arch.x86.ssse3

opaque _mm_shuffle_epi8
    (vector : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (indexes : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.ssse3


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi16)
opaque _mm_packs_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_packs_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

opaque _mm_set_epi8
    (_e15 : i8)
    (_e14 : i8)
    (_e13 : i8)
    (_e12 : i8)
    (_e11 : i8)
    (_e10 : i8)
    (_e9 : i8)
    (_e8 : i8)
    (_e7 : i8)
    (_e6 : i8)
    (_e5 : i8)
    (_e4 : i8)
    (_e3 : i8)
    (_e2 : i8)
    (_e1 : i8)
    (_e0 : i8) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi16)
opaque _mm_set1_epi16 (_ : i16) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_set1_epi16 (x : i16) : RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
opaque _mm_set_epi32 (_ : i32) (_ : i32) (_ : i32) (_ : i32) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_set_epi32 (e3 : i32) (e2 : i32) (e1 : i32) (e0 : i32) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi16)
opaque _mm_add_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_add_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi16)
opaque _mm_sub_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mullo_epi16)
opaque _mm_mullo_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_mullo_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epi16)
opaque _mm_mulhi_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_mulhi_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi64)
opaque _mm_srli_epi64 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_srli_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_epi8)
opaque _mm_movemask_epi8
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM i32

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_movemask_epi8
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpacklo_epi64)
opaque _mm_unpacklo_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_unpackhi_epi64)
opaque _mm_unpackhi_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi32)
opaque _mm_shuffle_epi32 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_si128)
opaque _mm_srli_si128 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_slli_si128)
opaque _mm_slli_si128 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_xor_si128)
opaque _mm_xor_si128
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_setzero_si128)
opaque _mm_setzero_si128 (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.sse2


namespace core_models.core_arch.x86.avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi64x)
opaque _mm256_set1_epi64x (_ : i64) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_set1_epi64x (a : i64) : RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi64x)
opaque _mm256_set_epi64x (_ : i64) (_ : i64) (_ : i64) (_ : i64) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_set_epi64x (e3 : i64) (e2 : i64) (e1 : i64) (e0 : i64) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_ps)
opaque _mm256_blendv_ps
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_blendv_ps
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (c : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi128_si256)
opaque _mm256_castsi128_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_testz_si256)
opaque _mm256_testz_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM i32

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi256_ps)
opaque _mm256_castsi256_ps
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castps_si256)
opaque _mm256_castps_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_ps)
opaque _mm256_movemask_ps
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM i32

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_movemask_ps
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_si256)
opaque _mm256_setzero_si256 (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_m128i)
opaque _mm256_set_m128i
    (hi : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (lo : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

@[spec]
def _mm256_castsi256_si128
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((128 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i => (do vector[i]_? : RustM core_models.abstractions.bit.Bit)))

--  This is opaque to Hax: it is defined only via the integer
--  interpretation. See `interpretations::int_vec::_mm256_set1_epi32`.
opaque _mm256_set1_epi32 (_ : i32) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_set1_epi32 (x : i32) : RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx

--  This is opaque to Hax: we have lemmas about this intrinsics
--  composed with others. See e.g. `_rw_mm256_sllv_epi32`.
opaque _mm256_set_epi32
    (_e0 : i32)
    (_e1 : i32)
    (_e2 : i32)
    (_e3 : i32)
    (_e4 : i32)
    (_e5 : i32)
    (_e6 : i32)
    (_e7 : i32) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  This is opaque to Hax: we have lemmas about this intrinsics
--  composed with others. See e.g. `_rw_mm256_mullo_epi16_shifts`.
opaque _mm256_set_epi16
    (_e00 : i16)
    (_e01 : i16)
    (_e02 : i16)
    (_e03 : i16)
    (_e04 : i16)
    (_e05 : i16)
    (_e06 : i16)
    (_e07 : i16)
    (_e08 : i16)
    (_e09 : i16)
    (_e10 : i16)
    (_e11 : i16)
    (_e12 : i16)
    (_e13 : i16)
    (_e14 : i16)
    (_e15 : i16) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  This is opaque to Hax: we have lemmas about this intrinsics
--  composed with others. See e.g. `_rw_mm256_shuffle_epi8`.
opaque _mm256_set_epi8
    (_e00 : i8)
    (_e01 : i8)
    (_e02 : i8)
    (_e03 : i8)
    (_e04 : i8)
    (_e05 : i8)
    (_e06 : i8)
    (_e07 : i8)
    (_e08 : i8)
    (_e09 : i8)
    (_e10 : i8)
    (_e11 : i8)
    (_e12 : i8)
    (_e13 : i8)
    (_e14 : i8)
    (_e15 : i8)
    (_e16 : i8)
    (_e17 : i8)
    (_e18 : i8)
    (_e19 : i8)
    (_e20 : i8)
    (_e21 : i8)
    (_e22 : i8)
    (_e23 : i8)
    (_e24 : i8)
    (_e25 : i8)
    (_e26 : i8)
    (_e27 : i8)
    (_e28 : i8)
    (_e29 : i8)
    (_e30 : i8)
    (_e31 : i8) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)
opaque _mm256_set1_epi16 (_ : i16) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_set1_epi16 (x : i16) : RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)
opaque _mm256_blend_epi32 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_blend_epi32 (CONTROL : i32)
    (x : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (y : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)
opaque _mm256_shuffle_epi32 (MASK : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_shuffle_epi32 (CONTROL : i32)
    (x : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)
opaque _mm256_sub_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_sub_epi32
    (x : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (y : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)
opaque _mm256_mul_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_mul_epi32
    (x : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (y : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)
opaque _mm256_add_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_add_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_madd_epi16)
opaque _mm256_madd_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)
opaque _mm256_add_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_add_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)
opaque _mm256_add_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_add_epi64
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)
opaque _mm256_abs_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_abs_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)
opaque _mm256_sub_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_sub_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)
opaque _mm256_cmpgt_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_cmpgt_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)
opaque _mm256_cmpgt_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_cmpgt_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi32)
opaque _mm256_cmpeq_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)
opaque _mm256_sign_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_sign_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)
opaque _mm256_mullo_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_mullo_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)
opaque _mm256_mulhi_epi16
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_mulhi_epi16
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)
opaque _mm256_mul_epu32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_mul_epu32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_and_si256)
opaque _mm256_and_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_or_si256)
opaque _mm256_or_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_xor_si256)
opaque _mm256_xor_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)
opaque _mm256_srai_epi16 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_srai_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)
opaque _mm256_srai_epi32 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_srai_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)
opaque _mm256_srli_epi16 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_srli_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)
opaque _mm256_srli_epi32 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_srli_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)
opaque _mm256_slli_epi32 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_slli_epi32 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)
opaque _mm256_permute4x64_epi64 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_permute4x64_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)
opaque _mm256_unpackhi_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_unpackhi_epi64
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)
opaque _mm256_unpacklo_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_unpacklo_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)
opaque _mm256_unpackhi_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_unpackhi_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)
opaque _mm256_cvtepi16_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_cvtepi16_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)
opaque _mm256_packs_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_packs_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)
opaque _mm256_inserti128_si256 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_inserti128_si256 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
opaque _mm256_blend_epi16 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_blend_epi16 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)
opaque _mm256_srlv_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_srlv_epi64
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)
opaque _mm_sllv_epi32
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm_sllv_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)
opaque _mm256_slli_epi64 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_slli_epi64 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
--  NOTE: the bsrli here is different from intel specification. In the intel specification, if an IMM8 is given whose first 8 bits are higher than 15, it fixes it to 16.
--  However, the Rust implementation erroneously takes the input modulo 16. Thus, instead of shifting by 16 bits at an input of 16, it shifts by 0.
--  We are currently modelling the Rust implementation.
opaque _mm256_bsrli_epi128 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_bsrli_epi128 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_andnot_si256)
opaque _mm256_andnot_si256
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)
opaque _mm256_unpacklo_epi64
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_unpacklo_epi64
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)
opaque _mm256_permute2x128_si256 (IMM8 : i32)
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.interpretations.int_vec.lemmas

opaque _mm256_permute2x128_si256 (IMM8 : i32)
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86.interpretations.int_vec.lemmas


namespace core_models.core_arch.x86.avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi16)
@[spec]
def _mm256_slli_epi16 (SHIFT_BY : i32)
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_10.chunked_shift
    ((256 : u64))
    ((16 : u64))
    ((16 : u64))
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((16 : u64))
      i128
      (u64 -> RustM i128)
      (fun _ =>
        (do
        (rust_primitives.hax.cast_op SHIFT_BY : RustM i128) : RustM i128)))))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi64)
@[spec]
def _mm256_srli_epi64 (SHIFT_BY : i32)
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_10.chunked_shift
    ((256 : u64))
    ((64 : u64))
    ((4 : u64))
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((4 : u64))
      i128
      (u64 -> RustM i128)
      (fun _ =>
        (do
        (-? (← (rust_primitives.hax.cast_op SHIFT_BY : RustM i128))) :
        RustM i128)))))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi16)
opaque _mm256_mullo_epi16
    (_vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (_shifts : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi32)
opaque _mm256_sllv_epi32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (counts : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi32)
opaque _mm256_srlv_epi32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (counts : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_epi32)
opaque _mm256_permutevar8x32_epi32
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extracti128_si256)
@[spec]
def _mm256_extracti128_si256 (IMM8 : i32)
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((128 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      vector[
        (← (i
          +? (← if (← (IMM8 ==? (0 : i32))) then do
            (pure (0 : u64))
          else do
            (pure (128 : u64)))))
        ]_? :
      RustM core_models.abstractions.bit.Bit)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi8)
opaque _mm256_shuffle_epi8
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (indexes : (core_models.abstractions.bitvec.BitVec ((256 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64)))

end core_models.core_arch.x86.avx2


namespace core_models.core_arch.x86.other

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aeskeygenassist_si128)
opaque _mm_aeskeygenassist_si128
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : i32) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aesenclast_si128)
opaque _mm_aesenclast_si128
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_aesenc_si128)
opaque _mm_aesenc_si128
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64)))) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_clmulepi64_si128)
opaque _mm_clmulepi64_si128
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (_ : i32) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64)))

end core_models.core_arch.x86.other


namespace core_models.core_arch.x86

--  Rewrite lemmas
def _ : rust_primitives.hax.Tuple0 := rust_primitives.hax.Tuple0.mk

@[spec]
def _._rw_mm256_mullo_epi16_shifts (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm256_sllv_epi32_u32_array
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (counts : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_10.chunked_shift
    ((256 : u64))
    ((32 : u64))
    ((8 : u64))
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((8 : u64))
      i128
      (u64 -> RustM i128)
      (fun i =>
        (do
        (rust_primitives.hax.cast_op (← counts[i]_?) : RustM i128) :
        RustM i128)))))

@[spec]
def mm256_sllv_epi32_u32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : u32)
    (b6 : u32)
    (b5 : u32)
    (b4 : u32)
    (b3 : u32)
    (b2 : u32)
    (b1 : u32)
    (b0 : u32) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (mm256_sllv_epi32_u32_array
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((8 : u64))
      u32
      (u64 -> RustM u32)
      (fun i =>
        (do
        match i with
          | 7 => do (pure b7)
          | 6 => do (pure b6)
          | 5 => do (pure b5)
          | 4 => do (pure b4)
          | 3 => do (pure b3)
          | 2 => do (pure b2)
          | 1 => do (pure b1)
          | 0 => do (pure b0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM u32)))))

end core_models.core_arch.x86.extra


namespace core_models.core_arch.x86

opaque _._rw_mm256_sllv_epi32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : i32)
    (b6 : i32)
    (b5 : i32)
    (b4 : i32)
    (b3 : i32)
    (b2 : i32)
    (b1 : i32)
    (b0 : i32) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm256_srlv_epi32_u32_array
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (counts : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_10.chunked_shift
    ((256 : u64))
    ((32 : u64))
    ((8 : u64))
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((8 : u64))
      i128
      (u64 -> RustM i128)
      (fun i =>
        (do
        (-? (← (rust_primitives.hax.cast_op (← counts[i]_?) : RustM i128))) :
        RustM i128)))))

@[spec]
def mm256_srlv_epi32_u32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : u32)
    (b6 : u32)
    (b5 : u32)
    (b4 : u32)
    (b3 : u32)
    (b2 : u32)
    (b1 : u32)
    (b0 : u32) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (mm256_srlv_epi32_u32_array
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((8 : u64))
      u32
      (u64 -> RustM u32)
      (fun i =>
        (do
        match i with
          | 7 => do (pure b7)
          | 6 => do (pure b6)
          | 5 => do (pure b5)
          | 4 => do (pure b4)
          | 3 => do (pure b3)
          | 2 => do (pure b2)
          | 1 => do (pure b1)
          | 0 => do (pure b0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM u32)))))

end core_models.core_arch.x86.extra


namespace core_models.core_arch.x86

opaque _._rw_mm256_srlv_epi32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : i32)
    (b6 : i32)
    (b5 : i32)
    (b4 : i32)
    (b3 : i32)
    (b2 : i32)
    (b1 : i32)
    (b0 : i32) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm256_permutevar8x32_epi32_u32_array
    (a : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b : (core_models.abstractions.funarr.FunArray ((8 : u64)) u32)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      let j : u64 ← (i /? (32 : u64));
      let index : u64 ←
        ((← (rust_primitives.hax.cast_op
            (← ((← b[j]_?) %? (8 : u32))) :
            RustM u64))
          *? (32 : u64));
      a[(← (index +? (← (i %? (32 : u64)))))]_? :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def mm256_permutevar8x32_epi32_u32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : u32)
    (b6 : u32)
    (b5 : u32)
    (b4 : u32)
    (b3 : u32)
    (b2 : u32)
    (b1 : u32)
    (b0 : u32) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (mm256_permutevar8x32_epi32_u32_array
    vector
    (← (core_models.abstractions.funarr.Impl_5.from_fn
      ((8 : u64))
      u32
      (u64 -> RustM u32)
      (fun i =>
        (do
        match i with
          | 7 => do (pure b7)
          | 6 => do (pure b6)
          | 5 => do (pure b5)
          | 4 => do (pure b4)
          | 3 => do (pure b3)
          | 2 => do (pure b2)
          | 1 => do (pure b1)
          | 0 => do (pure b0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM u32)))))

end core_models.core_arch.x86.extra


namespace core_models.core_arch.x86

opaque _._rw_mm256_permutevar8x32_epi32
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (b7 : i32)
    (b6 : i32)
    (b5 : i32)
    (b4 : i32)
    (b3 : i32)
    (b2 : i32)
    (b1 : i32)
    (b0 : i32) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm_shuffle_epi8_u8_array
    (vector : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (indexes : (core_models.abstractions.funarr.FunArray ((16 : u64)) u8)) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((128 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      let nth : u64 ← (i /? (8 : u64));
      let index : u8 ← indexes[nth]_?;
      if (← (index >? (127 : u8))) then do
        (pure core_models.abstractions.bit.Bit.Zero)
      else do
        let index : u64 ←
          (rust_primitives.hax.cast_op (← (index %? (16 : u8))) : RustM u64);
        vector[(← ((← (index *? (8 : u64))) +? (← (i %? (8 : u64)))))]_? :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def mm_shuffle_epi8_u8
    (vector : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (b15 : u8)
    (b14 : u8)
    (b13 : u8)
    (b12 : u8)
    (b11 : u8)
    (b10 : u8)
    (b9 : u8)
    (b8 : u8)
    (b7 : u8)
    (b6 : u8)
    (b5 : u8)
    (b4 : u8)
    (b3 : u8)
    (b2 : u8)
    (b1 : u8)
    (b0 : u8) :
    RustM (core_models.abstractions.bitvec.BitVec ((128 : u64))) := do
  let indexes : (core_models.abstractions.funarr.FunArray ((16 : u64)) u8) ←
    (core_models.abstractions.funarr.Impl_5.from_fn
      ((16 : u64))
      u8
      (u64 -> RustM u8)
      (fun i =>
        (do
        match i with
          | 15 => do (pure b15)
          | 14 => do (pure b14)
          | 13 => do (pure b13)
          | 12 => do (pure b12)
          | 11 => do (pure b11)
          | 10 => do (pure b10)
          | 9 => do (pure b9)
          | 8 => do (pure b8)
          | 7 => do (pure b7)
          | 6 => do (pure b6)
          | 5 => do (pure b5)
          | 4 => do (pure b4)
          | 3 => do (pure b3)
          | 2 => do (pure b2)
          | 1 => do (pure b1)
          | 0 => do (pure b0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM u8)));
  (mm_shuffle_epi8_u8_array vector indexes)

end core_models.core_arch.x86.extra


namespace core_models.core_arch.x86

opaque _._rw_mm_shuffle_epi8
    (vector : (core_models.abstractions.bitvec.BitVec ((128 : u64))))
    (e15 : i8)
    (e14 : i8)
    (e13 : i8)
    (e12 : i8)
    (e11 : i8)
    (e10 : i8)
    (e9 : i8)
    (e8 : i8)
    (e7 : i8)
    (e6 : i8)
    (e5 : i8)
    (e4 : i8)
    (e3 : i8)
    (e2 : i8)
    (e1 : i8)
    (e0 : i8) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm256_shuffle_epi8_i8_array
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (indexes : (core_models.abstractions.funarr.FunArray ((32 : u64)) i8)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      let nth : u64 ← (i /? (8 : u64));
      let index : i8 ← indexes[nth]_?;
      if (← (index <? (0 : i8))) then do
        (pure core_models.abstractions.bit.Bit.Zero)
      else do
        let index : u64 ←
          (rust_primitives.hax.cast_op (← (index %? (16 : i8))) : RustM u64);
        vector[
          (← ((← ((← if (← (i <? (128 : u64))) then do
                (pure (0 : u64))
              else do
                (pure (128 : u64)))
              +? (← (index *? (8 : u64)))))
            +? (← (i %? (8 : u64)))))
          ]_? :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def mm256_shuffle_epi8_i8
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (byte31 : i8)
    (byte30 : i8)
    (byte29 : i8)
    (byte28 : i8)
    (byte27 : i8)
    (byte26 : i8)
    (byte25 : i8)
    (byte24 : i8)
    (byte23 : i8)
    (byte22 : i8)
    (byte21 : i8)
    (byte20 : i8)
    (byte19 : i8)
    (byte18 : i8)
    (byte17 : i8)
    (byte16 : i8)
    (byte15 : i8)
    (byte14 : i8)
    (byte13 : i8)
    (byte12 : i8)
    (byte11 : i8)
    (byte10 : i8)
    (byte9 : i8)
    (byte8 : i8)
    (byte7 : i8)
    (byte6 : i8)
    (byte5 : i8)
    (byte4 : i8)
    (byte3 : i8)
    (byte2 : i8)
    (byte1 : i8)
    (byte0 : i8) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  let indexes : (core_models.abstractions.funarr.FunArray ((32 : u64)) i8) ←
    (core_models.abstractions.funarr.Impl_5.from_fn
      ((32 : u64))
      i8
      (u64 -> RustM i8)
      (fun i =>
        (do
        match i with
          | 31 => do (pure byte31)
          | 30 => do (pure byte30)
          | 29 => do (pure byte29)
          | 28 => do (pure byte28)
          | 27 => do (pure byte27)
          | 26 => do (pure byte26)
          | 25 => do (pure byte25)
          | 24 => do (pure byte24)
          | 23 => do (pure byte23)
          | 22 => do (pure byte22)
          | 21 => do (pure byte21)
          | 20 => do (pure byte20)
          | 19 => do (pure byte19)
          | 18 => do (pure byte18)
          | 17 => do (pure byte17)
          | 16 => do (pure byte16)
          | 15 => do (pure byte15)
          | 14 => do (pure byte14)
          | 13 => do (pure byte13)
          | 12 => do (pure byte12)
          | 11 => do (pure byte11)
          | 10 => do (pure byte10)
          | 9 => do (pure byte9)
          | 8 => do (pure byte8)
          | 7 => do (pure byte7)
          | 6 => do (pure byte6)
          | 5 => do (pure byte5)
          | 4 => do (pure byte4)
          | 3 => do (pure byte3)
          | 2 => do (pure byte2)
          | 1 => do (pure byte1)
          | 0 => do (pure byte0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM i8)));
  (mm256_shuffle_epi8_i8_array vector indexes)

end core_models.core_arch.x86.extra


namespace core_models.core_arch.x86

opaque _._rw_mm256_shuffle_epi8
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (byte31 : i8)
    (byte30 : i8)
    (byte29 : i8)
    (byte28 : i8)
    (byte27 : i8)
    (byte26 : i8)
    (byte25 : i8)
    (byte24 : i8)
    (byte23 : i8)
    (byte22 : i8)
    (byte21 : i8)
    (byte20 : i8)
    (byte19 : i8)
    (byte18 : i8)
    (byte17 : i8)
    (byte16 : i8)
    (byte15 : i8)
    (byte14 : i8)
    (byte13 : i8)
    (byte12 : i8)
    (byte11 : i8)
    (byte10 : i8)
    (byte9 : i8)
    (byte8 : i8)
    (byte7 : i8)
    (byte6 : i8)
    (byte5 : i8)
    (byte4 : i8)
    (byte3 : i8)
    (byte2 : i8)
    (byte1 : i8)
    (byte0 : i8) :
    RustM rust_primitives.hax.Tuple0

end core_models.core_arch.x86


namespace core_models.core_arch.x86.extra

@[spec]
def mm256_mullo_epi16_shifts_array
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (shifts : (core_models.abstractions.funarr.FunArray ((16 : u64)) u8)) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  (core_models.abstractions.bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM core_models.abstractions.bit.Bit)
    (fun i =>
      (do
      let nth_bit : u64 ← (i %? (16 : u64));
      let nth_i16 : u64 ← (i /? (16 : u64));
      let shift : u64 ←
        (rust_primitives.hax.cast_op (← shifts[nth_i16]_?) : RustM u64);
      if (← (nth_bit >=? shift)) then do
        vector[(← ((← ((← (nth_i16 *? (16 : u64))) +? nth_bit)) -? shift))]_?
      else do
        (pure core_models.abstractions.bit.Bit.Zero) :
      RustM core_models.abstractions.bit.Bit)))

@[spec]
def mm256_mullo_epi16_shifts
    (vector : (core_models.abstractions.bitvec.BitVec ((256 : u64))))
    (s15 : u8)
    (s14 : u8)
    (s13 : u8)
    (s12 : u8)
    (s11 : u8)
    (s10 : u8)
    (s9 : u8)
    (s8 : u8)
    (s7 : u8)
    (s6 : u8)
    (s5 : u8)
    (s4 : u8)
    (s3 : u8)
    (s2 : u8)
    (s1 : u8)
    (s0 : u8) :
    RustM (core_models.abstractions.bitvec.BitVec ((256 : u64))) := do
  let shifts : (core_models.abstractions.funarr.FunArray ((16 : u64)) u8) ←
    (core_models.abstractions.funarr.Impl_5.from_fn
      ((16 : u64))
      u8
      (u64 -> RustM u8)
      (fun i =>
        (do
        match i with
          | 15 => do (pure s15)
          | 14 => do (pure s14)
          | 13 => do (pure s13)
          | 12 => do (pure s12)
          | 11 => do (pure s11)
          | 10 => do (pure s10)
          | 9 => do (pure s9)
          | 8 => do (pure s8)
          | 7 => do (pure s7)
          | 6 => do (pure s6)
          | 5 => do (pure s5)
          | 4 => do (pure s4)
          | 3 => do (pure s3)
          | 2 => do (pure s2)
          | 1 => do (pure s1)
          | 0 => do (pure s0)
          | _ => do
            (rust_primitives.hax.never_to_any
              (← (core_models.panicking.panic
                "internal error: entered unreachable code"))) :
        RustM u8)));
  (mm256_mullo_epi16_shifts_array vector shifts)

end core_models.core_arch.x86.extra
