
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace hacspec_ml_kem.parameters

--  Field modulus: 3329
def FIELD_MODULUS : u16 := (3329 : u16)

--  Each field element needs floor(log_2(FIELD_MODULUS)) + 1 = 12 bits to represent
def BITS_PER_COEFFICIENT : usize := (12 : usize)

--  Coefficients per ring element
def COEFFICIENTS_IN_RING_ELEMENT : usize := (256 : usize)

--  Bits required per (uncompressed) ring element
def BITS_PER_RING_ELEMENT : usize :=
  RustM.of_isOk (do (COEFFICIENTS_IN_RING_ELEMENT *? (12 : usize))) (by rfl)

--  Bytes required per (uncompressed) ring element
def BYTES_PER_RING_ELEMENT : usize :=
  RustM.of_isOk (do (BITS_PER_RING_ELEMENT /? (8 : usize))) (by rfl)

--  Seed size for rejection sampling.
--
--  See <https://eprint.iacr.org/2023/708> for some background regarding
--  this choice.
def REJECTION_SAMPLING_SEED_SIZE : usize :=
  RustM.of_isOk (do ((168 : usize) *? (5 : usize))) (by rfl)

--  ML-KEM parameter set
structure MlKemParams where
  rank : usize
  eta1 : usize
  eta2 : usize
  du : usize
  dv : usize

@[spec]
def Impl.t_as_ntt_encoded_size (self : MlKemParams) : RustM usize := do
  ((MlKemParams.rank self) *? BYTES_PER_RING_ELEMENT)

@[spec]
def Impl.ek_size (self : MlKemParams) : RustM usize := do
  ((← (Impl.t_as_ntt_encoded_size self)) +? (32 : usize))

@[spec]
def Impl.dk_pke_size (self : MlKemParams) : RustM usize := do
  ((MlKemParams.rank self) *? BYTES_PER_RING_ELEMENT)

@[spec]
def Impl.u_encoded_size (self : MlKemParams) : RustM usize := do
  ((← ((← ((MlKemParams.rank self) *? COEFFICIENTS_IN_RING_ELEMENT))
      *? (MlKemParams.du self)))
    /? (8 : usize))

@[spec]
def Impl.v_encoded_size (self : MlKemParams) : RustM usize := do
  ((← (COEFFICIENTS_IN_RING_ELEMENT *? (MlKemParams.dv self))) /? (8 : usize))

@[spec]
def Impl.ciphertext_size (self : MlKemParams) : RustM usize := do
  ((← (Impl.u_encoded_size self)) +? (← (Impl.v_encoded_size self)))

def ML_KEM_512 : MlKemParams :=
  RustM.of_isOk
    (do
    (pure (MlKemParams.mk
      (rank := (2 : usize))
      (eta1 := (3 : usize))
      (eta2 := (2 : usize))
      (du := (10 : usize))
      (dv := (4 : usize)))))
    (by rfl)

def ML_KEM_768 : MlKemParams :=
  RustM.of_isOk
    (do
    (pure (MlKemParams.mk
      (rank := (3 : usize))
      (eta1 := (2 : usize))
      (eta2 := (2 : usize))
      (du := (10 : usize))
      (dv := (4 : usize)))))
    (by rfl)

def ML_KEM_1024 : MlKemParams :=
  RustM.of_isOk
    (do
    (pure (MlKemParams.mk
      (rank := (4 : usize))
      (eta1 := (2 : usize))
      (eta2 := (2 : usize))
      (du := (11 : usize))
      (dv := (5 : usize)))))
    (by rfl)

def ML_KEM_512_EK_SIZE : usize := (800 : usize)

def ML_KEM_512_DK_PKE_SIZE : usize := (768 : usize)

def ML_KEM_512_DK_SIZE : usize := (1632 : usize)

def ML_KEM_512_U_SIZE : usize := (640 : usize)

def ML_KEM_512_V_SIZE : usize := (128 : usize)

def ML_KEM_512_CT_SIZE : usize := (768 : usize)

def ML_KEM_512_J_INPUT_SIZE : usize := (800 : usize)

def ML_KEM_768_EK_SIZE : usize := (1184 : usize)

def ML_KEM_768_DK_PKE_SIZE : usize := (1152 : usize)

def ML_KEM_768_DK_SIZE : usize := (2400 : usize)

def ML_KEM_768_U_SIZE : usize := (960 : usize)

def ML_KEM_768_V_SIZE : usize := (128 : usize)

def ML_KEM_768_CT_SIZE : usize := (1088 : usize)

def ML_KEM_768_J_INPUT_SIZE : usize := (1120 : usize)

def ML_KEM_1024_EK_SIZE : usize := (1568 : usize)

def ML_KEM_1024_DK_PKE_SIZE : usize := (1536 : usize)

def ML_KEM_1024_DK_SIZE : usize := (3168 : usize)

def ML_KEM_1024_U_SIZE : usize := (1408 : usize)

def ML_KEM_1024_V_SIZE : usize := (160 : usize)

def ML_KEM_1024_CT_SIZE : usize := (1568 : usize)

def ML_KEM_1024_J_INPUT_SIZE : usize := (1600 : usize)

end hacspec_ml_kem.parameters


namespace hacspec_ml_kem.parameters.hash_functions

opaque G (input : (RustSlice u8)) : RustM (RustArray u8 64)

def H_DIGEST_SIZE : usize := (32 : usize)

end hacspec_ml_kem.parameters.hash_functions


namespace hacspec_ml_kem.parameters

@[spec]
def Impl.dk_size (self : MlKemParams) : RustM usize := do
  ((← ((← ((← (Impl.dk_pke_size self)) +? (← (Impl.ek_size self))))
      +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))
    +? (32 : usize))

end hacspec_ml_kem.parameters


namespace hacspec_ml_kem.parameters.hash_functions

opaque H (input : (RustSlice u8)) : RustM (RustArray u8 32)

opaque PRF (LEN : usize) (input : (RustSlice u8)) : RustM (RustArray u8 LEN)

opaque XOF (LEN : usize) (input : (RustSlice u8)) : RustM (RustArray u8 LEN)

opaque J (LEN : usize) (input : (RustSlice u8)) : RustM (RustArray u8 LEN)

end hacspec_ml_kem.parameters.hash_functions


namespace hacspec_ml_kem.parameters

--  An ML-KEM field element:
--  - after reduction modulo FIELD_MODULUS, it is an integer in the range [0, FIELD_MODULUS - 1]
--  - it is represented as a u16
structure FieldElement where
  val : u16

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.clone.Clone FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.marker.Copy FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.marker.StructuralPartialEq FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes FieldElement FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.cmp.PartialEq FieldElement FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.Eq FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.cmp.PartialOrd.AssociatedTypes FieldElement FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.cmp.PartialOrd FieldElement FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.cmp.Ord.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.cmp.Ord FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes FieldElement :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8 :
  core_models.fmt.Debug FieldElement :=
  by constructor <;> exact Inhabited.default

def Impl_9.new (val : u16) : RustM FieldElement := do
  (pure (FieldElement.mk (val := val)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl_9.new.spec (val : u16) :
    Spec
      (requires := do (val <? FIELD_MODULUS))
      (ensures := fun _ => pure True)
      (Impl_9.new (val : u16)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [Impl_9.new] <;> sorry
}

--  An ML-KEM polynomial ring element
abbrev Polynomial : Type := (RustArray FieldElement 256)

--  An ML-KEM vector
abbrev Vector (RANK : usize) :
  Type :=
  (RustArray (RustArray FieldElement 256) RANK)

--  Am ML-KEM matrix
abbrev Matrix (RANK : usize) :
  Type :=
  (RustArray (RustArray (RustArray FieldElement 256) RANK) RANK)

--  Utility function to create an array of size `N` by applying a function `f` to each index.
@[spec]
def createi
    (T : Type)
    (N : usize)
    (F : Type)
    [trait_constr_createi_associated_type_i0 :
      core_models.ops.function.Fn.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 usize)]
    (f : F) :
    RustM (RustArray T N) := sorry

abbrev BitVector (N : usize) : Type := (RustArray Bool N)

end hacspec_ml_kem.parameters


namespace hacspec_ml_kem.compress

--  This function implements the `Compress` function specified in the NIST FIPS
--  203 standard (Page 18, Expression 4.5), which is defined as:
--
--  ```plaintext
--  Compress_d: ℤq -> ℤ_{2ᵈ}
--  Compress_d(x) = ⌈(2ᵈ/q)·x⌋
--  ```
--
--  Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
--
--  ```plaintext
--  Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
--                = ⌊(2^{d+1}·x + q) / 2q⌋
--  ```
--
--  this latter expression is what the code computes, since it enables us to
--  avoid the use of floating point computations as required by the standard.
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def compress_d
    (fe : hacspec_ml_kem.parameters.FieldElement)
    (to_bit_size : usize) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let two_pow_bit_size : u32 ←
    (core_models.num.Impl_8.pow
      (2 : u32)
      (← (rust_primitives.hax.cast_op to_bit_size : RustM u32)));
  let compressed : u32 ←
    ((← ((← ((← ((← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val fe) :
              RustM u32))
            *? (2 : u32)))
          *? two_pow_bit_size))
        +? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32))))
      /? (← ((2 : u32)
        *? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32)))));
  (hacspec_ml_kem.parameters.Impl_9.new
    (← (rust_primitives.hax.cast_op
      (← (compressed %? two_pow_bit_size)) :
      RustM u16)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      compress_d.spec
      (fe : hacspec_ml_kem.parameters.FieldElement)
      (to_bit_size : usize) :
    Spec
      (requires := do (to_bit_size <? (12 : usize)))
      (ensures := fun _ => pure True)
      (compress_d
        (fe : hacspec_ml_kem.parameters.FieldElement)
        (to_bit_size : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [compress_d] <;> sorry
}

--  According to the NIST FIPS 203 standard (Page 10, Lines 536 - 539),
--  compressing a polynomial ring element is accomplished by `compress()`ing its
--  constituent field coefficients.
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def compress
    (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (bits_per_compressed_coefficient : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      (compress_d (← re[i]_?) bits_per_compressed_coefficient) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      compress.spec
      (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (bits_per_compressed_coefficient : usize) :
    Spec
      (requires := do (bits_per_compressed_coefficient <? (12 : usize)))
      (ensures := fun _ => pure True)
      (compress
        (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (bits_per_compressed_coefficient : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [compress] <;> sorry
}

--  This function implements the `Decompress` function specified in the NIST FIPS
--  203 standard (Page 18, Expression 4.6), which is defined as:
--
--  ```plaintext
--  Decompress_d: ℤ_{2ᵈ} -> ℤq
--  Decompress_d(y) = ⌈(q/2ᵈ)·y⌋
--  ```
--
--  Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
--
--  ```plaintext
--  Decompress_d(y) = ⌊(q/2ᵈ)·y + 1/2⌋
--                  = ⌊(2·y·q + 2ᵈ) / 2^{d+1})⌋
--  ```
--
--  this latter expression is what the code computes, since it enables us to
--  avoid the use of floating point computations as required by the standard.
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def decompress_d
    (fe : hacspec_ml_kem.parameters.FieldElement)
    (to_bit_size : usize) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let two_pow_bit_size : u32 ←
    (core_models.num.Impl_8.pow
      (2 : u32)
      (← (rust_primitives.hax.cast_op to_bit_size : RustM u32)));
  let numerator : u32 ←
    ((← ((← ((2 : u32)
          *? (← (rust_primitives.hax.cast_op
            (hacspec_ml_kem.parameters.FieldElement.val fe) :
            RustM u32))))
        *? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32))))
      +? two_pow_bit_size);
  let decompressed : u32 ← (numerator /? (← (two_pow_bit_size *? (2 : u32))));
  (hacspec_ml_kem.parameters.Impl_9.new
    (← (rust_primitives.hax.cast_op decompressed : RustM u16)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      decompress_d.spec
      (fe : hacspec_ml_kem.parameters.FieldElement)
      (to_bit_size : usize) :
    Spec
      (requires := do
        ((← (to_bit_size <? (12 : usize)))
          &&? (← ((hacspec_ml_kem.parameters.FieldElement.val fe)
            <? (← ((1 : u16) <<<? to_bit_size))))))
      (ensures := fun _ => pure True)
      (decompress_d
        (fe : hacspec_ml_kem.parameters.FieldElement)
        (to_bit_size : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [decompress_d] <;> sorry
}

--  According to the NIST FIPS 203 standard (Page 10, Lines 536 - 539),
--  compressing a polynomial ring element is accomplished by `decompress()`ing
--  its constituent field coefficients.
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def decompress
    (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (bits_per_compressed_coefficient : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      (decompress_d (← re[i]_?) bits_per_compressed_coefficient) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      decompress.spec
      (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (bits_per_compressed_coefficient : usize) :
    Spec
      (requires := do
        (hax_lib.prop.constructors.and
          (← (hax_lib.prop.constructors.from_bool
            (← (bits_per_compressed_coefficient <? (12 : usize)))))
          (← (hax_lib.prop.constructors.forall
            (fun i =>
              (do
              (hax_lib.prop.constructors.implies
                (← (hax_lib.prop.constructors.from_bool
                  (← (i <? (256 : usize)))))
                (← (hax_lib.prop.constructors.from_bool
                  (← ((hacspec_ml_kem.parameters.FieldElement.val (← re[i]_?))
                    <? (← ((1 : u16) <<<? bits_per_compressed_coefficient)))))))
              :
              RustM hax_lib.prop.Prop))))))
      (ensures := fun _ => pure True)
      (decompress
        (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (bits_per_compressed_coefficient : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [decompress] <;> sorry
}

end hacspec_ml_kem.compress


namespace hacspec_ml_kem.ind_cpa

def concat_byte (N : usize) (N1 : usize) (a : (RustArray u8 N)) (b : u8) :
    RustM (RustArray u8 N1) := do
  let result : (RustArray u8 N1) ← (rust_primitives.hax.repeat (0 : u8) N1);
  let result : (RustArray u8 N1) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      result
      (core_models.ops.range.RangeTo.mk (_end := N))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← result[(core_models.ops.range.RangeTo.mk (_end := N))]_?)
        (← (rust_primitives.unsize a)))));
  let result : (RustArray u8 N1) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize result N b);
  (pure result)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def concat_byte.spec (N : usize) (N1 : usize) (a : (RustArray u8 N)) (b : u8) :
    Spec
      (requires := do
        ((← (N1 >? (0 : usize))) &&? (← (N ==? (← (N1 -? (1 : usize)))))))
      (ensures := fun _ => pure True)
      (concat_byte (N : usize) (N1 : usize) (a : (RustArray u8 N)) (b : u8)) :=
{
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [concat_byte] <;> sorry
}

end hacspec_ml_kem.ind_cpa


namespace hacspec_ml_kem.invert_ntt

def INVERSE_OF_128 : hacspec_ml_kem.parameters.FieldElement :=
  RustM.of_isOk
    (do (hacspec_ml_kem.parameters.Impl_9.new (3303 : u16)))
    (by rfl)

@[spec]
def reduce_polynomial
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?)) :
                RustM u32))
              *? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val INVERSE_OF_128) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  Performs Barrett reduction on all coefficients of a polynomial.
--  This is the spec equivalent of `poly_barrett_reduce` in the implementation.
@[spec]
def poly_barrett_reduce
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← ((hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?))
          %? hacspec_ml_kem.parameters.FIELD_MODULUS))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

end hacspec_ml_kem.invert_ntt


namespace hacspec_ml_kem.matrix

--  N.B.: According to the NIST FIPS 203 standard (Page 9, Line 519), a matrix is
--  a set of column vectors.
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
--
@[spec]
def add_polynomials
    (p1 : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (p2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← p1[j]_?)) :
                RustM u32))
              +? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← p2[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

@[spec]
def sub_polynomials
    (p1 : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (p2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← p1[j]_?)) :
                  RustM u32))
                +? (← (rust_primitives.hax.cast_op
                  hacspec_ml_kem.parameters.FIELD_MODULUS :
                  RustM u32))))
              -? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← p2[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

@[spec]
def add_vectors (RANK : usize)
    (v1 :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (v2 :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      (add_polynomials (← v1[i]_?) (← v2[i]_?)) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

@[spec]
def transpose (RANK : usize)
    (matrix :
    (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK)) :
    RustM
    (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK)
    := do
  (hacspec_ml_kem.parameters.createi
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    (RANK)
    (usize ->
    RustM (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK))
    (fun i =>
      (do
      (hacspec_ml_kem.parameters.createi
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        (RANK)
        (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (fun j =>
          (do
          (← matrix[j]_?)[i]_? :
          RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256)))) :
      RustM
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))))

end hacspec_ml_kem.matrix


namespace hacspec_ml_kem.ntt

def ZETA : hacspec_ml_kem.parameters.FieldElement :=
  RustM.of_isOk (do (hacspec_ml_kem.parameters.Impl_9.new (17 : u16))) (by rfl)

--  Montgomery constant R = 2^16 mod q.
--  In the implementation, coefficients are stored in Montgomery form (a * R mod q).
--  In the spec, we use plain modular arithmetic, so R is conceptually 1.
--  This constant documents the correspondence.
def MONTGOMERY_R : i32 := (1 : i32)

--  Montgomery domain conversion: identity in the spec.
--
--  In the implementation, `to_standard_domain(a)` converts from Montgomery form
--  by computing `a * MONTGOMERY_R_INV mod q`. Since the spec uses plain arithmetic
--  (effectively MONTGOMERY_R = 1), this is an identity operation.
--
--  Documenting this correspondence enables function-by-function verification by
--  showing that the implementation's Montgomery conversions compose to identity.
@[spec]
def to_standard_domain (a : hacspec_ml_kem.parameters.FieldElement) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  (pure a)

--  Montgomery multiplication: identity wrapper in the spec.
--
--  In the implementation, `montgomery_multiply_by_constant(a, c)` computes
--  `a * c * R^{-1} mod q`. In the spec, this simplifies to `a * c mod q` since R = 1.
@[spec]
def montgomery_multiply_by_constant
    (a : hacspec_ml_kem.parameters.FieldElement)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  (hacspec_ml_kem.parameters.Impl_9.new
    (← (rust_primitives.hax.cast_op
      (← ((← ((← (rust_primitives.hax.cast_op
            (hacspec_ml_kem.parameters.FieldElement.val a) :
            RustM u32))
          *? (← (rust_primitives.hax.cast_op
            (hacspec_ml_kem.parameters.FieldElement.val c) :
            RustM u32))))
        %? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32)))) :
      RustM u16)))

--  Convert a field element to its unsigned representative in [0, q).
--  Corresponds to `to_unsigned_field_modulus` / `Vector::to_unsigned_representative`
--  in the implementation.
--
--  In the spec, field elements are already non-negative after reduction, so this
--  is a plain modular reduction.
@[spec]
def to_unsigned_field_modulus (a : hacspec_ml_kem.parameters.FieldElement) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  (hacspec_ml_kem.parameters.Impl_9.new
    (← ((hacspec_ml_kem.parameters.FieldElement.val a)
      %? hacspec_ml_kem.parameters.FIELD_MODULUS)))

@[spec]
def bit_rev_7 (x : usize) : RustM usize := do
  let result : usize := (0 : usize);
  let result : usize ←
    (rust_primitives.hax.folds.fold_range
      (0 : i32)
      (7 : i32)
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        if (← ((← ((← (x >>>? i)) &&&? (1 : usize))) ==? (1 : usize))) then do
          let result : usize ←
            (result |||? (← ((1 : usize) <<<? (← ((6 : i32) -? i)))));
          (pure result)
        else do
          (pure result) :
        RustM usize)));
  (pure result)
set_option maxRecDepth 1000
--  Use the Cooley–Tukey butterfly to compute an in-place NTT representation
--  of a `Polynomial`.
--
--  Given a `Polynomial` `f`, the NTT representation `f^` is:
--
--  ```plaintext
--  f^ := (f mod(X² - ζ^(2*BitRev₇(0) + 1), ..., f mod (X² − ζ^(2·BitRev₇(127) + 1))
--  ```
--
--  This function implements <strong>Algorithm 8</strong> of the NIST FIPS 203 standard, which
--  is reproduced below:
--
--  ```plaintext
--  Input: array f ∈ ℤ₂₅₆.
--  Output: array fˆ ∈ ℤ₂₅₆.
--
--  fˆ ← f
--  k ← 1
--  for (len ← 128; len ≥ 2; len ← len/2)
--      for (start ← 0; start < 256; start ← start + 2·len)
--          zeta ← ζ^(BitRev₇(k)) mod q
--          k ← k + 1
--          for (j ← start; j < start + len; j++)
--              t ← zeta·fˆ[j+len]
--              fˆ[j+len] ← fˆ[j] − t
--              fˆ[j] ← fˆ[j] + t
--          end for
--      end for
--  end for
--  return fˆ
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def ZETAS : (RustArray hacspec_ml_kem.parameters.FieldElement 128) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1729 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2580 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3289 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2642 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (630 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1897 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (848 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1062 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1919 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (193 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (797 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2786 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3260 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (569 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1746 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (296 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2447 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1339 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1476 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3046 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (56 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2240 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1333 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1426 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2094 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (535 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2882 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2393 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2879 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1974 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (821 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (289 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (331 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3253 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1756 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1197 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2304 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2277 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2055 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (650 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1977 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2513 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (632 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2865 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (33 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1320 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1915 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2319 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1435 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (807 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (452 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1438 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2868 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1534 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2402 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2647 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2617 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1481 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (648 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2474 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3110 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1227 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (910 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (17 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2761 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (583 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2649 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1637 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (723 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2288 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1100 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1409 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2662 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3281 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (233 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (756 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2156 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3015 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3050 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1703 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1651 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2789 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1789 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1847 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (952 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1461 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2687 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (939 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2308 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2437 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2388 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (733 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2337 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (268 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (641 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1584 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2298 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2037 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (3220 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (375 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2549 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2090 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1645 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1063 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (319 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2773 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (757 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2099 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (561 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2466 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2594 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2804 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1092 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (403 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1026 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1143 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2150 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2775 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (886 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1722 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1212 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1874 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (1029 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2110 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2935 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (885 : u16))),
                                (← (hacspec_ml_kem.parameters.Impl_9.new
                                  (2154 : u16)))])))
    (by rfl)

--  In the implementation, zetas are pre-multiplied by Montgomery R.
--  In the spec, ZETAS are plain values, so ZETAS_TIMES_MONTGOMERY_R == ZETAS.
--  This alias documents the correspondence with the implementation's `ZETAS_TIMES_MONTGOMERY_R`.
def ZETAS_TIMES_MONTGOMERY_R :
  (RustArray hacspec_ml_kem.parameters.FieldElement 128)
  :=
  ZETAS

def get_zeta (i : usize) : RustM hacspec_ml_kem.parameters.FieldElement := do
  let result : hacspec_ml_kem.parameters.FieldElement ← ZETAS[i]_?;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure result)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def get_zeta.spec (i : usize) :
    Spec
      (requires := do (i <? (128 : usize)))
      (ensures := fun
          r => do
          ((hacspec_ml_kem.parameters.FieldElement.val r) >=? (1 : u16)))
      (get_zeta (i : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [get_zeta] <;> sorry
}

end hacspec_ml_kem.ntt


namespace hacspec_ml_kem.invert_ntt

--  Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
--  of a `Polynomial`.
--
--  This function implements <strong>Algorithm 9</strong> of the NIST FIPS 203 standard, which
--  is reproduced below:
--
--  ```plaintext
--  Input: array fˆ ∈ ℤ₂₅₆.
--  Output: array f ∈ ℤ₂₅₆.
--
--  f ← fˆ
--  k ← 127
--  for (len ← 2; len ≤ 128; len ← 2·len)
--      for (start ← 0; start < 256; start ← start + 2·len)
--          zeta ← ζ^(BitRev₇(k)) mod q
--          k ← k − 1
--          for (j ← start; j < start + len; j++)
--              t ← f[j]
--              f[j] ← t + f[j + len]
--              f[j + len] ← zeta·(f[j+len] − t)
--          end for
--      end for
--  end for
--
--  f ← f·3303 mod q
--  return f
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
--
def ntt_inverse_layer
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (layer : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let len : usize ← ((1 : usize) <<<? layer);
  let _ := rust_primitives.hax.Tuple0.mk;
  let k : usize ← ((← ((256 : usize) /? len)) -? (1 : usize));
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      let round : usize ← (i /? (← ((2 : usize) *? len)));
      let _ := rust_primitives.hax.Tuple0.mk;
      let _ := rust_primitives.hax.Tuple0.mk;
      let idx : usize ← (i %? (← ((2 : usize) *? len)));
      let q : u32 ←
        (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32);
      if (← (idx <? len)) then do
        (hacspec_ml_kem.parameters.Impl_9.new
          (← (rust_primitives.hax.cast_op
            (← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?)) :
                  RustM u32))
                +? (← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val
                    (← p[(← (i +? len))]_?)) :
                  RustM u32))))
              %? q)) :
            RustM u16)))
      else do
        let diff : u32 ←
          ((← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?)) :
                  RustM u32))
                +? q))
              -? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val
                  (← p[(← (i -? len))]_?)) :
                RustM u32))))
            %? q);
        (hacspec_ml_kem.parameters.Impl_9.new
          (← (rust_primitives.hax.cast_op
            (← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val
                    (← (hacspec_ml_kem.ntt.get_zeta (← (k -? round))))) :
                  RustM u32))
                *? diff))
              %? q)) :
            RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      ntt_inverse_layer.spec
      (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (layer : usize) :
    Spec
      (requires := do
        ((← (layer >=? (1 : usize))) &&? (← (layer <=? (7 : usize)))))
      (ensures := fun _ => pure True)
      (ntt_inverse_layer
        (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (layer : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [ntt_inverse_layer] <;> sorry
}

@[spec]
def ntt_inverse (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (1 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (2 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (3 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (4 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (5 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (6 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_inverse_layer p (7 : usize));
  (reduce_polynomial p)

--  Inverse NTT applied to each polynomial in a vector.
@[spec]
def vector_inverse_ntt (RANK : usize)
    (vector_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      (ntt_inverse (← vector_as_ntt[i]_?)) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

end hacspec_ml_kem.invert_ntt


namespace hacspec_ml_kem.ntt

def ntt_layer
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (layer : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let len : usize ← ((1 : usize) <<<? layer);
  let _ := rust_primitives.hax.Tuple0.mk;
  let k : usize ← ((128 : usize) /? len);
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      let round : usize ← (i /? (← ((2 : usize) *? len)));
      let _ := rust_primitives.hax.Tuple0.mk;
      let _ := rust_primitives.hax.Tuple0.mk;
      let _ := rust_primitives.hax.Tuple0.mk;
      let idx : usize ← (i %? (← ((2 : usize) *? len)));
      let q : u32 ←
        (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u32);
      if (← (idx <? len)) then do
        (hacspec_ml_kem.parameters.Impl_9.new
          (← (rust_primitives.hax.cast_op
            (← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?)) :
                  RustM u32))
                +? (← ((← (rust_primitives.hax.cast_op
                    (hacspec_ml_kem.parameters.FieldElement.val
                      (← (get_zeta (← (round +? k))))) :
                    RustM u32))
                  *? (← (rust_primitives.hax.cast_op
                    (hacspec_ml_kem.parameters.FieldElement.val
                      (← p[(← (i +? len))]_?)) :
                    RustM u32))))))
              %? q)) :
            RustM u16)))
      else do
        (hacspec_ml_kem.parameters.Impl_9.new
          (← (rust_primitives.hax.cast_op
            (← ((← ((← ((← (rust_primitives.hax.cast_op
                    (hacspec_ml_kem.parameters.FieldElement.val
                      (← p[(← (i -? len))]_?)) :
                    RustM u32))
                  +? (← (q *? q))))
                -? (← ((← (rust_primitives.hax.cast_op
                    (hacspec_ml_kem.parameters.FieldElement.val
                      (← (get_zeta (← (round +? k))))) :
                    RustM u32))
                  *? (← (rust_primitives.hax.cast_op
                    (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?)) :
                    RustM u32))))))
              %? q)) :
            RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      ntt_layer.spec
      (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (layer : usize) :
    Spec
      (requires := do
        ((← (layer >=? (1 : usize))) &&? (← (layer <=? (7 : usize)))))
      (ensures := fun _ => pure True)
      (ntt_layer
        (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (layer : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [ntt_layer] <;> sorry
}

@[spec]
def ntt (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (7 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (6 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (5 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (4 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (3 : usize));
  let p : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (ntt_layer p (2 : usize));
  (ntt_layer p (1 : usize))

--  Compute the product of two `KyberBinomial`s with respect to the
--  modulus `X² - zeta`.
--
--  This function implements <strong>Algorithm 11</strong> of the NIST FIPS 203 standard, which
--  is reproduced below:
--
--  ```plaintext
--  Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
--  Input: γ ∈ ℤq.
--  Output: c₀, c₁ ∈ ℤq.
--
--  c₀ ← a₀·b₀ + a₁·b₁·γ
--  c₁ ← a₀·b₁ + a₁·b₀
--  return c₀, c₁
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
@[spec]
def base_case_multiply_even
    (a0 : hacspec_ml_kem.parameters.FieldElement)
    (a1 : hacspec_ml_kem.parameters.FieldElement)
    (b0 : hacspec_ml_kem.parameters.FieldElement)
    (b1 : hacspec_ml_kem.parameters.FieldElement)
    (zeta : hacspec_ml_kem.parameters.FieldElement) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  (hacspec_ml_kem.parameters.Impl_9.new
    (← (rust_primitives.hax.cast_op
      (← ((← ((← ((← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val a0) :
              RustM u64))
            *? (← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val b0) :
              RustM u64))))
          +? (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val a1) :
                RustM u64))
              *? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val b1) :
                RustM u64))))
            *? (← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val zeta) :
              RustM u64))))))
        %? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u64)))) :
      RustM u16)))

@[spec]
def base_case_multiply_odd
    (a0 : hacspec_ml_kem.parameters.FieldElement)
    (a1 : hacspec_ml_kem.parameters.FieldElement)
    (b0 : hacspec_ml_kem.parameters.FieldElement)
    (b1 : hacspec_ml_kem.parameters.FieldElement) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  (hacspec_ml_kem.parameters.Impl_9.new
    (← (rust_primitives.hax.cast_op
      (← ((← ((← ((← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val a0) :
              RustM u64))
            *? (← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val b1) :
              RustM u64))))
          +? (← ((← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val a1) :
              RustM u64))
            *? (← (rust_primitives.hax.cast_op
              (hacspec_ml_kem.parameters.FieldElement.val b0) :
              RustM u64))))))
        %? (← (rust_primitives.hax.cast_op
          hacspec_ml_kem.parameters.FIELD_MODULUS :
          RustM u64)))) :
      RustM u16)))

--  Given two `Polynomial`s in their NTT representations,
--  compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
--  the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:
--
--  ```plaintext
--  ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
--  ```
--
--  This function implements <strong>Algorithm 10</strong> of the NIST FIPS 203 standard, which
--  is reproduced below:
--
--  ```plaintext
--  Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
--  Output: An array ĥ ∈ ℤq.
--
--  for(i ← 0; i < 128; i++)
--      (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
--  end for
--  return ĥ
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
@[spec]
def multiply_ntts
    (p1 : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (p2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      let zeta_4 : hacspec_ml_kem.parameters.FieldElement ←
        (get_zeta (← ((64 : usize) +? (← (i /? (4 : usize))))));
      let zeta : hacspec_ml_kem.parameters.FieldElement ←
        if (← ((← (i %? (4 : usize))) <? (2 : usize))) then do
          (pure zeta_4)
        else do
          (hacspec_ml_kem.parameters.Impl_9.new
            (← (hacspec_ml_kem.parameters.FIELD_MODULUS
              -? (hacspec_ml_kem.parameters.FieldElement.val zeta_4))));
      if (← ((← (i %? (2 : usize))) ==? (0 : usize))) then do
        (base_case_multiply_even
          (← p1[i]_?)
          (← p1[(← (i +? (1 : usize)))]_?)
          (← p2[i]_?)
          (← p2[(← (i +? (1 : usize)))]_?)
          zeta)
      else do
        (base_case_multiply_odd
          (← p1[(← (i -? (1 : usize)))]_?)
          (← p1[i]_?)
          (← p2[(← (i -? (1 : usize)))]_?)
          (← p2[i]_?)) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

end hacspec_ml_kem.ntt


namespace hacspec_ml_kem.matrix

@[spec]
def multiply_matrix_by_column (RANK : usize)
    (matrix :
    (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK))
    (vector :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
        (rust_primitives.hax.repeat
          (← (hacspec_ml_kem.parameters.Impl_9.new (0 : u16)))
          (256 : usize));
      let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          RANK
          (fun result _ => (do (pure true) : RustM Bool))
          result
          (fun result j =>
            (do
            let
              product : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
              (hacspec_ml_kem.ntt.multiply_ntts
                (← (← matrix[j]_?)[i]_?)
                (← vector[j]_?));
            let
              result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
              (add_polynomials result product);
            (pure result) :
            RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
      (pure result) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

@[spec]
def multiply_vectors (RANK : usize)
    (v1 :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (v2 :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (rust_primitives.hax.repeat
      (← (hacspec_ml_kem.parameters.Impl_9.new (0 : u16)))
      (256 : usize));
  let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      RANK
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result j =>
        (do
        let product : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
          (hacspec_ml_kem.ntt.multiply_ntts (← v1[j]_?) (← v2[j]_?));
        let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
          (add_polynomials result product);
        (pure result) :
        RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
  (pure result)

--  Compute v − InverseNTT(sᵀ ◦ NTT(u)).
--  Corresponds to `compute_message` in the implementation's `matrix.rs`.
--
--  Used in K-PKE.Decrypt (Algorithm 15) to recover the message:
--    w ← v - NTT⁻¹(ŝᵀ ◦ NTT(u))
@[spec]
def compute_message (RANK : usize)
    (v : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (secret_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (u_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let inner_product : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (multiply_vectors (RANK) secret_as_ntt u_as_ntt);
  let
    inner_product_inv : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (hacspec_ml_kem.invert_ntt.ntt_inverse inner_product);
  (sub_polynomials v inner_product_inv)

--  Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message.
--  Corresponds to `compute_ring_element_v` in the implementation's `matrix.rs`.
--
--  Used in K-PKE.Encrypt (Algorithm 14):
--    v ← NTT⁻¹(t̂ᵀ ◦ r̂) + e₂ + μ
@[spec]
def compute_ring_element_v (RANK : usize)
    (t_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (r_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (error_2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (message : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let inner_product : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (multiply_vectors (RANK) t_as_ntt r_as_ntt);
  let
    inner_product_inv : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (hacspec_ml_kem.invert_ntt.ntt_inverse inner_product);
  (add_polynomials (← (add_polynomials inner_product_inv error_2)) message)

--  Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁.
--  Corresponds to `compute_vector_u` in the implementation's `matrix.rs`.
--
--  Used in K-PKE.Encrypt (Algorithm 14):
--    u ← NTT⁻¹(Âᵀ ◦ r̂) + e₁
@[spec]
def compute_vector_u (RANK : usize)
    (a_as_ntt :
    (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK))
    (r_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (error_1 :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  let
    a_transpose : (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK) ←
    (transpose (RANK) a_as_ntt);
  let
    product : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (multiply_matrix_by_column (RANK) a_transpose r_as_ntt);
  let
    product_inv : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (hacspec_ml_kem.parameters.createi
      (RustArray hacspec_ml_kem.parameters.FieldElement 256)
      (RANK)
      (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (fun i =>
        (do
        (hacspec_ml_kem.invert_ntt.ntt_inverse (← product[i]_?)) :
        RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
  (add_vectors (RANK) product_inv error_1)

--  Compute t̂ := Â ◦ ŝ + ê.
--  Corresponds to `compute_As_plus_e` in the implementation's `matrix.rs`.
--
--  Used in K-PKE.KeyGen (Algorithm 13):
--    t̂ ← Â◦ŝ + ê
@[spec]
def compute_As_plus_e (RANK : usize)
    (a_as_ntt :
    (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK))
    (s_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (error_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  let
    product : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (multiply_matrix_by_column (RANK) a_as_ntt s_as_ntt);
  (add_vectors (RANK) product error_as_ntt)

end hacspec_ml_kem.matrix


namespace hacspec_ml_kem.ntt

@[spec]
def vector_ntt (RANK : usize)
    (vector :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      (ntt (← vector[i]_?)) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

end hacspec_ml_kem.ntt


namespace hacspec_ml_kem.polynomial

--  The zero polynomial. Corresponds to `PolynomialRingElement::ZERO()` in the implementation.
@[spec]
def poly_zero (_ : rust_primitives.hax.Tuple0) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (rust_primitives.hax.repeat
    (← (hacspec_ml_kem.parameters.Impl_9.new (0 : u16)))
    (256 : usize))

--  Add `rhs` into `self` in-place. Corresponds to `PolynomialRingElement::add_to_ring_element()`.
--
--  Note: In the spec we return a new polynomial; in the implementation this is `&mut self`.
--  The mathematical operation is identical.
@[spec]
def add_to_ring_element
    (lhs : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (rhs : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← lhs[j]_?)) :
                RustM u32))
              +? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← rhs[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  Barrett reduction of all coefficients. Corresponds to `PolynomialRingElement::poly_barrett_reduce()`.
--
--  In the spec, this is a no-op modular reduction since we always work with exact arithmetic.
--  In the implementation, this is needed because intermediate values may exceed the field modulus.
@[spec]
def poly_barrett_reduce
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← ((hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?))
          %? hacspec_ml_kem.parameters.FIELD_MODULUS))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  Subtract `b` from `a` and reduce. Corresponds to `PolynomialRingElement::subtract_reduce()`.
@[spec]
def subtract_reduce
    (a : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (b : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← a[j]_?)) :
                  RustM u32))
                +? (← (rust_primitives.hax.cast_op
                  hacspec_ml_kem.parameters.FIELD_MODULUS :
                  RustM u32))))
              -? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← b[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  NTT-domain polynomial multiplication. Corresponds to `PolynomialRingElement::ntt_multiply()`.
--
--  Given two polynomials in NTT form, returns their product in NTT form.
@[spec]
def ntt_multiply
    (a : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (b : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.ntt.multiply_ntts a b)

--  Fused add(error, message, result). Corresponds to `PolynomialRingElement::add_message_error_reduce()`.
--
--  Computes: self + message + result, where:
--  - `self` is error_2
--  - `message` is the decompressed message
--  - `result` is NTT⁻¹(tᵀ ◦ r̂)
--
--  In the implementation, this fuses the addition to avoid extra temporaries.
@[spec]
def add_message_error_reduce
    (error_2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (message : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (ntt_product : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← ((← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← error_2[j]_?))
                  :
                  RustM u32))
                +? (← (rust_primitives.hax.cast_op
                  (hacspec_ml_kem.parameters.FieldElement.val (← message[j]_?))
                  :
                  RustM u32))))
              +? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val
                  (← ntt_product[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  Fused add(self, error) with reduction. Corresponds to `PolynomialRingElement::add_error_reduce()`.
--
--  Used to compute u = NTT⁻¹(Aᵀ ◦ r̂) + e₁
@[spec]
def add_error_reduce
    (ntt_product : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (error : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val
                  (← ntt_product[j]_?)) :
                RustM u32))
              +? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← error[j]_?)) :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

--  Fused add(self, error) for NTT-domain values. Corresponds to `PolynomialRingElement::add_standard_error_reduce()`.
--
--  Used to compute t̂ = Â◦ŝ + ê (both operands are in NTT domain).
@[spec]
def add_standard_error_reduce
    (ntt_product : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (error_ntt : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun j =>
      (do
      (hacspec_ml_kem.parameters.Impl_9.new
        (← (rust_primitives.hax.cast_op
          (← ((← ((← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val
                  (← ntt_product[j]_?)) :
                RustM u32))
              +? (← (rust_primitives.hax.cast_op
                (hacspec_ml_kem.parameters.FieldElement.val (← error_ntt[j]_?))
                :
                RustM u32))))
            %? (← (rust_primitives.hax.cast_op
              hacspec_ml_kem.parameters.FIELD_MODULUS :
              RustM u32)))) :
          RustM u16))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

end hacspec_ml_kem.polynomial


namespace hacspec_ml_kem.sampling

structure BadRejectionSamplingRandomnessError where
  -- no fields

@[instance] opaque Impl.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes BadRejectionSamplingRandomnessError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.fmt.Debug BadRejectionSamplingRandomnessError :=
  by constructor <;> exact Inhabited.default

def sum_coins (eta : usize) (coins : (RustSlice Bool)) :
    RustM hacspec_ml_kem.parameters.FieldElement := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let sum : u16 := (0 : u16);
  let sum : u16 ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      eta
      (fun sum i =>
        (do
        (sum <=? (← (rust_primitives.hax.cast_op i : RustM u16))) : RustM Bool))
      sum
      (fun sum i =>
        (do
        let sum : u16 ←
          (sum +? (← (rust_primitives.hax.cast_op (← coins[i]_?) : RustM u16)));
        (pure sum) :
        RustM u16)));
  (hacspec_ml_kem.parameters.Impl_9.new sum)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sum_coins.spec (eta : usize) (coins : (RustSlice Bool)) :
    Spec
      (requires := do
        ((← (eta <=? (4 : usize)))
          &&? (← ((← (core_models.slice.Impl.len Bool coins)) ==? eta))))
      (ensures := fun
          r => do
          ((hacspec_ml_kem.parameters.FieldElement.val r)
            <=? (← (rust_primitives.hax.cast_op eta : RustM u16))))
      (sum_coins (eta : usize) (coins : (RustSlice Bool))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [sum_coins] <;> sorry
}

end hacspec_ml_kem.sampling


namespace hacspec_ml_kem.serialize

def MAX_BYTES : usize := (16384 : usize)

--  Converts a set of bytes in `bytes` into a set of bits.
--
--  This function implements <strong>Algorithm 3</strong> of the NIST FIPS 203
--  standard, which is reproduced below:
--
--  ```plaintext
--  Input: byte array B ∈ 𝔹ˡ.
--  Output: bit array b ∈ {0,1}⁸ˡ.
--  for (i ← 0; i < l; i++)
--      for(j ← 0; j < 8; j++)
--          b[8i + j] ← B[i] mod 2
--          B[i] ← ⌊B[i]/2⌋
--      end for
--  end for
--  return b
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def bytes_to_bits (N : usize) (N8 : usize) (bytes : (RustArray u8 N)) :
    RustM (RustArray Bool N8) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi Bool (N8) (usize -> RustM Bool)
    (fun i =>
      (do
      ((← ((← ((← bytes[(← (i /? (8 : usize)))]_?) >>>? (← (i %? (8 : usize)))))
          &&&? (1 : u8)))
        ==? (1 : u8)) :
      RustM Bool)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def bytes_to_bits.spec (N : usize) (N8 : usize) (bytes : (RustArray u8 N)) :
    Spec
      (requires := do
        ((← (N <? (16384 : usize))) &&? (← (N8 ==? (← (N *? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (bytes_to_bits (N : usize) (N8 : usize) (bytes : (RustArray u8 N))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [bytes_to_bits] <;> sorry
}

end hacspec_ml_kem.serialize


namespace hacspec_ml_kem.sampling

--  Given a series of uniformly random bytes in `randomness`, sample
--  a ring element from a binomial distribution centered at 0 that uses two sets
--  of `eta` coin flips. If, for example,
--  `eta = ETA`, each ring coefficient is a value `v` such
--  such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
--
--  ```plaintext
--  - If v < 0, Pr[v] = Pr[-v]
--  - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
--  ```
--
--  The values `v < 0` are mapped to the appropriate `KyberFieldElement`.
--
--  The expected value is:
--
--  ```plaintext
--  E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1] + (ETA)Pr[ETA]
--       = 0 since Pr[-v] = Pr[v] when v < 0.
--  ```
--
--  And the variance is:
--
--  ```plaintext
--  Var(X) = E[(X - E[X])^2]
--         = E[X^2]
--         = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2^(2 * ETA))
--         = ETA / 2
--  ```
--
--  This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203 standard, which is
--  reproduced below:
--
--  ```plaintext
--  Input: byte array B ∈ 𝔹^{64η}.
--  Output: array f ∈ ℤ₂₅₆.
--
--  b ← BytesToBits(B)
--  for (i ← 0; i < 256; i++)
--      x ← ∑(j=0 to η - 1) b[2iη + j]
--      y ← ∑(j=0 to η - 1) b[2iη + η + j]
--      f[i] ← x−y mod q
--  end for
--  return f
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def sample_poly_cbd (ETA64 : usize) (ETA512 : usize)
    (eta : usize)
    (bytes : (RustArray u8 ETA64)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let bits : (RustArray Bool ETA512) ←
    (hacspec_ml_kem.serialize.bytes_to_bits (ETA64) (ETA512) bytes);
  (hacspec_ml_kem.parameters.createi
    hacspec_ml_kem.parameters.FieldElement
    ((256 : usize))
    (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
    (fun i =>
      (do
      let x : hacspec_ml_kem.parameters.FieldElement ←
        (sum_coins
          eta
          (← bits[
            (core_models.ops.range.Range.mk
              (start := (← ((← ((2 : usize) *? i)) *? eta)))
              (_end := (← ((← ((← ((2 : usize) *? i)) *? eta)) +? eta))))
            ]_?));
      let y : hacspec_ml_kem.parameters.FieldElement ←
        (sum_coins
          eta
          (← bits[
            (core_models.ops.range.Range.mk
              (start := (← ((← ((← ((2 : usize) *? i)) *? eta)) +? eta)))
              (_end := (← ((← ((← ((2 : usize) *? i)) *? eta))
                +? (← ((2 : usize) *? eta))))))
            ]_?));
      (hacspec_ml_kem.parameters.Impl_9.new
        (← ((← ((← ((hacspec_ml_kem.parameters.FieldElement.val x)
              +? hacspec_ml_kem.parameters.FIELD_MODULUS))
            -? (hacspec_ml_kem.parameters.FieldElement.val y)))
          %? hacspec_ml_kem.parameters.FIELD_MODULUS))) :
      RustM hacspec_ml_kem.parameters.FieldElement)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      sample_poly_cbd.spec (ETA64 : usize) (ETA512 : usize)
      (eta : usize)
      (bytes : (RustArray u8 ETA64)) :
    Spec
      (requires := do
        ((← ((← (eta <=? (4 : usize)))
            &&? (← (ETA64 ==? (← (eta *? (64 : usize)))))))
          &&? (← (ETA512 ==? (← (eta *? (512 : usize)))))))
      (ensures := fun _ => pure True)
      (sample_poly_cbd
        (ETA64 : usize)
        (ETA512 : usize)
        (eta : usize)
        (bytes : (RustArray u8 ETA64))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [sample_poly_cbd] <;> sorry
}

end hacspec_ml_kem.sampling


namespace hacspec_ml_kem.ind_cpa

--  Helper to sample a polynomial from CBD with dynamic eta.
def sample_secret (eta : usize) (prf_input : (RustArray u8 33)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  match eta with
    | 2 => do
      let out : (RustArray u8 128) ←
        (hacspec_ml_kem.parameters.hash_functions.PRF ((128 : usize))
          (← (rust_primitives.unsize prf_input)));
      (hacspec_ml_kem.sampling.sample_poly_cbd ((128 : usize)) ((1024 : usize))
        (2 : usize)
        out)
    | 3 => do
      let out : (RustArray u8 192) ←
        (hacspec_ml_kem.parameters.hash_functions.PRF ((192 : usize))
          (← (rust_primitives.unsize prf_input)));
      (hacspec_ml_kem.sampling.sample_poly_cbd ((192 : usize)) ((1536 : usize))
        (3 : usize)
        out)
    | _ => do
      let args : (rust_primitives.hax.Tuple1 usize) :=
        (rust_primitives.hax.Tuple1.mk eta);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display usize
                                (rust_primitives.hax.Tuple1._0 args)))]);
      (rust_primitives.hax.never_to_any
        (← (core_models.panicking.panic_fmt
          (← (core_models.fmt.rt.Impl_1.new_v1 ((1 : usize)) ((1 : usize))
            (RustArray.ofVec #v["unsupported eta="])
            args)))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sample_secret.spec (eta : usize) (prf_input : (RustArray u8 33)) :
    Spec
      (requires := do ((← (eta ==? (2 : usize))) ||? (← (eta ==? (3 : usize)))))
      (ensures := fun _ => pure True)
      (sample_secret (eta : usize) (prf_input : (RustArray u8 33))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [sample_secret] <;> sorry
}

end hacspec_ml_kem.ind_cpa


namespace hacspec_ml_kem.serialize

--  Converts a bit string `bits` into an array of bytes. This function asserts
--  that `bits.len()` is a multiple of 8.
--
--  This function implements <strong>Algorithm 2</strong> of the NIST FIPS 203
--  standard, which is reproduced below:
--
--  ```plaintext
--  Input: bit array b ∈ {0,1}⁸ˡ.
--  Output: byte array B ∈ 𝔹ˡ.
--
--  B ← (0,...,0)
--  for (i ← 0; i < 8l; i++)
--      B[⌊i/8⌋] ← B[⌊i/8⌋] + b[i]·2^{i} mod 8
--  end for
--  return B
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def bits_to_bytes (N : usize) (N8 : usize) (bv : (RustArray Bool N8)) :
    RustM (RustArray u8 N) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi u8 (N) (usize -> RustM u8)
    (fun i =>
      (do
      ((← ((← ((← ((← ((← ((← ((← (rust_primitives.hax.cast_op
                      (← bv[(← ((8 : usize) *? i))]_?) :
                      RustM u8))
                    |||? (← ((← (rust_primitives.hax.cast_op
                        (← bv[(← ((← ((8 : usize) *? i)) +? (1 : usize)))]_?) :
                        RustM u8))
                      <<<? (1 : i32)))))
                  |||? (← ((← (rust_primitives.hax.cast_op
                      (← bv[(← ((← ((8 : usize) *? i)) +? (2 : usize)))]_?) :
                      RustM u8))
                    <<<? (2 : i32)))))
                |||? (← ((← (rust_primitives.hax.cast_op
                    (← bv[(← ((← ((8 : usize) *? i)) +? (3 : usize)))]_?) :
                    RustM u8))
                  <<<? (3 : i32)))))
              |||? (← ((← (rust_primitives.hax.cast_op
                  (← bv[(← ((← ((8 : usize) *? i)) +? (4 : usize)))]_?) :
                  RustM u8))
                <<<? (4 : i32)))))
            |||? (← ((← (rust_primitives.hax.cast_op
                (← bv[(← ((← ((8 : usize) *? i)) +? (5 : usize)))]_?) :
                RustM u8))
              <<<? (5 : i32)))))
          |||? (← ((← (rust_primitives.hax.cast_op
              (← bv[(← ((← ((8 : usize) *? i)) +? (6 : usize)))]_?) :
              RustM u8))
            <<<? (6 : i32)))))
        |||? (← ((← (rust_primitives.hax.cast_op
            (← bv[(← ((← ((8 : usize) *? i)) +? (7 : usize)))]_?) :
            RustM u8))
          <<<? (7 : i32)))) :
      RustM u8)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def bits_to_bytes.spec (N : usize) (N8 : usize) (bv : (RustArray Bool N8)) :
    Spec
      (requires := do
        ((← (N <? (16384 : usize))) &&? (← (N8 ==? (← (N *? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (bits_to_bytes (N : usize) (N8 : usize) (bv : (RustArray Bool N8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [bits_to_bytes] <;> sorry
}

--  Convert the associated ring element into a vector of
--  `COEFFICIENTS_IN_RING_ELEMENT * bits_per_coefficient`
--  bits, and output this vector as a byte array such that the first 8 bits of
--  the vector represent the first byte of the output, the next 8 bits the
--  next byte of the output, and so on ...
--
--  N.B.: `byte_encode` is only the inverse of `byte_decode` when:
--
--  - each ring coefficient can fit into `bits_per_coefficient` (otherwise
--    lossy compression takes place)
--  - `bits_per_coefficient < BITS_PER_COEFFICIENT`, since
--    otherwise when `byte_decode` operates on 12 bits at a time,
--    it is not injective: the values 3329 + 1 and 1 for example both fit into
--    12 bits and map to the same `KyberFieldElement`
--
--  Otherwise `byte_decode` is not injective and therefore has no left inverse.
--
--  N.B.: This function asserts that `bits_per_coefficient <= 12`
--
--  This function implements <strong>Algorithm 4</strong> of the NIST FIPS 203 standard, which is
--  reproduced below:
--
--  ```plaintext
--  Input: integer array F ∈ ℤₘ²⁵⁶, where m = 2ᵈ if d < 12 and m = q if d = 12.
--  Output: byte array B ∈ 𝔹^{32d}.
--  for(i ← 0; i < 256; i++)
--      a ← F[i]
--      for(j ← 0; j < d; j++)
--          b[i·d + j] ← a mod 2
--          a ← (a − b[i·d + j])/2
--      end for
--  B ← BitsToBytes(b)
--  return B
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def bitvector_from_bounded_ints (N : usize) (Nd : usize)
    (input : (RustArray u16 N))
    (d : usize) :
    RustM (RustArray Bool Nd) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi Bool (Nd) (usize -> RustM Bool)
    (fun i =>
      (do
      ((← ((← ((← input[(← (i /? d))]_?) >>>? (← (i %? d)))) &&&? (1 : u16)))
        ==? (1 : u16)) :
      RustM Bool)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      bitvector_from_bounded_ints.spec (N : usize) (Nd : usize)
      (input : (RustArray u16 N))
      (d : usize) :
    Spec
      (requires := do
        ((← ((← (N <? (16384 : usize)))
            &&? (← (d <=? hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT))))
          &&? (← (Nd ==? (← (N *? d))))))
      (ensures := fun _ => pure True)
      (bitvector_from_bounded_ints
        (N : usize)
        (Nd : usize)
        (input : (RustArray u16 N))
        (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [bitvector_from_bounded_ints] <;> sorry
}

def byte_encode (D32 : usize) (D256 : usize)
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (d : usize) :
    RustM (RustArray u8 D32) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let p_raw : (RustArray u16 256) ←
    (hacspec_ml_kem.parameters.createi u16 ((256 : usize)) (usize -> RustM u16)
      (fun i =>
        (do
        (pure (hacspec_ml_kem.parameters.FieldElement.val (← p[i]_?))) :
        RustM u16)));
  let bv : (RustArray Bool D256) ←
    (bitvector_from_bounded_ints ((256 : usize)) (D256) p_raw d);
  (bits_to_bytes (D32) (D256) bv)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      byte_encode.spec (D32 : usize) (D256 : usize)
      (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (d : usize) :
    Spec
      (requires := do
        ((← ((← (d <=? hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT))
            &&? (← (D32 ==? (← ((32 : usize) *? d))))))
          &&? (← (D256 ==? (← ((256 : usize) *? d))))))
      (ensures := fun _ => pure True)
      (byte_encode
        (D32 : usize)
        (D256 : usize)
        (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [byte_encode] <;> sorry
}

--  Given a series of bytes representing a ring element in `re_bytes`,
--  first convert them into a vector of bits in little-endian order; i.e.
--  the least significant `bits_per_coefficient` of `re_bytes[0]`
--  are the first set of bits in the bitstream.
--
--  This vector is deserialized into a `Polynomial` structure.
--  The first `bits_per_coefficient` represent the first coefficient of
--  the ring element, the second `bits_per_coefficient` the second coefficient,
--  and so on.
--
--  N.B.: This function asserts that `bits_per_coefficient <= 12`
--
--  This function implements <strong>Algorithm 5</strong> of the NIST FIPS 203
--  standard, which is reproduced below:
--
--  ```plaintext
--  Input: byte array B ∈ 𝔹^{32d}.
--  Output: integer array F ∈ ℤₘ²⁵⁶, where m = 2ᵈ if d < 12 and m = q if d = 12.
--
--  b ← BytesToBits(B)
--  for (i ← 0; i < 256; i++)
--      F[i] ← ∑(j = 0 to d−1) b[i·d + j] · 2ʲ mod m
--  end for
--  return F
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def bitvector_to_bounded_ints (N : usize) (Nd : usize)
    (input : (RustArray Bool Nd))
    (d : usize) :
    RustM (RustArray u16 N) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let result : (RustArray u16 N) ←
    (hacspec_ml_kem.parameters.createi u16 (N) (usize -> RustM u16)
      (fun i =>
        (do
        let coefficient : u16 := (0 : u16);
        let coefficient : u16 ←
          (rust_primitives.hax.folds.fold_range
            (0 : usize)
            d
            (fun coefficient _ => (do (pure true) : RustM Bool))
            coefficient
            (fun coefficient j =>
              (do
              if (← input[(← ((← (i *? d)) +? j))]_?) then do
                let coefficient : u16 ←
                  (coefficient |||? (← ((1 : u16) <<<? j)));
                (pure coefficient)
              else do
                (pure coefficient) :
              RustM u16)));
        (pure coefficient) :
        RustM u16)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure result)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      bitvector_to_bounded_ints.spec (N : usize) (Nd : usize)
      (input : (RustArray Bool Nd))
      (d : usize) :
    Spec
      (requires := do
        ((← ((← (N <? (16384 : usize)))
            &&? (← (d <=? hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT))))
          &&? (← (Nd ==? (← (N *? d))))))
      (ensures := fun _ => pure True)
      (bitvector_to_bounded_ints
        (N : usize)
        (Nd : usize)
        (input : (RustArray Bool Nd))
        (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [bitvector_to_bounded_ints] <;> sorry
}

def byte_decode_generic (N : usize) (N8 : usize) (Nd : usize) (Nd8 : usize)
    (b : (RustArray u8 Nd))
    (d : usize) :
    RustM (RustArray u16 N8) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let bv : (RustArray Bool Nd8) ← (bytes_to_bits (Nd) (Nd8) b);
  (bitvector_to_bounded_ints (N8) (Nd8) bv d)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      byte_decode_generic.spec
      (N : usize)
      (N8 : usize)
      (Nd : usize)
      (Nd8 : usize)
      (b : (RustArray u8 Nd))
      (d : usize) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← (d >? (0 : usize)))
                    &&? (← (d
                      <=? hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT))))
                  &&? (← (N <? (← ((16384 : usize) /? d))))))
                &&? (← (N <? (← ((16384 : usize) /? (8 : usize)))))))
              &&? (← (N8 ==? (← (N *? (8 : usize)))))))
            &&? (← (Nd ==? (← (N *? d))))))
          &&? (← (Nd8 ==? (← (Nd *? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (byte_decode_generic
        (N : usize)
        (N8 : usize)
        (Nd : usize)
        (Nd8 : usize)
        (b : (RustArray u8 Nd))
        (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [byte_decode_generic] <;> sorry
}

end hacspec_ml_kem.serialize


namespace hacspec_ml_kem.sampling

--  If `bytes` contains a set of uniformly random bytes, this function
--  uniformly samples a ring element `â` that is treated as being the NTT representation
--  of the corresponding polynomial `a`.
--
--  Since rejection sampling is used, it is possible the supplied bytes are
--  not enough to sample the element, in which case an `Err` is returned and the
--  caller must try again with a fresh set of bytes.
--
--  This function <strong>partially</strong> implements <strong>Algorithm 6</strong> of the NIST FIPS 203 standard,
--  We say \"partially\" because this implementation only accepts a finite set of
--  bytes as input and returns an error if the set is not enough; Algorithm 6 of
--  the FIPS 203 standard on the other hand samples from an infinite stream of bytes
--  until the ring element is filled. Algorithm 6 is reproduced below:
--
--  ```plaintext
--  Input: byte stream B ∈ 𝔹*.
--  Output: array â ∈ ℤ₂₅₆.
--
--  i ← 0
--  j ← 0
--  while j < 256 do
--      d₁ ← B[i] + 256·(B[i+1] mod 16)
--      d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
--      if d₁ < q then
--          â[j] ← d₁
--          j ← j + 1
--      end if
--      if d₂ < q and j < 256 then
--          â[j] ← d₂
--          j ← j + 1
--      end if
--      i ← i + 3
--  end while
--  return â
--  ```
--
--  The NIST FIPS 203 standard can be found at
--  <https://csrc.nist.gov/pubs/fips/203/ipd>.
def sample_ntt (N : usize) (N8 : usize) (N12 : usize) (N96 : usize)
    (bytes : (RustArray u8 N12)) :
    RustM
    (core_models.result.Result
      (RustArray hacspec_ml_kem.parameters.FieldElement 256)
      BadRejectionSamplingRandomnessError)
    := do
  let decoded : (RustArray u16 N8) ←
    (hacspec_ml_kem.serialize.byte_decode_generic (N) (N8) (N12) (N96)
      bytes
      (12 : usize));
  let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (rust_primitives.hax.repeat
      (← (hacspec_ml_kem.parameters.Impl_9.new (0 : u16)))
      (256 : usize));
  let sampled_coefficients : usize := (0 : usize);
  let ⟨result, sampled_coefficients⟩ ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      N8
      (fun ⟨result, sampled_coefficients⟩ _ => (do (pure true) : RustM Bool))
      (rust_primitives.hax.Tuple2.mk result sampled_coefficients)
      (fun ⟨result, sampled_coefficients⟩ i =>
        (do
        if
        (← ((← ((← decoded[i]_?) <? hacspec_ml_kem.parameters.FIELD_MODULUS))
          &&? (← (sampled_coefficients <? (256 : usize))))) then do
          let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
            (rust_primitives.hax.monomorphized_update_at.update_at_usize
              result
              sampled_coefficients
              (← (hacspec_ml_kem.parameters.Impl_9.new (← decoded[i]_?))));
          (pure (rust_primitives.hax.Tuple2.mk
            result
            (← (sampled_coefficients +? (1 : usize)))))
        else do
          (pure (rust_primitives.hax.Tuple2.mk result sampled_coefficients)) :
        RustM
        (rust_primitives.hax.Tuple2
          (RustArray hacspec_ml_kem.parameters.FieldElement 256)
          usize))));
  if (← (sampled_coefficients ==? (256 : usize))) then do
    (pure (core_models.result.Result.Ok result))
  else do
    (pure (core_models.result.Result.Err
      BadRejectionSamplingRandomnessError.mk))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      sample_ntt.spec (N : usize) (N8 : usize) (N12 : usize) (N96 : usize)
      (bytes : (RustArray u8 N12)) :
    Spec
      (requires := do
        ((← ((← ((← (N
                <=? (← (hacspec_ml_kem.serialize.MAX_BYTES /? (96 : usize)))))
              &&? (← (N8 ==? (← (N *? (8 : usize)))))))
            &&? (← (N12 ==? (← (N *? (12 : usize)))))))
          &&? (← (N96 ==? (← (N12 *? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (sample_ntt
        (N : usize)
        (N8 : usize)
        (N12 : usize)
        (N96 : usize)
        (bytes : (RustArray u8 N12))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [sample_ntt] <;> sorry
}

end hacspec_ml_kem.sampling


namespace hacspec_ml_kem.matrix

--  Sample the matrix A from a seed. Corresponds to `sample_matrix_A` in the implementation.
--
--  When `transpose` is true, A_transpose[j][i] = sampled(i, j).
--  When `transpose` is false, A_transpose[i][j] = sampled(i, j).
def sample_matrix_A (RANK : usize)
    (seed_for_A : (RustSlice u8))
    (transpose : Bool) :
    RustM
    (core_models.result.Result
      (RustArray
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
      RANK)
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let
    A_as_ntt : (RustArray
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    RANK) ←
    (rust_primitives.hax.repeat
      (← (rust_primitives.hax.repeat
        (← (rust_primitives.hax.repeat
          (← (hacspec_ml_kem.parameters.Impl_9.new (0 : u16)))
          (256 : usize)))
        RANK))
      RANK);
  let xof_input : (RustArray u8 34) ←
    (rust_primitives.hax.repeat (0 : u8) (34 : usize));
  let xof_input : (RustArray u8 34) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      xof_input
      (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← xof_input[
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          ]_?)
        seed_for_A)));
  match
    (← (rust_primitives.hax.folds.fold_range_return
      (0 : usize)
      RANK
      (fun ⟨A_as_ntt, xof_input⟩ _ => (do (pure true) : RustM Bool))
      (rust_primitives.hax.Tuple2.mk A_as_ntt xof_input)
      (fun ⟨A_as_ntt, xof_input⟩ i =>
        (do
        match
          (← (rust_primitives.hax.folds.fold_range_return
            (0 : usize)
            RANK
            (fun ⟨A_as_ntt, xof_input⟩ _ => (do (pure true) : RustM Bool))
            (rust_primitives.hax.Tuple2.mk A_as_ntt xof_input)
            (fun ⟨A_as_ntt, xof_input⟩ j =>
              (do
              let xof_input : (RustArray u8 34) ←
                (rust_primitives.hax.monomorphized_update_at.update_at_usize
                  xof_input
                  (32 : usize)
                  (← (rust_primitives.hax.cast_op i : RustM u8)));
              let xof_input : (RustArray u8 34) ←
                (rust_primitives.hax.monomorphized_update_at.update_at_usize
                  xof_input
                  (33 : usize)
                  (← (rust_primitives.hax.cast_op j : RustM u8)));
              let xof_bytes : (RustArray u8 840) ←
                (hacspec_ml_kem.parameters.hash_functions.XOF ((840 : usize))
                  (← (rust_primitives.unsize xof_input)));
              match
                (← (hacspec_ml_kem.sampling.sample_ntt
                  ((70 : usize))
                  ((560 : usize))
                  ((840 : usize))
                  ((6720 : usize)) xof_bytes))
              with
                | (core_models.result.Result.Ok  sampled) => do
                  if transpose then do
                    let
                      A_as_ntt : (RustArray
                      (RustArray
                      (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                      RANK)
                      RANK) ←
                      (rust_primitives.hax.monomorphized_update_at.update_at_usize
                        A_as_ntt
                        j
                        (←
                        (rust_primitives.hax.monomorphized_update_at.update_at_usize
                          (← A_as_ntt[j]_?)
                          i
                          sampled)));
                    (pure (core_models.ops.control_flow.ControlFlow.Continue
                      (rust_primitives.hax.Tuple2.mk A_as_ntt xof_input)))
                  else do
                    let
                      A_as_ntt : (RustArray
                      (RustArray
                      (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                      RANK)
                      RANK) ←
                      (rust_primitives.hax.monomorphized_update_at.update_at_usize
                        A_as_ntt
                        i
                        (←
                        (rust_primitives.hax.monomorphized_update_at.update_at_usize
                          (← A_as_ntt[i]_?)
                          j
                          sampled)));
                    (pure (core_models.ops.control_flow.ControlFlow.Continue
                      (rust_primitives.hax.Tuple2.mk A_as_ntt xof_input)))
                | (core_models.result.Result.Err  err) => do
                  (pure (core_models.ops.control_flow.ControlFlow.Break
                    (core_models.ops.control_flow.ControlFlow.Break
                      (core_models.result.Result.Err err)))) :
              RustM
              (core_models.ops.control_flow.ControlFlow
                (core_models.ops.control_flow.ControlFlow
                  (core_models.result.Result
                    (RustArray
                    (RustArray
                    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                    RANK)
                    RANK)
                    hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
                  (rust_primitives.hax.Tuple2
                    rust_primitives.hax.Tuple0
                    (rust_primitives.hax.Tuple2
                      (RustArray
                      (RustArray
                      (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                      RANK)
                      RANK)
                      (RustArray u8 34))))
                (rust_primitives.hax.Tuple2
                  (RustArray
                  (RustArray
                  (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                  RANK)
                  RANK)
                  (RustArray u8 34)))))))
        with
          | (core_models.ops.control_flow.ControlFlow.Break  ret) => do
            (pure (core_models.ops.control_flow.ControlFlow.Break
              (core_models.ops.control_flow.ControlFlow.Break ret)))
          | (core_models.ops.control_flow.ControlFlow.Continue  loop_res) => do
            (pure (core_models.ops.control_flow.ControlFlow.Continue loop_res))
        :
        RustM
        (core_models.ops.control_flow.ControlFlow
          (core_models.ops.control_flow.ControlFlow
            (core_models.result.Result
              (RustArray
              (RustArray
              (RustArray hacspec_ml_kem.parameters.FieldElement 256)
              RANK)
              RANK)
              hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
            (rust_primitives.hax.Tuple2
              rust_primitives.hax.Tuple0
              (rust_primitives.hax.Tuple2
                (RustArray
                (RustArray
                (RustArray hacspec_ml_kem.parameters.FieldElement 256)
                RANK)
                RANK)
                (RustArray u8 34))))
          (rust_primitives.hax.Tuple2
            (RustArray
            (RustArray
            (RustArray hacspec_ml_kem.parameters.FieldElement 256)
            RANK)
            RANK)
            (RustArray u8 34)))))))
  with
    | (core_models.ops.control_flow.ControlFlow.Break  ret) => do (pure ret)
    | (core_models.ops.control_flow.ControlFlow.Continue  ⟨A_as_ntt, xof_input⟩)
      => do
      (pure (core_models.result.Result.Ok A_as_ntt))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      sample_matrix_A.spec (RANK : usize)
      (seed_for_A : (RustSlice u8))
      (transpose : Bool) :
    Spec
      (requires := do
        ((← ((← (core_models.slice.Impl.len u8 seed_for_A)) ==? (32 : usize)))
          &&? (← (RANK <=? (4 : usize)))))
      (ensures := fun _ => pure True)
      (sample_matrix_A
        (RANK : usize)
        (seed_for_A : (RustSlice u8))
        (transpose : Bool)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [sample_matrix_A] <;> sorry
}

end hacspec_ml_kem.matrix


namespace hacspec_ml_kem.serialize

def byte_decode (D32 : usize) (D256 : usize)
    (b : (RustArray u8 D32))
    (d : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let decoded : (RustArray u16 256) ←
    (byte_decode_generic ((32 : usize)) ((256 : usize)) (D32) (D256) b d);
  let result : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (hacspec_ml_kem.parameters.createi
      hacspec_ml_kem.parameters.FieldElement
      ((256 : usize))
      (usize -> RustM hacspec_ml_kem.parameters.FieldElement)
      (fun i =>
        (do
        (hacspec_ml_kem.parameters.Impl_9.new
          (← ((← decoded[i]_?) %? hacspec_ml_kem.parameters.FIELD_MODULUS))) :
        RustM hacspec_ml_kem.parameters.FieldElement)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure result)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      byte_decode.spec (D32 : usize) (D256 : usize)
      (b : (RustArray u8 D32))
      (d : usize) :
    Spec
      (requires := do
        ((← ((← ((← ((← (d >? (0 : usize)))
                &&? (← (d <=? hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT))))
              &&? (← ((← (core_models.slice.Impl.len u8
                  (← (rust_primitives.unsize b))))
                ==? (← ((32 : usize) *? d))))))
            &&? (← (D32 ==? (← ((32 : usize) *? d))))))
          &&? (← (D256 ==? (← ((256 : usize) *? d))))))
      (ensures := fun
          result => do
          (hax_lib.prop.constructors.forall
            (fun i =>
              (do
              (hax_lib.prop.constructors.implies
                (← (hax_lib.prop.constructors.from_bool
                  (← (i <? (256 : usize)))))
                (← (hax_lib.prop.constructors.from_bool
                  (← ((hacspec_ml_kem.parameters.FieldElement.val
                      (← result[i]_?))
                    <? (← ((1 : u16) <<<? d))))))) :
              RustM hax_lib.prop.Prop))))
      (byte_decode
        (D32 : usize)
        (D256 : usize)
        (b : (RustArray u8 D32))
        (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [byte_decode] <;> sorry
}

end hacspec_ml_kem.serialize


namespace hacspec_ml_kem.ind_cca

--  Modulus check for encapsulation key validation (FIPS 203 Section 7.2).
--
--  Verifies that ByteEncode₁₂(ByteDecode₁₂(ek[..384k])) == ek[..384k].
def public_key_modulus_check (EK_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (ek : (RustArray u8 EK_SIZE)) :
    RustM Bool := do
  let t_size : usize ←
    (hacspec_ml_kem.parameters.Impl.t_as_ntt_encoded_size params);
  let encoded_ring_elements : (RustSlice u8) ←
    ek[(core_models.ops.range.RangeTo.mk (_end := t_size))]_?;
  let valid : Bool := true;
  let valid : Bool ←
    (rust_primitives.hax.folds.fold_chunked_slice
      hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT
      encoded_ring_elements
      (fun valid _ => (do (pure true) : RustM Bool))
      valid
      (fun valid chunk =>
        (do
        let decoded : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
          (hacspec_ml_kem.serialize.byte_decode ((384 : usize)) ((3072 : usize))
            (← (core_models.result.Impl.unwrap
              (RustArray u8 384)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 384) chunk))))
            (12 : usize));
        let re_encoded : (RustArray u8 384) ←
          (hacspec_ml_kem.serialize.byte_encode ((384 : usize)) ((3072 : usize))
            decoded
            (12 : usize));
        if
        (← (core_models.cmp.PartialEq.ne
          (RustSlice u8)
          (RustSlice u8)
          chunk
          (← (core_models.array.Impl_23.as_slice u8 ((384 : usize))
            re_encoded)))) then do
          let valid : Bool := false;
          (pure valid)
        else do
          (pure valid) :
        RustM Bool)));
  (pure valid)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      public_key_modulus_check.spec (EK_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (ek : (RustArray u8 EK_SIZE)) :
    Spec
      (requires := do
        ((← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
            <=? (4 : usize)))
          &&? (← (EK_SIZE
            ==? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
                *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
              +? (32 : usize)))))))
      (ensures := fun _ => pure True)
      (public_key_modulus_check
        (EK_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (ek : (RustArray u8 EK_SIZE))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [public_key_modulus_check] <;> sorry
}

end hacspec_ml_kem.ind_cca


namespace hacspec_ml_kem.serialize

def vector_encode_12 (RANK : usize) (T_SIZE : usize)
    (vector :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM (RustArray u8 T_SIZE) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let out : (RustArray u8 T_SIZE) ←
    (rust_primitives.hax.repeat (0 : u8) T_SIZE);
  let out : (RustArray u8 T_SIZE) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      RANK
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let encoded : (RustArray u8 384) ←
          (byte_encode ((384 : usize)) ((3072 : usize))
            (← vector[i]_?)
            (12 : usize));
        let out : (RustArray u8 T_SIZE) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← (i *? (384 : usize))))
              (_end := (← ((← (i +? (1 : usize))) *? (384 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← (i *? (384 : usize))))
                  (_end := (← ((← (i +? (1 : usize))) *? (384 : usize)))))
                ]_?)
              (← (rust_primitives.unsize encoded)))));
        (pure out) :
        RustM (RustArray u8 T_SIZE))));
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      vector_encode_12.spec (RANK : usize) (T_SIZE : usize)
      (vector :
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    Spec
      (requires := do
        ((← (RANK <=? (4 : usize)))
          &&? (← (T_SIZE
            ==? (← (RANK
              *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
      (ensures := fun _ => pure True)
      (vector_encode_12
        (RANK : usize)
        (T_SIZE : usize)
        (vector :
        (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [vector_encode_12] <;> sorry
}

def vector_decode_12 (RANK : usize) (encoded : (RustSlice u8)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      let start : usize ←
        (i *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT);
      let chunk : (RustArray u8 384) ←
        (core_models.result.Impl.unwrap
          (RustArray u8 384)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 384)
            (← encoded[
              (core_models.ops.range.Range.mk
                (start := start)
                (_end := (← (start +? (384 : usize)))))
              ]_?))));
      (byte_decode ((384 : usize)) ((3072 : usize)) chunk (12 : usize)) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def vector_decode_12.spec (RANK : usize) (encoded : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (RANK <=? (4 : usize)))
          &&? (← ((← (core_models.slice.Impl.len u8 encoded))
            ==? (← (RANK
              *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
      (ensures := fun _ => pure True)
      (vector_decode_12 (RANK : usize) (encoded : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [vector_decode_12] <;> sorry
}

def byte_encode_into
    (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (d : usize)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let out : (RustSlice u8) ←
    match d with
      | 1 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((32 : usize)) ((256 : usize)) p (1 : usize))))))
      | 4 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((128 : usize)) ((1024 : usize)) p (4 : usize))))))
      | 5 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((160 : usize)) ((1280 : usize)) p (5 : usize))))))
      | 10 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((320 : usize)) ((2560 : usize)) p (10 : usize))))))
      | 11 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((352 : usize)) ((2816 : usize)) p (11 : usize))))))
      | 12 => do
        (core_models.slice.Impl.copy_from_slice u8
          out
          (← (rust_primitives.unsize
            (← (byte_encode ((384 : usize)) ((3072 : usize)) p (12 : usize))))))
      | _ => do
        let args : (rust_primitives.hax.Tuple1 usize) :=
          (rust_primitives.hax.Tuple1.mk d);
        let args : (RustArray core_models.fmt.rt.Argument 1) :=
          (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display usize
                                  (rust_primitives.hax.Tuple1._0 args)))]);
        (pure out);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      byte_encode_into.spec
      (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (d : usize)
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← (d ==? (1 : usize)))
                    ||? (← (d ==? (4 : usize)))))
                  ||? (← (d ==? (5 : usize)))))
                ||? (← (d ==? (10 : usize)))))
              ||? (← (d ==? (11 : usize)))))
            ||? (← (d ==? (12 : usize)))))
          &&? (← ((← (core_models.slice.Impl.len u8 out))
            ==? (← ((32 : usize) *? d))))))
      (ensures := fun _ => pure True)
      (byte_encode_into
        (p : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (d : usize)
        (out : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [byte_encode_into] <;> sorry
}

def byte_decode_dyn (b : (RustSlice u8)) (d : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  match d with
    | 1 => do
      (byte_decode ((32 : usize)) ((256 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 32)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 32) b))))
        (1 : usize))
    | 4 => do
      (byte_decode ((128 : usize)) ((1024 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 128)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 128) b))))
        (4 : usize))
    | 5 => do
      (byte_decode ((160 : usize)) ((1280 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 160)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 160) b))))
        (5 : usize))
    | 10 => do
      (byte_decode ((320 : usize)) ((2560 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 320)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 320) b))))
        (10 : usize))
    | 11 => do
      (byte_decode ((352 : usize)) ((2816 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 352)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 352) b))))
        (11 : usize))
    | 12 => do
      (byte_decode ((384 : usize)) ((3072 : usize))
        (← (core_models.result.Impl.unwrap
          (RustArray u8 384)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 384) b))))
        (12 : usize))
    | _ => do
      let args : (rust_primitives.hax.Tuple1 usize) :=
        (rust_primitives.hax.Tuple1.mk d);
      let args : (RustArray core_models.fmt.rt.Argument 1) :=
        (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display usize
                                (rust_primitives.hax.Tuple1._0 args)))]);
      (rust_primitives.hax.never_to_any
        (← (core_models.panicking.panic_fmt
          (← (core_models.fmt.rt.Impl_1.new_v1 ((1 : usize)) ((1 : usize))
            (RustArray.ofVec #v["unsupported d="])
            args)))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def byte_decode_dyn.spec (b : (RustSlice u8)) (d : usize) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← (d ==? (1 : usize)))
                    ||? (← (d ==? (4 : usize)))))
                  ||? (← (d ==? (5 : usize)))))
                ||? (← (d ==? (10 : usize)))))
              ||? (← (d ==? (11 : usize)))))
            ||? (← (d ==? (12 : usize)))))
          &&? (← ((← (core_models.slice.Impl.len u8 b))
            ==? (← ((32 : usize) *? d))))))
      (ensures := fun _ => pure True)
      (byte_decode_dyn (b : (RustSlice u8)) (d : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [byte_decode_dyn] <;> sorry
}

--  Compress a polynomial to 1 bit per coefficient, then serialize to bytes.
--  Corresponds to `compress_then_serialize_message` in the implementation.
--
--  Used for encoding/decoding the message in K-PKE.
@[spec]
def compress_then_serialize_message
    (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray u8 32) := do
  (byte_encode ((32 : usize)) ((256 : usize))
    (← (hacspec_ml_kem.compress.compress re (1 : usize)))
    (1 : usize))

--  Deserialize bytes to a polynomial, then decompress from 1 bit per coefficient.
--  Corresponds to `deserialize_then_decompress_message` in the implementation.
@[spec]
def deserialize_then_decompress_message (serialized : (RustArray u8 32)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.compress.decompress
    (← (byte_decode ((32 : usize)) ((256 : usize)) serialized (1 : usize)))
    (1 : usize))

--  Serialize a polynomial with 12-bit coefficients (no compression).
--  Corresponds to `serialize_uncompressed_ring_element` in the implementation.
@[spec]
def serialize_uncompressed_ring_element
    (re : (RustArray hacspec_ml_kem.parameters.FieldElement 256)) :
    RustM (RustArray u8 384) := do
  (byte_encode ((384 : usize)) ((3072 : usize)) re (12 : usize))

--  Deserialize bytes to a polynomial with 12-bit coefficients (no decompression).
--  Corresponds to `deserialize_to_uncompressed_ring_element` in the implementation.
@[spec]
def deserialize_to_uncompressed_ring_element (serialized : (RustArray u8 384)) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (byte_decode ((384 : usize)) ((3072 : usize)) serialized (12 : usize))

--  Compress each polynomial in u to du bits, then serialize.
--  Corresponds to `compress_then_serialize_ring_element_u` in the implementation.
--
--  Note: The implementation dispatches on the compression factor (10 or 11).
--  In the spec we use the generic compress + byte_encode path.
def compress_then_serialize_u (RANK : usize) (U_SIZE : usize)
    (u :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (du : usize) :
    RustM (RustArray u8 U_SIZE) := do
  let du_poly_size : usize ←
    ((← (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT *? du))
      /? (8 : usize));
  let out : (RustArray u8 U_SIZE) ←
    (rust_primitives.hax.repeat (0 : u8) U_SIZE);
  let out : (RustArray u8 U_SIZE) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      RANK
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out
          (core_models.ops.range.Range.mk
            (start := (← (i *? du_poly_size)))
            (_end := (← ((← (i +? (1 : usize))) *? du_poly_size))))
          (← (byte_encode_into
            (← (hacspec_ml_kem.compress.compress (← u[i]_?) du))
            du
            (← out[
              (core_models.ops.range.Range.mk
                (start := (← (i *? du_poly_size)))
                (_end := (← ((← (i +? (1 : usize))) *? du_poly_size))))
              ]_?)))) :
        RustM (RustArray u8 U_SIZE))));
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      compress_then_serialize_u.spec (RANK : usize) (U_SIZE : usize)
      (u :
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
      (du : usize) :
    Spec
      (requires := do
        ((← ((← (RANK <=? (4 : usize)))
            &&? (← ((← (du ==? (10 : usize))) ||? (← (du ==? (11 : usize)))))))
          &&? (← (U_SIZE
            ==? (← ((← ((← (RANK
                  *? hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                *? du))
              /? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (compress_then_serialize_u
        (RANK : usize)
        (U_SIZE : usize)
        (u :
        (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
        (du : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [compress_then_serialize_u] <;> sorry
}

--  Compress v to dv bits, then serialize.
--  Corresponds to `compress_then_serialize_ring_element_v` in the implementation.
def compress_then_serialize_v (V_SIZE : usize)
    (v : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (dv : usize) :
    RustM (RustArray u8 V_SIZE) := do
  let out : (RustArray u8 V_SIZE) ←
    (rust_primitives.hax.repeat (0 : u8) V_SIZE);
  let out : (RustArray u8 V_SIZE) ←
    (byte_encode_into (← (hacspec_ml_kem.compress.compress v dv)) dv out);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      compress_then_serialize_v.spec (V_SIZE : usize)
      (v : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
      (dv : usize) :
    Spec
      (requires := do
        ((← ((← (dv ==? (4 : usize))) ||? (← (dv ==? (5 : usize)))))
          &&? (← (V_SIZE
            ==? (← ((← (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                *? dv))
              /? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (compress_then_serialize_v
        (V_SIZE : usize)
        (v : (RustArray hacspec_ml_kem.parameters.FieldElement 256))
        (dv : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [compress_then_serialize_v] <;> sorry
}

--  Deserialize and decompress u from ciphertext bytes.
--  Corresponds to `deserialize_then_decompress_ring_element_u` in the implementation.
def deserialize_then_decompress_u (RANK : usize)
    (ciphertext : (RustSlice u8))
    (du : usize) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  let du_poly_size : usize ←
    ((← (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT *? du))
      /? (8 : usize));
  (hacspec_ml_kem.parameters.createi
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    (RANK)
    (usize -> RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
    (fun i =>
      (do
      let start : usize ← (i *? du_poly_size);
      (hacspec_ml_kem.compress.decompress
        (← (byte_decode_dyn
          (← ciphertext[
            (core_models.ops.range.Range.mk
              (start := start)
              (_end := (← (start +? du_poly_size))))
            ]_?)
          du))
        du) :
      RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      deserialize_then_decompress_u.spec (RANK : usize)
      (ciphertext : (RustSlice u8))
      (du : usize) :
    Spec
      (requires := do
        ((← ((← (RANK <=? (4 : usize)))
            &&? (← ((← (du ==? (10 : usize))) ||? (← (du ==? (11 : usize)))))))
          &&? (← ((← (core_models.slice.Impl.len u8 ciphertext))
            ==? (← ((← ((← (RANK
                  *? hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                *? du))
              /? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (deserialize_then_decompress_u
        (RANK : usize)
        (ciphertext : (RustSlice u8))
        (du : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [deserialize_then_decompress_u] <;> sorry
}

--  Deserialize and decompress v from ciphertext bytes.
--  Corresponds to `deserialize_then_decompress_ring_element_v` in the implementation.
def deserialize_then_decompress_v (serialized : (RustSlice u8)) (dv : usize) :
    RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256) := do
  (hacspec_ml_kem.compress.decompress (← (byte_decode_dyn serialized dv)) dv)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      deserialize_then_decompress_v.spec
      (serialized : (RustSlice u8))
      (dv : usize) :
    Spec
      (requires := do
        ((← ((← (dv ==? (4 : usize))) ||? (← (dv ==? (5 : usize)))))
          &&? (← ((← (core_models.slice.Impl.len u8 serialized))
            ==? (← ((← (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                *? dv))
              /? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (deserialize_then_decompress_v (serialized : (RustSlice u8)) (dv : usize))
    := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [deserialize_then_decompress_v] <;> sorry
}

--  Deserialize ring elements from a byte slice, reducing mod q.
--  Corresponds to `deserialize_ring_elements_reduced` in the implementation.
--
--  This is equivalent to `vector_decode_12` but named to match the implementation.
def deserialize_ring_elements_reduced (RANK : usize)
    (encoded : (RustSlice u8)) :
    RustM
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)
    := do
  (vector_decode_12 (RANK) encoded)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      deserialize_ring_elements_reduced.spec (RANK : usize)
      (encoded : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (RANK <=? (4 : usize)))
          &&? (← ((← (core_models.slice.Impl.len u8 encoded))
            ==? (← (RANK
              *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
      (ensures := fun _ => pure True)
      (deserialize_ring_elements_reduced
        (RANK : usize)
        (encoded : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [deserialize_ring_elements_reduced] <;> sorry
}

end hacspec_ml_kem.serialize


namespace hacspec_ml_kem.ind_cpa

--  Algorithm 14: K-PKE.Encrypt
--
--  Uses the encryption key to encrypt a plaintext message using the randomness r.
--
--  ```plaintext
--  Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
--  Input: message m ∈ 𝔹^{32}.
--  Input: encryption randomness r ∈ 𝔹^{32}.
--  Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
--
--  N ← 0
--  t\u{302} ← ByteDecode₁₂(ekₚₖₑ[0:384k])
--  ρ ← ekₚₖₑ[384k: 384k + 32]
--  for (i ← 0; i < k; i++)
--      for(j ← 0; j < k; j++)
--          Â[i,j] ← SampleNTT(XOF(ρ, j, i))
--      end for
--  end for
--  for(i ← 0; i < k; i++)
--      r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
--      N ← N + 1
--  end for
--  for(i ← 0; i < k; i++)
--      e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
--      N ← N + 1
--  end for
--  e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
--  r\u{302} ← NTT(r)
--  u ← NTT⁻¹(Âᵀ ◦ r\u{302}) + e₁
--  μ ← Decompress₁(ByteDecode₁(m))
--  v ← NTT⁻¹(t\u{302}ᵀ ◦ r\u{302}) + e₂ + μ
--  c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
--  c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
--  return c ← (c₁ ‖ c₂)
--  ```
def encrypt (RANK : usize) (U_SIZE : usize) (V_SIZE : usize) (CT_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (ek : (RustSlice u8))
    (message : (RustArray u8 32))
    (randomness : (RustArray u8 32)) :
    RustM
    (core_models.result.Result
      (RustArray u8 CT_SIZE)
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let t_encoded_size : usize ←
    (hacspec_ml_kem.parameters.Impl.t_as_ntt_encoded_size params);
  let
    t_as_ntt : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (hacspec_ml_kem.serialize.deserialize_ring_elements_reduced (RANK)
      (← ek[(core_models.ops.range.RangeTo.mk (_end := t_encoded_size))]_?));
  let seed_for_A : (RustSlice u8) ←
    ek[(core_models.ops.range.RangeFrom.mk (start := t_encoded_size))]_?;
  match (← (hacspec_ml_kem.matrix.sample_matrix_A (RANK) seed_for_A false)) with
    | (core_models.result.Result.Ok  A_as_ntt) => do
      let
        r : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.parameters.createi
          (RustArray hacspec_ml_kem.parameters.FieldElement 256)
          (RANK)
          (usize ->
          RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
          (fun i =>
            (do
            let prf_input : (RustArray u8 33) ←
              (concat_byte ((32 : usize)) ((33 : usize))
                (← (core_models.result.Impl.unwrap
                  (RustArray u8 32)
                  core_models.convert.Infallible
                  (← (core_models.convert.TryInto.try_into
                    (RustArray u8 32)
                    (RustArray u8 32) randomness))))
                (← (rust_primitives.hax.cast_op i : RustM u8)));
            (sample_secret
              (hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              prf_input) :
            RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
      let
        error_1 : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.parameters.createi
          (RustArray hacspec_ml_kem.parameters.FieldElement 256)
          (RANK)
          (usize ->
          RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
          (fun i =>
            (do
            let prf_input : (RustArray u8 33) ←
              (concat_byte ((32 : usize)) ((33 : usize))
                (← (core_models.result.Impl.unwrap
                  (RustArray u8 32)
                  core_models.convert.Infallible
                  (← (core_models.convert.TryInto.try_into
                    (RustArray u8 32)
                    (RustArray u8 32) randomness))))
                (← (rust_primitives.hax.cast_op (← (RANK +? i)) : RustM u8)));
            (sample_secret
              (hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              prf_input) :
            RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
      let prf_input : (RustArray u8 33) ←
        (rust_primitives.hax.repeat (0 : u8) (33 : usize));
      let prf_input : (RustArray u8 33) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_to
          prf_input
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← prf_input[
              (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
              ]_?)
            (← (rust_primitives.unsize randomness)))));
      let prf_input : (RustArray u8 33) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          prf_input
          (32 : usize)
          (← (rust_primitives.hax.cast_op
            (← (RANK *? (2 : usize))) :
            RustM u8)));
      let error_2 : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
        (sample_secret
          (hacspec_ml_kem.parameters.MlKemParams.eta2 params)
          prf_input);
      let
        r_as_ntt : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.ntt.vector_ntt (RANK) r);
      let
        u : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.matrix.compute_vector_u (RANK)
          A_as_ntt
          r_as_ntt
          error_1);
      let
        message_as_ring_element : (RustArray
        hacspec_ml_kem.parameters.FieldElement
        256) ←
        (hacspec_ml_kem.serialize.deserialize_then_decompress_message message);
      let v : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
        (hacspec_ml_kem.matrix.compute_ring_element_v (RANK)
          t_as_ntt
          r_as_ntt
          error_2
          message_as_ring_element);
      let c1 : (RustArray u8 U_SIZE) ←
        (hacspec_ml_kem.serialize.compress_then_serialize_u (RANK) (U_SIZE)
          u
          (hacspec_ml_kem.parameters.MlKemParams.du params));
      let c2 : (RustArray u8 V_SIZE) ←
        (hacspec_ml_kem.serialize.compress_then_serialize_v (V_SIZE)
          v
          (hacspec_ml_kem.parameters.MlKemParams.dv params));
      let c : (RustArray u8 CT_SIZE) ←
        (rust_primitives.hax.repeat (0 : u8) CT_SIZE);
      let c : (RustArray u8 CT_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_to
          c
          (core_models.ops.range.RangeTo.mk (_end := U_SIZE))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← c[(core_models.ops.range.RangeTo.mk (_end := U_SIZE))]_?)
            (← (rust_primitives.unsize c1)))));
      let c : (RustArray u8 CT_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_from
          c
          (core_models.ops.range.RangeFrom.mk (start := U_SIZE))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← c[(core_models.ops.range.RangeFrom.mk (start := U_SIZE))]_?)
            (← (rust_primitives.unsize c2)))));
      (pure (core_models.result.Result.Ok c))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      encrypt.spec
      (RANK : usize)
      (U_SIZE : usize)
      (V_SIZE : usize)
      (CT_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (ek : (RustSlice u8))
      (message : (RustArray u8 32))
      (randomness : (RustArray u8 32)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                      &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank
                          params)
                        ==? RANK))))
                    &&? (← (U_SIZE
                      ==? (← ((← ((← (RANK
                            *?
                            hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                          *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                        /? (8 : usize)))))))
                  &&? (← (V_SIZE
                    ==? (← ((←
                      (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                        *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))
                      /? (8 : usize)))))))
                &&? (← (CT_SIZE ==? (← (U_SIZE +? V_SIZE))))))
              &&? (← ((← (core_models.slice.Impl.len u8 ek))
                ==? (← ((← (RANK
                    *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                  +? (32 : usize)))))))
            &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (2 : usize)))
              ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (3 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (encrypt
        (RANK : usize)
        (U_SIZE : usize)
        (V_SIZE : usize)
        (CT_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (ek : (RustSlice u8))
        (message : (RustArray u8 32))
        (randomness : (RustArray u8 32))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [encrypt] <;> sorry
}

end hacspec_ml_kem.ind_cpa


namespace hacspec_ml_kem.ind_cca

--  Algorithm 17: ML-KEM.Encaps_internal
--
--  ```plaintext
--  Input: encapsulation key ek ∈ 𝔹^{384k+32}.
--  Input: m ∈ 𝔹³².
--  Output: shared key K ∈ 𝔹³².
--  Output: ciphertext c ∈ 𝔹^{32(dᵤk+dᵥ)}.
--
--  (K, r) ← G(m ‖ H(ek))
--  c ← K-PKE.Encrypt(ek, m, r)
--  return (K, c)
--  ```
def encaps_internal
    (RANK : usize)
    (U_SIZE : usize)
    (V_SIZE : usize)
    (CT_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (ek : (RustSlice u8))
    (m : (RustArray u8 32)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 (RustArray u8 32) (RustArray u8 CT_SIZE))
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.repeat (0 : u8) (64 : usize));
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      to_hash
      (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← to_hash[(core_models.ops.range.RangeTo.mk (_end := (32 : usize)))]_?)
        (← (rust_primitives.unsize m)))));
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      to_hash
      (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← to_hash[
          (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
          ]_?)
        (← (rust_primitives.unsize
          (← (hacspec_ml_kem.parameters.hash_functions.H ek)))))));
  let hashed : (RustArray u8 64) ←
    (hacspec_ml_kem.parameters.hash_functions.G
      (← (rust_primitives.unsize to_hash)));
  let ⟨shared_secret, pseudorandomness⟩ ←
    (core_models.slice.Impl.split_at u8
      (← (rust_primitives.unsize hashed))
      (32 : usize));
  let r : (RustArray u8 32) ←
    (core_models.result.Impl.unwrap
      (RustArray u8 32)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u8)
        (RustArray u8 32)
        (← pseudorandomness[
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          ]_?))));
  match
    (← (hacspec_ml_kem.ind_cpa.encrypt (RANK) (U_SIZE) (V_SIZE) (CT_SIZE)
      params
      ek
      m
      r))
  with
    | (core_models.result.Result.Ok  c) => do
      let k : (RustArray u8 32) ←
        (rust_primitives.hax.repeat (0 : u8) (32 : usize));
      let k : (RustArray u8 32) ←
        (core_models.slice.Impl.copy_from_slice u8 k shared_secret);
      (pure (core_models.result.Result.Ok (rust_primitives.hax.Tuple2.mk k c)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      encaps_internal.spec
      (RANK : usize)
      (U_SIZE : usize)
      (V_SIZE : usize)
      (CT_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (ek : (RustSlice u8))
      (m : (RustArray u8 32)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                      &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank
                          params)
                        ==? RANK))))
                    &&? (← (U_SIZE
                      ==? (← ((← ((← (RANK
                            *?
                            hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                          *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                        /? (8 : usize)))))))
                  &&? (← (V_SIZE
                    ==? (← ((←
                      (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                        *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))
                      /? (8 : usize)))))))
                &&? (← (CT_SIZE ==? (← (U_SIZE +? V_SIZE))))))
              &&? (← ((← (core_models.slice.Impl.len u8 ek))
                ==? (← ((← (RANK
                    *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                  +? (32 : usize)))))))
            &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (2 : usize)))
              ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (3 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (encaps_internal
        (RANK : usize)
        (U_SIZE : usize)
        (V_SIZE : usize)
        (CT_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (ek : (RustSlice u8))
        (m : (RustArray u8 32))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [encaps_internal] <;> sorry
}

--  Algorithm 20: ML-KEM.Encaps
--
--  Uses the encapsulation key to generate a shared key and ciphertext.
--  Includes modulus check on ek per FIPS 203 Section 7.2.
def encapsulate
    (RANK : usize)
    (EK_SIZE : usize)
    (U_SIZE : usize)
    (V_SIZE : usize)
    (CT_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (ek : (RustArray u8 EK_SIZE))
    (m : (RustArray u8 32)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 (RustArray u8 32) (RustArray u8 CT_SIZE))
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ := rust_primitives.hax.Tuple0.mk;
  (encaps_internal (RANK) (U_SIZE) (V_SIZE) (CT_SIZE)
    params
    (← (rust_primitives.unsize ek))
    m)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      encapsulate.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (U_SIZE : usize)
      (V_SIZE : usize)
      (CT_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (ek : (RustArray u8 EK_SIZE))
      (m : (RustArray u8 32)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                      &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank
                          params)
                        ==? RANK))))
                    &&? (← (EK_SIZE
                      ==? (← ((← (RANK
                          *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                        +? (32 : usize)))))))
                  &&? (← (U_SIZE
                    ==? (← ((← ((← (RANK
                          *?
                          hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                        *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                      /? (8 : usize)))))))
                &&? (← (V_SIZE
                  ==? (← ((←
                    (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                      *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))
                    /? (8 : usize)))))))
              &&? (← (CT_SIZE ==? (← (U_SIZE +? V_SIZE))))))
            &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (2 : usize)))
              ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (3 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (encapsulate
        (RANK : usize)
        (EK_SIZE : usize)
        (U_SIZE : usize)
        (V_SIZE : usize)
        (CT_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (ek : (RustArray u8 EK_SIZE))
        (m : (RustArray u8 32))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [encapsulate] <;> sorry
}

end hacspec_ml_kem.ind_cca


namespace hacspec_ml_kem.ind_cpa

--  Algorithm 15: K-PKE.Decrypt
--
--  Uses the decryption key to decrypt a ciphertext.
--
--  ```plaintext
--  Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
--  Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
--  Output: message m ∈ 𝔹^{32}.
--
--  c₁ ← c[0 : 32dᵤk]
--  c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
--  u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
--  v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
--  ŝ ← ByteDecode₁₂(dkₚₖₑ)
--  w ← v - NTT⁻¹(ŝᵀ ◦ NTT(u))
--  m ← ByteEncode₁(Compress₁(w))
--  return m
--  ```
def decrypt (RANK : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (dk : (RustSlice u8))
    (ciphertext : (RustSlice u8)) :
    RustM (RustArray u8 32) := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let u_encoded_size : usize ←
    (hacspec_ml_kem.parameters.Impl.u_encoded_size params);
  let
    u : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (hacspec_ml_kem.serialize.deserialize_then_decompress_u (RANK)
      (← ciphertext[
        (core_models.ops.range.Range.mk
          (start := (0 : usize))
          (_end := u_encoded_size))
        ]_?)
      (hacspec_ml_kem.parameters.MlKemParams.du params));
  let v : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (hacspec_ml_kem.serialize.deserialize_then_decompress_v
      (← ciphertext[
        (core_models.ops.range.RangeFrom.mk (start := u_encoded_size))
        ]_?)
      (hacspec_ml_kem.parameters.MlKemParams.dv params));
  let
    secret_as_ntt : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (hacspec_ml_kem.serialize.deserialize_ring_elements_reduced (RANK) dk);
  let
    u_as_ntt : (RustArray
    (RustArray hacspec_ml_kem.parameters.FieldElement 256)
    RANK) ←
    (hacspec_ml_kem.ntt.vector_ntt (RANK) u);
  let w : (RustArray hacspec_ml_kem.parameters.FieldElement 256) ←
    (hacspec_ml_kem.matrix.compute_message (RANK) v secret_as_ntt u_as_ntt);
  (hacspec_ml_kem.serialize.compress_then_serialize_message w)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      decrypt.spec (RANK : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (dk : (RustSlice u8))
      (ciphertext : (RustSlice u8)) :
    Spec
      (requires := do
        ((← ((← ((← (RANK <=? (4 : usize)))
              &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
                ==? RANK))))
            &&? (← ((← (core_models.slice.Impl.len u8 dk))
              ==? (← (RANK
                *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
          &&? (← ((← (core_models.slice.Impl.len u8 ciphertext))
            ==? (← ((← ((← ((← (RANK
                    *? hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                  *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                +? (← (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                  *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))))
              /? (8 : usize)))))))
      (ensures := fun _ => pure True)
      (decrypt
        (RANK : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (dk : (RustSlice u8))
        (ciphertext : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [decrypt] <;> sorry
}

end hacspec_ml_kem.ind_cpa


namespace hacspec_ml_kem.ind_cca

--  Algorithm 18: ML-KEM.Decaps_internal
--
--  ```plaintext
--  Input: decapsulation key dk ∈ 𝔹^{768k+96}.
--  Input: ciphertext c ∈ 𝔹^{32(dᵤk+dᵥ)}.
--  Output: shared key K ∈ 𝔹³².
--
--  dkₚₖₑ ← dk[0 : 384k]
--  ekₚₖₑ ← dk[384k : 768k + 32]
--  h ← dk[768k + 32 : 768k + 64]
--  z ← dk[768k + 64 : 768k + 96]
--  m′ ← K-PKE.Decrypt(dkₚₖₑ, c)
--  (K′, r′) ← G(m′ ‖ h)
--  K\u{303} ← J(z ‖ c)
--  c′ ← K-PKE.Encrypt(ekₚₖₑ, m′, r′)
--  if c ≠ c′ then
--      K′ ← K\u{303}
--  end if
--  return K′
--  ```
def decaps_internal
    (RANK : usize)
    (EK_SIZE : usize)
    (DK_SIZE : usize)
    (DK_PKE_SIZE : usize)
    (U_SIZE : usize)
    (V_SIZE : usize)
    (CT_SIZE : usize)
    (J_INPUT_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (dk : (RustArray u8 DK_SIZE))
    (c : (RustArray u8 CT_SIZE)) :
    RustM
    (core_models.result.Result
      (RustArray u8 32)
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let dk_pke : (RustSlice u8) ←
    dk[(core_models.ops.range.RangeTo.mk (_end := DK_PKE_SIZE))]_?;
  let ek : (RustSlice u8) ←
    dk[
      (core_models.ops.range.Range.mk
        (start := DK_PKE_SIZE)
        (_end := (← (DK_PKE_SIZE +? EK_SIZE))))
      ]_?;
  let h : (RustSlice u8) ←
    dk[
      (core_models.ops.range.Range.mk
        (start := (← (DK_PKE_SIZE +? EK_SIZE)))
        (_end := (← ((← (DK_PKE_SIZE +? EK_SIZE))
          +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
      ]_?;
  let z : (RustSlice u8) ←
    dk[
      (core_models.ops.range.RangeFrom.mk
        (start := (← ((← (DK_PKE_SIZE +? EK_SIZE))
          +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
      ]_?;
  let m_prime : (RustArray u8 32) ←
    (hacspec_ml_kem.ind_cpa.decrypt (RANK)
      params
      dk_pke
      (← (rust_primitives.unsize c)));
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.repeat (0 : u8) (64 : usize));
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      to_hash
      (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← to_hash[(core_models.ops.range.RangeTo.mk (_end := (32 : usize)))]_?)
        (← (rust_primitives.unsize m_prime)))));
  let to_hash : (RustArray u8 64) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      to_hash
      (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← to_hash[
          (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
          ]_?)
        h)));
  let hashed : (RustArray u8 64) ←
    (hacspec_ml_kem.parameters.hash_functions.G
      (← (rust_primitives.unsize to_hash)));
  let ⟨success_shared_secret, pseudorandomness⟩ ←
    (core_models.slice.Impl.split_at u8
      (← (rust_primitives.unsize hashed))
      (32 : usize));
  let r_prime : (RustArray u8 32) ←
    (core_models.result.Impl.unwrap
      (RustArray u8 32)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u8)
        (RustArray u8 32)
        (← pseudorandomness[
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          ]_?))));
  let j_input : (RustArray u8 J_INPUT_SIZE) ←
    (rust_primitives.hax.repeat (0 : u8) J_INPUT_SIZE);
  let j_input : (RustArray u8 J_INPUT_SIZE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      j_input
      (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← j_input[(core_models.ops.range.RangeTo.mk (_end := (32 : usize)))]_?)
        z)));
  let j_input : (RustArray u8 J_INPUT_SIZE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      j_input
      (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← j_input[
          (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
          ]_?)
        (← (rust_primitives.unsize c)))));
  let rejection_shared_secret : (RustArray u8 32) ←
    (hacspec_ml_kem.parameters.hash_functions.J ((32 : usize))
      (← (rust_primitives.unsize j_input)));
  match
    (← (hacspec_ml_kem.ind_cpa.encrypt (RANK) (U_SIZE) (V_SIZE) (CT_SIZE)
      params
      ek
      m_prime
      r_prime))
  with
    | (core_models.result.Result.Ok  c_prime) => do
      if
      (← (core_models.cmp.PartialEq.eq
        (RustSlice u8)
        (RustSlice u8)
        (← c[core_models.ops.range.RangeFull.mk]_?)
        (← c_prime[core_models.ops.range.RangeFull.mk]_?))) then do
        let k : (RustArray u8 32) ←
          (rust_primitives.hax.repeat (0 : u8) (32 : usize));
        let k : (RustArray u8 32) ←
          (core_models.slice.Impl.copy_from_slice u8 k success_shared_secret);
        (pure (core_models.result.Result.Ok k))
      else do
        (pure (core_models.result.Result.Ok rejection_shared_secret))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      decaps_internal.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (DK_SIZE : usize)
      (DK_PKE_SIZE : usize)
      (U_SIZE : usize)
      (V_SIZE : usize)
      (CT_SIZE : usize)
      (J_INPUT_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (dk : (RustArray u8 DK_SIZE))
      (c : (RustArray u8 CT_SIZE)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                            &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank
                                params)
                              ==? RANK))))
                          &&? (← (EK_SIZE
                            ==? (← ((← (RANK
                                *?
                                hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                              +? (32 : usize)))))))
                        &&? (← (DK_PKE_SIZE
                          ==? (← (RANK
                            *?
                            hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
                      &&? (← (DK_SIZE
                        ==? (← ((← ((← (DK_PKE_SIZE +? EK_SIZE))
                            +?
                            hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))
                          +? (32 : usize)))))))
                    &&? (← (U_SIZE
                      ==? (← ((← ((← (RANK
                            *?
                            hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                          *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                        /? (8 : usize)))))))
                  &&? (← (V_SIZE
                    ==? (← ((←
                      (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                        *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))
                      /? (8 : usize)))))))
                &&? (← (CT_SIZE ==? (← (U_SIZE +? V_SIZE))))))
              &&? (← (J_INPUT_SIZE ==? (← ((32 : usize) +? CT_SIZE))))))
            &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (2 : usize)))
              ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (3 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (decaps_internal
        (RANK : usize)
        (EK_SIZE : usize)
        (DK_SIZE : usize)
        (DK_PKE_SIZE : usize)
        (U_SIZE : usize)
        (V_SIZE : usize)
        (CT_SIZE : usize)
        (J_INPUT_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (dk : (RustArray u8 DK_SIZE))
        (c : (RustArray u8 CT_SIZE))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [decaps_internal] <;> sorry
}

--  Algorithm 21: ML-KEM.Decaps
--
--  Uses the decapsulation key to produce a shared key from a ciphertext.
def decapsulate
    (RANK : usize)
    (EK_SIZE : usize)
    (DK_SIZE : usize)
    (DK_PKE_SIZE : usize)
    (U_SIZE : usize)
    (V_SIZE : usize)
    (CT_SIZE : usize)
    (J_INPUT_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (dk : (RustArray u8 DK_SIZE))
    (c : (RustArray u8 CT_SIZE)) :
    RustM
    (core_models.result.Result
      (RustArray u8 32)
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  (decaps_internal
    (RANK)
    (EK_SIZE)
    (DK_SIZE)
    (DK_PKE_SIZE)
    (U_SIZE)
    (V_SIZE)
    (CT_SIZE)
    (J_INPUT_SIZE) params dk c)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      decapsulate.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (DK_SIZE : usize)
      (DK_PKE_SIZE : usize)
      (U_SIZE : usize)
      (V_SIZE : usize)
      (CT_SIZE : usize)
      (J_INPUT_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (dk : (RustArray u8 DK_SIZE))
      (c : (RustArray u8 CT_SIZE)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                            &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank
                                params)
                              ==? RANK))))
                          &&? (← (EK_SIZE
                            ==? (← ((← (RANK
                                *?
                                hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                              +? (32 : usize)))))))
                        &&? (← (DK_PKE_SIZE
                          ==? (← (RANK
                            *?
                            hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
                      &&? (← (DK_SIZE
                        ==? (← ((← ((← (DK_PKE_SIZE +? EK_SIZE))
                            +?
                            hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))
                          +? (32 : usize)))))))
                    &&? (← (U_SIZE
                      ==? (← ((← ((← (RANK
                            *?
                            hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT))
                          *? (hacspec_ml_kem.parameters.MlKemParams.du params)))
                        /? (8 : usize)))))))
                  &&? (← (V_SIZE
                    ==? (← ((←
                      (hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
                        *? (hacspec_ml_kem.parameters.MlKemParams.dv params)))
                      /? (8 : usize)))))))
                &&? (← (CT_SIZE ==? (← (U_SIZE +? V_SIZE))))))
              &&? (← (J_INPUT_SIZE ==? (← ((32 : usize) +? CT_SIZE))))))
            &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (2 : usize)))
              ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
                ==? (3 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta2 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (decapsulate
        (RANK : usize)
        (EK_SIZE : usize)
        (DK_SIZE : usize)
        (DK_PKE_SIZE : usize)
        (U_SIZE : usize)
        (V_SIZE : usize)
        (CT_SIZE : usize)
        (J_INPUT_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (dk : (RustArray u8 DK_SIZE))
        (c : (RustArray u8 CT_SIZE))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [decapsulate] <;> sorry
}

end hacspec_ml_kem.ind_cca


namespace hacspec_ml_kem.serialize

--  Serialize a vector of polynomials with 12-bit coefficients.
--  Corresponds to `serialize_secret_key` / `serialize_vector` in the implementation.
def serialize_secret_key (RANK : usize) (T_SIZE : usize)
    (vector :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    RustM (RustArray u8 T_SIZE) := do
  (vector_encode_12 (RANK) (T_SIZE) vector)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      serialize_secret_key.spec (RANK : usize) (T_SIZE : usize)
      (vector :
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK)) :
    Spec
      (requires := do
        ((← (RANK <=? (4 : usize)))
          &&? (← (T_SIZE
            ==? (← (RANK
              *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
      (ensures := fun _ => pure True)
      (serialize_secret_key
        (RANK : usize)
        (T_SIZE : usize)
        (vector :
        (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [serialize_secret_key] <;> sorry
}

end hacspec_ml_kem.serialize


namespace hacspec_ml_kem.ind_cpa

--  Algorithm 13: K-PKE.KeyGen
--
--  Generates an encryption key and a corresponding decryption key.
--
--  ```plaintext
--  Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
--  Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
--
--  d ←$ B
--  (ρ,σ) ← G(d)
--  N ← 0
--  for (i ← 0; i < k; i++)
--      for(j ← 0; j < k; j++)
--          Â[i,j] ← SampleNTT(XOF(ρ, j, i))
--      end for
--  end for
--  for(i ← 0; i < k; i++)
--      s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
--      N ← N + 1
--  end for
--  for(i ← 0; i < k; i++)
--      e[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
--      N ← N + 1
--  end for
--  ŝ ← NTT(s)
--  ê ← NTT(e)
--  t\u{302} ← Â◦ŝ + ê
--  ekₚₖₑ ← ByteEncode₁₂(t\u{302}) ‖ ρ
--  dkₚₖₑ ← ByteEncode₁₂(ŝ)
--  ```
def generate_keypair (RANK : usize) (EK_SIZE : usize) (DK_PKE_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (key_generation_seed : (RustArray u8 32)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        (RustArray u8 EK_SIZE)
        (RustArray u8 DK_PKE_SIZE))
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let g_input : (RustArray u8 33) ←
    (rust_primitives.hax.repeat (0 : u8) (33 : usize));
  let g_input : (RustArray u8 33) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      g_input
      (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← g_input[(core_models.ops.range.RangeTo.mk (_end := (32 : usize)))]_?)
        (← (rust_primitives.unsize key_generation_seed)))));
  let g_input : (RustArray u8 33) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      g_input
      (32 : usize)
      (← (rust_primitives.hax.cast_op RANK : RustM u8)));
  let hashed : (RustArray u8 64) ←
    (hacspec_ml_kem.parameters.hash_functions.G
      (← (rust_primitives.unsize g_input)));
  let ⟨seed_for_A, seed_for_secret_and_error⟩ ←
    (core_models.slice.Impl.split_at u8
      (← (rust_primitives.unsize hashed))
      (32 : usize));
  match (← (hacspec_ml_kem.matrix.sample_matrix_A (RANK) seed_for_A false)) with
    | (core_models.result.Result.Ok  A_as_ntt) => do
      let
        secret : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.parameters.createi
          (RustArray hacspec_ml_kem.parameters.FieldElement 256)
          (RANK)
          (usize ->
          RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
          (fun i =>
            (do
            let prf_input : (RustArray u8 33) ←
              (concat_byte ((32 : usize)) ((33 : usize))
                (← (core_models.result.Impl.unwrap
                  (RustArray u8 32)
                  core_models.array.TryFromSliceError
                  (← (core_models.convert.TryInto.try_into
                    (RustSlice u8)
                    (RustArray u8 32) seed_for_secret_and_error))))
                (← (rust_primitives.hax.cast_op i : RustM u8)));
            (sample_secret
              (hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              prf_input) :
            RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
      let
        error : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.parameters.createi
          (RustArray hacspec_ml_kem.parameters.FieldElement 256)
          (RANK)
          (usize ->
          RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))
          (fun i =>
            (do
            let prf_input : (RustArray u8 33) ←
              (concat_byte ((32 : usize)) ((33 : usize))
                (← (core_models.result.Impl.unwrap
                  (RustArray u8 32)
                  core_models.array.TryFromSliceError
                  (← (core_models.convert.TryInto.try_into
                    (RustSlice u8)
                    (RustArray u8 32) seed_for_secret_and_error))))
                (← (rust_primitives.hax.cast_op (← (RANK +? i)) : RustM u8)));
            (sample_secret
              (hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              prf_input) :
            RustM (RustArray hacspec_ml_kem.parameters.FieldElement 256))));
      let
        secret_as_ntt : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.ntt.vector_ntt (RANK) secret);
      let
        error_as_ntt : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.ntt.vector_ntt (RANK) error);
      let
        t_as_ntt : (RustArray
        (RustArray hacspec_ml_kem.parameters.FieldElement 256)
        RANK) ←
        (hacspec_ml_kem.matrix.compute_As_plus_e (RANK)
          A_as_ntt
          secret_as_ntt
          error_as_ntt);
      let t_encoded : (RustArray u8 DK_PKE_SIZE) ←
        (hacspec_ml_kem.serialize.serialize_secret_key (RANK) (DK_PKE_SIZE)
          t_as_ntt);
      let ek : (RustArray u8 EK_SIZE) ←
        (rust_primitives.hax.repeat (0 : u8) EK_SIZE);
      let ek : (RustArray u8 EK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_to
          ek
          (core_models.ops.range.RangeTo.mk (_end := DK_PKE_SIZE))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← ek[(core_models.ops.range.RangeTo.mk (_end := DK_PKE_SIZE))]_?)
            (← (rust_primitives.unsize t_encoded)))));
      let ek : (RustArray u8 EK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_from
          ek
          (core_models.ops.range.RangeFrom.mk (start := DK_PKE_SIZE))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← ek[
              (core_models.ops.range.RangeFrom.mk (start := DK_PKE_SIZE))
              ]_?)
            seed_for_A)));
      let dk : (RustArray u8 DK_PKE_SIZE) ←
        (hacspec_ml_kem.serialize.serialize_secret_key (RANK) (DK_PKE_SIZE)
          secret_as_ntt);
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk ek dk)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      generate_keypair.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (DK_PKE_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (key_generation_seed : (RustArray u8 32)) :
    Spec
      (requires := do
        ((← ((← ((← ((← (RANK <=? (4 : usize)))
                &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
                  ==? RANK))))
              &&? (← (EK_SIZE
                ==? (← ((← (RANK
                    *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                  +? (32 : usize)))))))
            &&? (← (DK_PKE_SIZE
              ==? (← (RANK
                *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (generate_keypair
        (RANK : usize)
        (EK_SIZE : usize)
        (DK_PKE_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (key_generation_seed : (RustArray u8 32))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [generate_keypair] <;> sorry
}

end hacspec_ml_kem.ind_cpa


namespace hacspec_ml_kem.ind_cca

--  Algorithm 16: ML-KEM.KeyGen_internal
--
--  ```plaintext
--  Input: d ∈ 𝔹³², z ∈ 𝔹³².
--  Output: encapsulation key ek ∈ 𝔹^{384k+32}.
--  Output: decapsulation key dk ∈ 𝔹^{768k+96}.
--
--  (ekₚₖₑ, dkₚₖₑ) ← K-PKE.KeyGen(d)
--  ek ← ekₚₖₑ
--  dk ← (dkₚₖₑ ‖ ek ‖ H(ek) ‖ z)
--  return (ek, dk)
--  ```
def keygen_internal
    (RANK : usize)
    (EK_SIZE : usize)
    (DK_PKE_SIZE : usize)
    (DK_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (d : (RustArray u8 32))
    (z : (RustArray u8 32)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 (RustArray u8 EK_SIZE) (RustArray u8 DK_SIZE))
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  match
    (← (hacspec_ml_kem.ind_cpa.generate_keypair (RANK) (EK_SIZE) (DK_PKE_SIZE)
      params
      d))
  with
    | (core_models.result.Result.Ok  ⟨ek, dk_pke⟩) => do
      let dk : (RustArray u8 DK_SIZE) ←
        (rust_primitives.hax.repeat (0 : u8) DK_SIZE);
      let dk : (RustArray u8 DK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_to
          dk
          (core_models.ops.range.RangeTo.mk (_end := DK_PKE_SIZE))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← dk[(core_models.ops.range.RangeTo.mk (_end := DK_PKE_SIZE))]_?)
            (← (rust_primitives.unsize dk_pke)))));
      let dk : (RustArray u8 DK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          dk
          (core_models.ops.range.Range.mk
            (start := DK_PKE_SIZE)
            (_end := (← (DK_PKE_SIZE +? EK_SIZE))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← dk[
              (core_models.ops.range.Range.mk
                (start := DK_PKE_SIZE)
                (_end := (← (DK_PKE_SIZE +? EK_SIZE))))
              ]_?)
            (← (rust_primitives.unsize ek)))));
      let dk : (RustArray u8 DK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          dk
          (core_models.ops.range.Range.mk
            (start := (← (DK_PKE_SIZE +? EK_SIZE)))
            (_end := (← ((← (DK_PKE_SIZE +? EK_SIZE))
              +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← dk[
              (core_models.ops.range.Range.mk
                (start := (← (DK_PKE_SIZE +? EK_SIZE)))
                (_end := (← ((← (DK_PKE_SIZE +? EK_SIZE))
                  +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
              ]_?)
            (← (rust_primitives.unsize
              (← (hacspec_ml_kem.parameters.hash_functions.H
                (← (rust_primitives.unsize ek)))))))));
      let dk : (RustArray u8 DK_SIZE) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_from
          dk
          (core_models.ops.range.RangeFrom.mk
            (start := (← ((← (DK_PKE_SIZE +? EK_SIZE))
              +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← dk[
              (core_models.ops.range.RangeFrom.mk
                (start := (← ((← (DK_PKE_SIZE +? EK_SIZE))
                  +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))))
              ]_?)
            (← (rust_primitives.unsize z)))));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk ek dk)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      keygen_internal.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (DK_PKE_SIZE : usize)
      (DK_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (d : (RustArray u8 32))
      (z : (RustArray u8 32)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                  &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
                    ==? RANK))))
                &&? (← (EK_SIZE
                  ==? (← ((← (RANK
                      *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                    +? (32 : usize)))))))
              &&? (← (DK_PKE_SIZE
                ==? (← (RANK
                  *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
            &&? (← (DK_SIZE
              ==? (← ((← ((← (DK_PKE_SIZE +? EK_SIZE))
                  +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))
                +? (32 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (keygen_internal
        (RANK : usize)
        (EK_SIZE : usize)
        (DK_PKE_SIZE : usize)
        (DK_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (d : (RustArray u8 32))
        (z : (RustArray u8 32))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [keygen_internal] <;> sorry
}

--  Algorithm 19: ML-KEM.KeyGen
--
--  Generates an encapsulation key and a corresponding decapsulation key.
def generate_keypair
    (RANK : usize)
    (EK_SIZE : usize)
    (DK_SIZE : usize)
    (DK_PKE_SIZE : usize)
    (params : hacspec_ml_kem.parameters.MlKemParams)
    (randomness : (RustArray u8 64)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 (RustArray u8 EK_SIZE) (RustArray u8 DK_SIZE))
      hacspec_ml_kem.sampling.BadRejectionSamplingRandomnessError)
    := do
  let _ := rust_primitives.hax.Tuple0.mk;
  let d : (RustArray u8 32) ←
    (core_models.result.Impl.unwrap
      (RustArray u8 32)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u8)
        (RustArray u8 32)
        (← randomness[
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          ]_?))));
  let z : (RustArray u8 32) ←
    (core_models.result.Impl.unwrap
      (RustArray u8 32)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u8)
        (RustArray u8 32)
        (← randomness[
          (core_models.ops.range.RangeFrom.mk (start := (32 : usize)))
          ]_?))));
  (keygen_internal (RANK) (EK_SIZE) (DK_PKE_SIZE) (DK_SIZE) params d z)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      generate_keypair.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (DK_SIZE : usize)
      (DK_PKE_SIZE : usize)
      (params : hacspec_ml_kem.parameters.MlKemParams)
      (randomness : (RustArray u8 64)) :
    Spec
      (requires := do
        ((← ((← ((← ((← ((← (RANK <=? (4 : usize)))
                  &&? (← ((hacspec_ml_kem.parameters.MlKemParams.rank params)
                    ==? RANK))))
                &&? (← (EK_SIZE
                  ==? (← ((← (RANK
                      *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                    +? (32 : usize)))))))
              &&? (← (DK_PKE_SIZE
                ==? (← (RANK
                  *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
            &&? (← (DK_SIZE
              ==? (← ((← ((← (DK_PKE_SIZE +? EK_SIZE))
                  +? hacspec_ml_kem.parameters.hash_functions.H_DIGEST_SIZE))
                +? (32 : usize)))))))
          &&? (← ((← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (2 : usize)))
            ||? (← ((hacspec_ml_kem.parameters.MlKemParams.eta1 params)
              ==? (3 : usize)))))))
      (ensures := fun _ => pure True)
      (generate_keypair
        (RANK : usize)
        (EK_SIZE : usize)
        (DK_SIZE : usize)
        (DK_PKE_SIZE : usize)
        (params : hacspec_ml_kem.parameters.MlKemParams)
        (randomness : (RustArray u8 64))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [generate_keypair] <;> sorry
}

end hacspec_ml_kem.ind_cca


namespace hacspec_ml_kem.serialize

--  Serialize a public key: encode the NTT vector t\u{302} concatenated with the seed ρ.
--  Corresponds to `serialize_public_key` in the implementation\'s `ind_cpa.rs`.
def serialize_public_key (RANK : usize) (EK_SIZE : usize) (T_SIZE : usize)
    (t_as_ntt :
    (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
    (seed_for_A : (RustSlice u8)) :
    RustM (RustArray u8 EK_SIZE) := do
  let t_encoded : (RustArray u8 T_SIZE) ←
    (vector_encode_12 (RANK) (T_SIZE) t_as_ntt);
  let ek : (RustArray u8 EK_SIZE) ←
    (rust_primitives.hax.repeat (0 : u8) EK_SIZE);
  let ek : (RustArray u8 EK_SIZE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_to
      ek
      (core_models.ops.range.RangeTo.mk (_end := T_SIZE))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← ek[(core_models.ops.range.RangeTo.mk (_end := T_SIZE))]_?)
        (← (rust_primitives.unsize t_encoded)))));
  let ek : (RustArray u8 EK_SIZE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      ek
      (core_models.ops.range.RangeFrom.mk (start := T_SIZE))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← ek[(core_models.ops.range.RangeFrom.mk (start := T_SIZE))]_?)
        (← seed_for_A[
          (core_models.ops.range.RangeTo.mk (_end := (32 : usize)))
          ]_?))));
  (pure ek)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      serialize_public_key.spec
      (RANK : usize)
      (EK_SIZE : usize)
      (T_SIZE : usize)
      (t_as_ntt :
      (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
      (seed_for_A : (RustSlice u8)) :
    Spec
      (requires := do
        ((← ((← ((← (RANK <=? (4 : usize)))
              &&? (← (EK_SIZE
                ==? (← ((← (RANK
                    *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))
                  +? (32 : usize)))))))
            &&? (← (T_SIZE
              ==? (← (RANK
                *? hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT))))))
          &&? (← ((← (core_models.slice.Impl.len u8 seed_for_A))
            >=? (32 : usize)))))
      (ensures := fun _ => pure True)
      (serialize_public_key
        (RANK : usize)
        (EK_SIZE : usize)
        (T_SIZE : usize)
        (t_as_ntt :
        (RustArray (RustArray hacspec_ml_kem.parameters.FieldElement 256) RANK))
        (seed_for_A : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [serialize_public_key] <;> sorry
}

end hacspec_ml_kem.serialize
