module Core_models.Abstractions.Bitvec.Int_vec_interp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an interpretation lemma.
let v_SIMPLIFICATION_LEMMA: Prims.unit = () <: Prims.unit

let e_ee_1: Prims.unit = ()

///Conversion from i32 vectors of size 8to  bit vectors of size 256
assume
val e_ee_1__impl__from_i32x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_1__impl__from_i32x8 = e_ee_1__impl__from_i32x8'

///Conversion from bit vectors of size 256 to i32 vectors of size 8
assume
val e_ee_1__impl__to_i32x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32

unfold
let e_ee_1__impl__to_i32x8 = e_ee_1__impl__to_i32x8'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
assume
val e_ee_1__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (e_ee_1__impl__to_i32x8 (e_ee_1__impl__from_i32x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      x)

unfold
let e_ee_1__lemma_cancel_iv = e_ee_1__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x8 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_1__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_1__impl__from_i32x8 (e_ee_1__impl__to_i32x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_1__lemma_cancel_bv = e_ee_1__lemma_cancel_bv'

let e_ee_2: Prims.unit = ()

///Conversion from i64 vectors of size 4to  bit vectors of size 256
assume
val e_ee_2__impl__from_i64x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_2__impl__from_i64x4 = e_ee_2__impl__from_i64x4'

///Conversion from bit vectors of size 256 to i64 vectors of size 4
assume
val e_ee_2__impl__to_i64x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64

unfold
let e_ee_2__impl__to_i64x4 = e_ee_2__impl__to_i64x4'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i64x4 :: from is the identity.
assume
val e_ee_2__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (e_ee_2__impl__to_i64x4 (e_ee_2__impl__from_i64x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      x)

unfold
let e_ee_2__lemma_cancel_iv = e_ee_2__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x4 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_2__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_2__impl__from_i64x4 (e_ee_2__impl__to_i64x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_2__lemma_cancel_bv = e_ee_2__lemma_cancel_bv'

let e_ee_3: Prims.unit = ()

///Conversion from i16 vectors of size 16to  bit vectors of size 256
assume
val e_ee_3__impl__from_i16x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_3__impl__from_i16x16 = e_ee_3__impl__from_i16x16'

///Conversion from bit vectors of size 256 to i16 vectors of size 16
assume
val e_ee_3__impl__to_i16x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16

unfold
let e_ee_3__impl__to_i16x16 = e_ee_3__impl__to_i16x16'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i16x16 :: from is the identity.
assume
val e_ee_3__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16
  -> Lemma
    (ensures
      (e_ee_3__impl__to_i16x16 (e_ee_3__impl__from_i16x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16) ==
      x)

unfold
let e_ee_3__lemma_cancel_iv = e_ee_3__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x16 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_3__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_3__impl__from_i16x16 (e_ee_3__impl__to_i16x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_3__lemma_cancel_bv = e_ee_3__lemma_cancel_bv'

let e_ee_4: Prims.unit = ()

///Conversion from i128 vectors of size 2to  bit vectors of size 256
assume
val e_ee_4__impl__from_i128x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_4__impl__from_i128x2 = e_ee_4__impl__from_i128x2'

///Conversion from bit vectors of size 256 to i128 vectors of size 2
assume
val e_ee_4__impl__to_i128x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128

unfold
let e_ee_4__impl__to_i128x2 = e_ee_4__impl__to_i128x2'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i128x2 :: from is the identity.
assume
val e_ee_4__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128
  -> Lemma
    (ensures
      (e_ee_4__impl__to_i128x2 (e_ee_4__impl__from_i128x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128) ==
      x)

unfold
let e_ee_4__lemma_cancel_iv = e_ee_4__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i128x2 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_4__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_4__impl__from_i128x2 (e_ee_4__impl__to_i128x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_4__lemma_cancel_bv = e_ee_4__lemma_cancel_bv'

let e_ee_5: Prims.unit = ()

///Conversion from i8 vectors of size 32to  bit vectors of size 256
assume
val e_ee_5__impl__from_i8x32': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_5__impl__from_i8x32 = e_ee_5__impl__from_i8x32'

///Conversion from bit vectors of size 256 to i8 vectors of size 32
assume
val e_ee_5__impl__to_i8x32': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8

unfold
let e_ee_5__impl__to_i8x32 = e_ee_5__impl__to_i8x32'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i8x32 :: from is the identity.
assume
val e_ee_5__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8
  -> Lemma
    (ensures
      (e_ee_5__impl__to_i8x32 (e_ee_5__impl__from_i8x32 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8) ==
      x)

unfold
let e_ee_5__lemma_cancel_iv = e_ee_5__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x32 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_5__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_5__impl__from_i8x32 (e_ee_5__impl__to_i8x32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_5__lemma_cancel_bv = e_ee_5__lemma_cancel_bv'

let e_ee_6: Prims.unit = ()

///Conversion from u32 vectors of size 8to  bit vectors of size 256
assume
val e_ee_6__impl__from_u32x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_6__impl__from_u32x8 = e_ee_6__impl__from_u32x8'

///Conversion from bit vectors of size 256 to u32 vectors of size 8
assume
val e_ee_6__impl__to_u32x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32

unfold
let e_ee_6__impl__to_u32x8 = e_ee_6__impl__to_u32x8'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u32x8 :: from is the identity.
assume
val e_ee_6__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32
  -> Lemma
    (ensures
      (e_ee_6__impl__to_u32x8 (e_ee_6__impl__from_u32x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32) ==
      x)

unfold
let e_ee_6__lemma_cancel_iv = e_ee_6__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x8 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_6__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_6__impl__from_u32x8 (e_ee_6__impl__to_u32x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_6__lemma_cancel_bv = e_ee_6__lemma_cancel_bv'

let e_ee_7: Prims.unit = ()

///Conversion from u64 vectors of size 4to  bit vectors of size 256
assume
val e_ee_7__impl__from_u64x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_7__impl__from_u64x4 = e_ee_7__impl__from_u64x4'

///Conversion from bit vectors of size 256 to u64 vectors of size 4
assume
val e_ee_7__impl__to_u64x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64

unfold
let e_ee_7__impl__to_u64x4 = e_ee_7__impl__to_u64x4'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u64x4 :: from is the identity.
assume
val e_ee_7__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64
  -> Lemma
    (ensures
      (e_ee_7__impl__to_u64x4 (e_ee_7__impl__from_u64x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64) ==
      x)

unfold
let e_ee_7__lemma_cancel_iv = e_ee_7__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u64x4 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_7__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_7__impl__from_u64x4 (e_ee_7__impl__to_u64x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_7__lemma_cancel_bv = e_ee_7__lemma_cancel_bv'

let e_ee_8: Prims.unit = ()

///Conversion from u16 vectors of size 16to  bit vectors of size 256
assume
val e_ee_8__impl__from_u16x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_8__impl__from_u16x16 = e_ee_8__impl__from_u16x16'

///Conversion from bit vectors of size 256 to u16 vectors of size 16
assume
val e_ee_8__impl__to_u16x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16

unfold
let e_ee_8__impl__to_u16x16 = e_ee_8__impl__to_u16x16'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u16x16 :: from is the identity.
assume
val e_ee_8__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16
  -> Lemma
    (ensures
      (e_ee_8__impl__to_u16x16 (e_ee_8__impl__from_u16x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16) ==
      x)

unfold
let e_ee_8__lemma_cancel_iv = e_ee_8__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x16 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_8__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_8__impl__from_u16x16 (e_ee_8__impl__to_u16x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_8__lemma_cancel_bv = e_ee_8__lemma_cancel_bv'

let e_ee_9: Prims.unit = ()

///Conversion from i32 vectors of size 4to  bit vectors of size 128
assume
val e_ee_9__impl__from_i32x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_9__impl__from_i32x4 = e_ee_9__impl__from_i32x4'

///Conversion from bit vectors of size 128 to i32 vectors of size 4
assume
val e_ee_9__impl__to_i32x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32

unfold
let e_ee_9__impl__to_i32x4 = e_ee_9__impl__to_i32x4'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i32x4 :: from is the identity.
assume
val e_ee_9__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32
  -> Lemma
    (ensures
      (e_ee_9__impl__to_i32x4 (e_ee_9__impl__from_i32x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32) ==
      x)

unfold
let e_ee_9__lemma_cancel_iv = e_ee_9__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x4 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_9__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_9__impl__from_i32x4 (e_ee_9__impl__to_i32x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_9__lemma_cancel_bv = e_ee_9__lemma_cancel_bv'

let e_ee_10: Prims.unit = ()

///Conversion from i64 vectors of size 2to  bit vectors of size 128
assume
val e_ee_10__impl__from_i64x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_10__impl__from_i64x2 = e_ee_10__impl__from_i64x2'

///Conversion from bit vectors of size 128 to i64 vectors of size 2
assume
val e_ee_10__impl__to_i64x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64

unfold
let e_ee_10__impl__to_i64x2 = e_ee_10__impl__to_i64x2'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i64x2 :: from is the identity.
assume
val e_ee_10__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64
  -> Lemma
    (ensures
      (e_ee_10__impl__to_i64x2 (e_ee_10__impl__from_i64x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64) ==
      x)

unfold
let e_ee_10__lemma_cancel_iv = e_ee_10__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x2 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_10__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_10__impl__from_i64x2 (e_ee_10__impl__to_i64x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_10__lemma_cancel_bv = e_ee_10__lemma_cancel_bv'

let e_ee_11: Prims.unit = ()

///Conversion from i16 vectors of size 8to  bit vectors of size 128
assume
val e_ee_11__impl__from_i16x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_11__impl__from_i16x8 = e_ee_11__impl__from_i16x8'

///Conversion from bit vectors of size 128 to i16 vectors of size 8
assume
val e_ee_11__impl__to_i16x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16

unfold
let e_ee_11__impl__to_i16x8 = e_ee_11__impl__to_i16x8'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i16x8 :: from is the identity.
assume
val e_ee_11__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16
  -> Lemma
    (ensures
      (e_ee_11__impl__to_i16x8 (e_ee_11__impl__from_i16x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16) ==
      x)

unfold
let e_ee_11__lemma_cancel_iv = e_ee_11__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x8 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_11__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_11__impl__from_i16x8 (e_ee_11__impl__to_i16x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_11__lemma_cancel_bv = e_ee_11__lemma_cancel_bv'

let e_ee_12: Prims.unit = ()

///Conversion from i128 vectors of size 1to  bit vectors of size 128
assume
val e_ee_12__impl__from_i128x1': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_12__impl__from_i128x1 = e_ee_12__impl__from_i128x1'

///Conversion from bit vectors of size 128 to i128 vectors of size 1
assume
val e_ee_12__impl__to_i128x1': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128

unfold
let e_ee_12__impl__to_i128x1 = e_ee_12__impl__to_i128x1'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i128x1 :: from is the identity.
assume
val e_ee_12__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128
  -> Lemma
    (ensures
      (e_ee_12__impl__to_i128x1 (e_ee_12__impl__from_i128x1 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128) ==
      x)

unfold
let e_ee_12__lemma_cancel_iv = e_ee_12__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i128x1 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_12__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_12__impl__from_i128x1 (e_ee_12__impl__to_i128x1 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_12__lemma_cancel_bv = e_ee_12__lemma_cancel_bv'

let e_ee_13: Prims.unit = ()

///Conversion from i8 vectors of size 16to  bit vectors of size 128
assume
val e_ee_13__impl__from_i8x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_13__impl__from_i8x16 = e_ee_13__impl__from_i8x16'

///Conversion from bit vectors of size 128 to i8 vectors of size 16
assume
val e_ee_13__impl__to_i8x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8

unfold
let e_ee_13__impl__to_i8x16 = e_ee_13__impl__to_i8x16'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i8x16 :: from is the identity.
assume
val e_ee_13__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8
  -> Lemma
    (ensures
      (e_ee_13__impl__to_i8x16 (e_ee_13__impl__from_i8x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) ==
      x)

unfold
let e_ee_13__lemma_cancel_iv = e_ee_13__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x16 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_13__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_13__impl__from_i8x16 (e_ee_13__impl__to_i8x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_13__lemma_cancel_bv = e_ee_13__lemma_cancel_bv'

let e_ee_14: Prims.unit = ()

///Conversion from u32 vectors of size 4to  bit vectors of size 128
assume
val e_ee_14__impl__from_u32x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_14__impl__from_u32x4 = e_ee_14__impl__from_u32x4'

///Conversion from bit vectors of size 128 to u32 vectors of size 4
assume
val e_ee_14__impl__to_u32x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32

unfold
let e_ee_14__impl__to_u32x4 = e_ee_14__impl__to_u32x4'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u32x4 :: from is the identity.
assume
val e_ee_14__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32
  -> Lemma
    (ensures
      (e_ee_14__impl__to_u32x4 (e_ee_14__impl__from_u32x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32) ==
      x)

unfold
let e_ee_14__lemma_cancel_iv = e_ee_14__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x4 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_14__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_14__impl__from_u32x4 (e_ee_14__impl__to_u32x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_14__lemma_cancel_bv = e_ee_14__lemma_cancel_bv'

let e_ee_15: Prims.unit = ()

///Conversion from u64 vectors of size 2to  bit vectors of size 128
assume
val e_ee_15__impl__from_u64x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_15__impl__from_u64x2 = e_ee_15__impl__from_u64x2'

///Conversion from bit vectors of size 128 to u64 vectors of size 2
assume
val e_ee_15__impl__to_u64x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64

unfold
let e_ee_15__impl__to_u64x2 = e_ee_15__impl__to_u64x2'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u64x2 :: from is the identity.
assume
val e_ee_15__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64
  -> Lemma
    (ensures
      (e_ee_15__impl__to_u64x2 (e_ee_15__impl__from_u64x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64) ==
      x)

unfold
let e_ee_15__lemma_cancel_iv = e_ee_15__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u64x2 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_15__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_15__impl__from_u64x2 (e_ee_15__impl__to_u64x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_15__lemma_cancel_bv = e_ee_15__lemma_cancel_bv'

let e_ee_16: Prims.unit = ()

///Conversion from u16 vectors of size 8to  bit vectors of size 128
assume
val e_ee_16__impl__from_u16x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_16__impl__from_u16x8 = e_ee_16__impl__from_u16x8'

///Conversion from bit vectors of size 128 to u16 vectors of size 8
assume
val e_ee_16__impl__to_u16x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16

unfold
let e_ee_16__impl__to_u16x8 = e_ee_16__impl__to_u16x8'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u16x8 :: from is the identity.
assume
val e_ee_16__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16
  -> Lemma
    (ensures
      (e_ee_16__impl__to_u16x8 (e_ee_16__impl__from_u16x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16) ==
      x)

unfold
let e_ee_16__lemma_cancel_iv = e_ee_16__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x8 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_16__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_16__impl__from_u16x8 (e_ee_16__impl__to_u16x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_16__lemma_cancel_bv = e_ee_16__lemma_cancel_bv'

let impl__into_i32x8 (self: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let value:i64 =
          Core_models.Abstractions.Funarr.impl_5__get (mk_u64 4) #i64 self (i /! mk_u64 2 <: u64)
        in
        cast ((if (i %! mk_u64 2 <: u64) =. mk_u64 0 then value else value >>! mk_i32 32) <: i64)
        <:
        i32)

let impl_1__into_i64x4 (self: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        let low:u64 =
          cast (cast (Core_models.Abstractions.Funarr.impl_5__get (mk_u64 8)
                    #i32
                    self
                    (mk_u64 2 *! i <: u64)
                  <:
                  i32)
              <:
              u32)
          <:
          u64
        in
        let high:i64 =
          cast (Core_models.Abstractions.Funarr.impl_5__get (mk_u64 8)
                #i32
                self
                ((mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64)
              <:
              i32)
          <:
          i64
        in
        (high <<! mk_i32 32 <: i64) |. (cast (low <: u64) <: i64))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) =
  {
    f_from_pre = (fun (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> true);
    f_from_post
    =
    (fun
        (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (out: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        ->
        true);
    f_from
    =
    fun (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> impl__into_i32x8 vec
  }

[@@ v_SIMPLIFICATION_LEMMA ]

/// Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
/// yields the same result as directly converting the `i64x4` into an `i32x8`.
assume
val lemma_rewrite_i64x4_bv_i32x8': bv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (e_ee_1__impl__to_i32x8 (e_ee_2__impl__from_i64x4 bv
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      (impl__into_i32x8 bv <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32))

unfold
let lemma_rewrite_i64x4_bv_i32x8 = lemma_rewrite_i64x4_bv_i32x8'

[@@ v_SIMPLIFICATION_LEMMA ]

/// Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
/// yields the same result as directly converting the `i64x4` into an `i32x8`.
assume
val lemma_rewrite_i32x8_bv_i64x4': bv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (e_ee_2__impl__to_i64x4 (e_ee_1__impl__from_i32x8 bv
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      (impl_1__into_i64x4 bv <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64))

unfold
let lemma_rewrite_i32x8_bv_i64x4 = lemma_rewrite_i32x8_bv_i64x4'

[@@ v_SIMPLIFICATION_LEMMA ]
        let lemma (t: Type) (i: Core.Convert.t_From t t) (x: t)
            : Lemma (Core.Convert.f_from #t #t #i x == (norm [primops; iota; delta; zeta] i.f_from) x)
            = ()
