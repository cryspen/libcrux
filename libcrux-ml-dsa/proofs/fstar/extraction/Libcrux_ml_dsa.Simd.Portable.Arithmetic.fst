module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let compute_one_hint (v_GAMMA2 low high: i32) =
  if
    low >. v_GAMMA2 || low <. (Core.Ops.Arith.Neg.neg v_GAMMA2 <: i32) ||
    low =. (Core.Ops.Arith.Neg.neg v_GAMMA2 <: i32) && high <>. 0l
  then 1l
  else 0l

let get_n_least_significant_bits (n: u8) (value: u64) = value &. ((1uL <<! n <: u64) -! 1uL <: u64)

let reduce_element (fe: i32) =
  let quotient:i32 = (fe +! (1l <<! 22l <: i32) <: i32) >>! 23l in
  fe -! (quotient *! Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)

let montgomery_reduce_element (value: i64) =
  let t:u64 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i64) <: u64) <: u64) *!
    Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
  in
  let k:i32 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u64) <: i32 in
  let k_times_modulus:i64 =
    (cast (k <: i32) <: i64) *! (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64)
  in
  let c:i32 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  let value_high:i32 = cast (value >>! v_MONTGOMERY_SHIFT <: i64) <: i32 in
  value_high -! c

let montgomery_multiply_fe_by_fer (fe fer: i32) =
  montgomery_reduce_element ((cast (fe <: i32) <: i64) *! (cast (fer <: i32) <: i64) <: i64)

let decompose_element (v_GAMMA2 r: i32) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((r >.
              (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
              <:
              bool) &&
            (r <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
      in
      ()
  in
  let r:i32 = r +! ((r >>! 31l <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) in
  let v_ALPHA:i32 = v_GAMMA2 *! 2l in
  let ceil_of_r_by_128_:i32 = (r +! 127l <: i32) >>! 7l in
  let r1:i32 =
    match v_ALPHA with
    | 190464l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 11275l <: i32) +! (1l <<! 23l <: i32) <: i32) >>! 24l
      in
      (result ^. ((43l -! result <: i32) >>! 31l <: i32) <: i32) &. result
    | 523776l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 1025l <: i32) +! (1l <<! 21l <: i32) <: i32) >>! 22l
      in
      result &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let r0:i32 = r -! (r1 *! v_ALPHA <: i32) in
  let r0:i32 =
    r0 -!
    (((((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -! 1l <: i32) /! 2l <: i32) -! r0 <: i32) >>!
        31l
        <:
        i32) &.
      Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
      <:
      i32)
  in
  r0, r1 <: (i32 & i32)

let infinity_norm_exceeds
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (bound: i32)
     =
  let exceeds:bool = false in
  let exceeds:bool =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Array.Iter.t_IntoIter
              i32 (sz 8))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Collect.f_into_iter #(t_Array i32 (sz 8))
              #FStar.Tactics.Typeclasses.solve
              simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 8))
        <:
        Core.Array.Iter.t_IntoIter i32 (sz 8))
      exceeds
      (fun exceeds coefficient ->
          let exceeds:bool = exceeds in
          let coefficient:i32 = coefficient in
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                Hax_lib.v_assert ((coefficient >.
                      (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
                      <:
                      bool) &&
                    (coefficient <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
              in
              ()
          in
          let sign:i32 = coefficient >>! 31l in
          let normalized:i32 = coefficient -! (sign &. (2l *! coefficient <: i32) <: i32) in
          let exceeds:bool = exceeds || normalized >=. bound in
          exceeds)
  in
  exceeds

let power2round_element (t: i32) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((t >.
              (Core.Ops.Arith.Neg.neg Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32)
              <:
              bool) &&
            (t <. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: bool))
      in
      ()
  in
  let t:i32 = t +! ((t >>! 31l <: i32) &. Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) in
  let t1:i32 =
    ((t -! 1l <: i32) +!
      (1l <<! (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! sz 1 <: usize) <: i32)
      <:
      i32) >>!
    Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T
  in
  let t0:i32 = t -! (t1 <<! Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T <: i32) in
  t0, t1 <: (i32 & i32)

let use_one_hint (v_GAMMA2 r hint: i32) =
  let r0, r1:(i32 & i32) = decompose_element v_GAMMA2 r in
  if hint =. 0l
  then r1
  else
    match v_GAMMA2 with
    | 95232l ->
      if r0 >. 0l
      then if r1 =. 43l then 0l else r1 +! hint
      else if r1 =. 0l then 43l else r1 -! hint
    | 261888l -> if r0 >. 0l then (r1 +! hint <: i32) &. 15l else (r1 -! hint <: i32) &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)

let power2round (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let t0_simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let t1_simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let t0_simd_unit, t1_simd_unit:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
    Rust_primitives.Hax.Folds.fold_enumerated_slice simd_unit
        .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
      (fun temp_0_ temp_1_ ->
          let t0_simd_unit, t1_simd_unit:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (t0_simd_unit, t1_simd_unit
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit))
      (fun temp_0_ temp_1_ ->
          let t0_simd_unit, t1_simd_unit:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
            temp_0_
          in
          let i, t:(usize & i32) = temp_1_ in
          let t0, t1:(i32 & i32) = power2round_element t in
          let t0_simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              t0_simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t0_simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                i
                t0
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let t1_simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              t1_simd_unit with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1_simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                i
                t1
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          t0_simd_unit, t1_simd_unit
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit))
  in
  t0_simd_unit, t1_simd_unit
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)

let add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let sum:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let sum:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (sum.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun sum temp_1_ ->
          let sum:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = sum in
          let _:usize = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = sum in
          let i:usize = i in
          {
            sum with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sum
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32) +!
                (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  sum

let compute_hint
      (v_GAMMA2: i32)
      (low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
     =
  let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let one_hints_count:usize = sz 0 in
  let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            usize) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (hint, one_hints_count
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit & usize))
      (fun temp_0_ i ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            usize) =
            temp_0_
          in
          let i:usize = i in
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              hint with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                i
                (compute_one_hint v_GAMMA2
                    (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                    (high.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let one_hints_count:usize =
            one_hints_count +!
            (cast (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
              <:
              usize)
          in
          hint, one_hints_count
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit & usize))
  in
  one_hints_count, hint <: (usize & Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)

let decompose
      (v_GAMMA2: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
     =
  let low:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let high:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (high, low
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit))
      (fun temp_0_ i ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
            temp_0_
          in
          let i:usize = i in
          let low_part, high_part:(i32 & i32) =
            decompose_element v_GAMMA2
              (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
          in
          let low:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              low with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                i
                low_part
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          let high:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
            {
              high with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
                i
                high_part
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
          in
          high, low
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit))
  in
  low, high
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)

let montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let product:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let product:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (product.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun product temp_1_ ->
          let product:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = product in
          let _:usize = temp_1_ in
          true)
      product
      (fun product i ->
          let product:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = product in
          let i:usize = i in
          {
            product with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize product
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              (montgomery_reduce_element ((cast (lhs
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i64) *!
                    (cast (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                      <:
                      i64)
                    <:
                    i64)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  product

let montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (c: i32)
     =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = simd_unit in
          let i:usize = i in
          {
            simd_unit with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              (montgomery_reduce_element ((cast (simd_unit
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i64) *!
                    (cast (c <: i32) <: i64)
                    <:
                    i64)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  simd_unit

let shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
     =
  let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun out temp_1_ ->
          let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = out in
          let i:usize = i in
          {
            out with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              (reduce_element ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i
                      ]
                      <:
                      i32) <<!
                    v_SHIFT_BY
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  out

let subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit) =
  let difference:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let difference:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (difference.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun difference temp_1_ ->
          let difference:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = difference in
          let _:usize = temp_1_ in
          true)
      difference
      (fun difference i ->
          let difference:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = difference in
          let i:usize = i in
          {
            difference with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize difference
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32) -!
                (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  difference

let use_hint
      (v_GAMMA2: i32)
      (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
     =
  let result:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Portable.Vector_type.v_ZERO ()
  in
  let result:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (result.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients <: t_Slice i32)
        <:
        usize)
      (fun result temp_1_ ->
          let result:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients
              i
              (use_one_hint v_GAMMA2
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                  (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_coefficients.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
  in
  result
