module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let compute_one_hint (low high gamma2: i32) =
  if
    low >. gamma2 || low <. (Core.Ops.Arith.Neg.neg gamma2 <: i32) ||
    low =. (Core.Ops.Arith.Neg.neg gamma2 <: i32) && high <>. 0l
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

let decompose_element (gamma2 r: i32) =
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
  let ceil_of_r_by_128_:i32 = (r +! 127l <: i32) >>! 7l in
  let r1:i32 =
    match gamma2 <: i32 with
    | 95232l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 11275l <: i32) +! (1l <<! 23l <: i32) <: i32) >>! 24l
      in
      (result ^. ((43l -! result <: i32) >>! 31l <: i32) <: i32) &. result
    | 261888l ->
      let result:i32 =
        ((ceil_of_r_by_128_ *! 1025l <: i32) +! (1l <<! 21l <: i32) <: i32) >>! 22l
      in
      result &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let alpha:i32 = gamma2 *! 2l in
  let r0:i32 = r -! (r1 *! alpha <: i32) in
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

let use_one_hint (gamma2 r hint: i32) =
  let r0, r1:(i32 & i32) = decompose_element gamma2 r in
  if hint =. 0l
  then r1
  else
    match gamma2 <: i32 with
    | 95232l ->
      if r0 >. 0l
      then if r1 =. 43l then 0l else r1 +! hint
      else if r1 =. 0l then 43l else r1 -! hint
    | 261888l -> if r0 >. 0l then (r1 +! hint <: i32) &. 15l else (r1 -! hint <: i32) &. 15l
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)

let add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) +!
                (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  lhs

let compute_hint
      (low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma2: i32)
      (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let one_hints_count:usize = sz 0 in
  let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize
          ) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (hint, one_hints_count <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize))
      (fun temp_0_ i ->
          let hint, one_hints_count:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize
          ) =
            temp_0_
          in
          let i:usize = i in
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              hint with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                (compute_one_hint (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                      <:
                      i32)
                    (high.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                    gamma2
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let one_hints_count:usize =
            one_hints_count +!
            (cast (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) <: usize)
          in
          hint, one_hints_count <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)
      )
  in
  let hax_temp_output:usize = one_hints_count in
  hint, hax_temp_output <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)

let decompose
      (gamma2: i32)
      (simd_unit low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (low.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (high, low
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
      (fun temp_0_ i ->
          let high, low:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          let lhs, lhs_1_:(i32 & i32) =
            decompose_element gamma2
              (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
          in
          let low:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              low with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize low
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let high:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              high with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize high
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs_1_
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          high, low
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
  in
  low, high
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)

let infinity_norm_exceeds
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (bound: i32)
     =
  let result:bool = false in
  let result:bool =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun result temp_1_ ->
          let result:bool = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:bool = result in
          let i:usize = i in
          let coefficient:i32 = simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] in
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
          let result:bool = result || normalized >=. bound in
          result)
  in
  result

let montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (montgomery_reduce_element ((cast (lhs
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
                          <:
                          i32)
                      <:
                      i64) *!
                    (cast (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
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
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  lhs

let montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (c: i32)
     =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          {
            simd_unit with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (montgomery_reduce_element ((cast (simd_unit
                            .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
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
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  simd_unit

let power2round (t0 t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (t0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun temp_0_ temp_1_ ->
          let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (t0, t1
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
      (fun temp_0_ i ->
          let t0, t1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
            temp_0_
          in
          let i:usize = i in
          let lhs, lhs_1_:(i32 & i32) =
            power2round_element (t0.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
          in
          let t0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              t0 with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t0
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          let t1:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            {
              t1 with
              Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize t1
                  .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
                i
                lhs_1_
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
          in
          t0, t1
          <:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
  in
  t0, t1
  <:
  (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
    Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)

let shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
     =
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit i ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = simd_unit in
          let i:usize = i in
          {
            simd_unit with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (reduce_element ((simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ]
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
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  simd_unit

let subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              ((lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32) -!
                (rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  lhs

let use_hint (gamma2: i32) (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
  let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      (Core.Slice.impl__len #i32
          (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values <: t_Slice i32)
        <:
        usize)
      (fun hint temp_1_ ->
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = hint in
          let _:usize = temp_1_ in
          true)
      hint
      (fun hint i ->
          let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = hint in
          let i:usize = i in
          {
            hint with
            Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                .Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
              i
              (use_one_hint gamma2
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                  (hint.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values.[ i ] <: i32)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
  in
  hint
