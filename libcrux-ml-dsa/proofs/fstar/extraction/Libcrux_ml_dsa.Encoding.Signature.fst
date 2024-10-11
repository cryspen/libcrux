module Libcrux_ml_dsa.Encoding.Signature
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let impl__deserialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Array u8 v_SIGNATURE_SIZE)
     =
  let commitment_hash, rest_of_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 (serialized <: t_Slice u8) v_COMMITMENT_HASH_SIZE
  in
  let signer_response_serialized, hint_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      rest_of_serialized
      (v_GAMMA1_RING_ELEMENT_SIZE *! v_COLUMNS_IN_A <: usize)
  in
  let signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_COLUMNS_IN_A
  in
  let signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      v_COLUMNS_IN_A
      (fun signer_response temp_1_ ->
          let signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            signer_response
          in
          let _:usize = temp_1_ in
          true)
      signer_response
      (fun signer_response i ->
          let signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            signer_response
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signer_response
            i
            (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
                v_GAMMA1_EXPONENT
                (signer_response_serialized.[ {
                      Core.Ops.Range.f_start = i *! v_GAMMA1_RING_ELEMENT_SIZE <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! Rust_primitives.mk_usize 1 <: usize) *! v_GAMMA1_RING_ELEMENT_SIZE
                      <:
                      usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let hint:t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Rust_primitives.mk_i32 0)
          (Rust_primitives.mk_usize 256)
        <:
        t_Array i32 (Rust_primitives.mk_usize 256))
      v_ROWS_IN_A
  in
  let previous_true_hints_seen:usize = Rust_primitives.mk_usize 0 in
  let i:usize = Rust_primitives.mk_usize 0 in
  let malformed_hint:bool = false in
  let hint, i, malformed_hint, previous_true_hints_seen:(t_Array
      (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A &
    usize &
    bool &
    usize) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let hint, i, malformed_hint, previous_true_hints_seen:(t_Array
              (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A &
            usize &
            bool &
            usize) =
            temp_0_
          in
          (i <. v_ROWS_IN_A <: bool) && (~.malformed_hint <: bool))
      (hint, i, malformed_hint, previous_true_hints_seen
        <:
        (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool & usize))
      (fun temp_0_ ->
          let hint, i, malformed_hint, previous_true_hints_seen:(t_Array
              (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A &
            usize &
            bool &
            usize) =
            temp_0_
          in
          let current_true_hints_seen:usize =
            cast (hint_serialized.[ v_MAX_ONES_IN_HINT +! i <: usize ] <: u8) <: usize
          in
          let malformed_hint:bool =
            if
              current_true_hints_seen <. previous_true_hints_seen ||
              previous_true_hints_seen >. v_MAX_ONES_IN_HINT
            then
              let malformed_hint:bool = true in
              malformed_hint
            else malformed_hint
          in
          let j:usize = previous_true_hints_seen in
          let hint, j, malformed_hint:(t_Array (t_Array i32 (Rust_primitives.mk_usize 256))
              v_ROWS_IN_A &
            usize &
            bool) =
            Rust_primitives.f_while_loop (fun temp_0_ ->
                  let hint, j, malformed_hint:(t_Array (t_Array i32 (Rust_primitives.mk_usize 256))
                      v_ROWS_IN_A &
                    usize &
                    bool) =
                    temp_0_
                  in
                  (~.malformed_hint <: bool) && (j <. current_true_hints_seen <: bool))
              (hint, j, malformed_hint
                <:
                (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool))
              (fun temp_0_ ->
                  let hint, j, malformed_hint:(t_Array (t_Array i32 (Rust_primitives.mk_usize 256))
                      v_ROWS_IN_A &
                    usize &
                    bool) =
                    temp_0_
                  in
                  let malformed_hint:bool =
                    if
                      j >. previous_true_hints_seen &&
                      (hint_serialized.[ j ] <: u8) <=.
                      (hint_serialized.[ j -! Rust_primitives.mk_usize 1 <: usize ] <: u8)
                    then
                      let malformed_hint:bool = true in
                      malformed_hint
                    else malformed_hint
                  in
                  if ~.malformed_hint
                  then
                    let hint:t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                        i
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (hint.[ i ]
                              <:
                              t_Array i32 (Rust_primitives.mk_usize 256))
                            (cast (hint_serialized.[ j ] <: u8) <: usize)
                            (Rust_primitives.mk_i32 1)
                          <:
                          t_Array i32 (Rust_primitives.mk_usize 256))
                    in
                    let j:usize = j +! Rust_primitives.mk_usize 1 in
                    hint, j, malformed_hint
                    <:
                    (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool
                    )
                  else
                    hint, j, malformed_hint
                    <:
                    (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool
                    ))
          in
          if ~.malformed_hint
          then
            let previous_true_hints_seen:usize = current_true_hints_seen in
            let i:usize = i +! Rust_primitives.mk_usize 1 in
            hint, i, malformed_hint, previous_true_hints_seen
            <:
            (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool & usize
            )
          else
            hint, i, malformed_hint, previous_true_hints_seen
            <:
            (t_Array (t_Array i32 (Rust_primitives.mk_usize 256)) v_ROWS_IN_A & usize & bool & usize
            ))
  in
  let i:usize = previous_true_hints_seen in
  let i, malformed_hint:(usize & bool) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let i, malformed_hint:(usize & bool) = temp_0_ in
          (i <. v_MAX_ONES_IN_HINT <: bool) && (~.malformed_hint <: bool))
      (i, malformed_hint <: (usize & bool))
      (fun temp_0_ ->
          let i, malformed_hint:(usize & bool) = temp_0_ in
          let malformed_hint:bool =
            if (hint_serialized.[ i ] <: u8) <>. Rust_primitives.mk_u8 0
            then
              let malformed_hint:bool = true in
              malformed_hint
            else malformed_hint
          in
          let i:usize = i +! Rust_primitives.mk_usize 1 in
          i, malformed_hint <: (usize & bool))
  in
  if malformed_hint
  then
    Core.Result.Result_Err
    (Libcrux_ml_dsa.Types.VerificationError_MalformedHintError
      <:
      Libcrux_ml_dsa.Types.t_VerificationError)
    <:
    Core.Result.t_Result
      (Libcrux_ml_dsa.Types.t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A
      ) Libcrux_ml_dsa.Types.t_VerificationError
  else
    Core.Result.Result_Ok
    ({
        Libcrux_ml_dsa.Types.f_commitment_hash
        =
        Core.Result.impl__unwrap #(t_Array u8 v_COMMITMENT_HASH_SIZE)
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 v_COMMITMENT_HASH_SIZE)
              #FStar.Tactics.Typeclasses.solve
              commitment_hash
            <:
            Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) Core.Array.t_TryFromSliceError);
        Libcrux_ml_dsa.Types.f_signer_response = signer_response;
        Libcrux_ml_dsa.Types.f_hint = hint
      }
      <:
      Libcrux_ml_dsa.Types.t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
    <:
    Core.Result.t_Result
      (Libcrux_ml_dsa.Types.t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A
      ) Libcrux_ml_dsa.Types.t_VerificationError

let impl__serialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self:
          Libcrux_ml_dsa.Types.t_Signature v_SIMDUnit
            v_COMMITMENT_HASH_SIZE
            v_COLUMNS_IN_A
            v_ROWS_IN_A)
     =
  let signature:t_Array u8 v_SIGNATURE_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_SIGNATURE_SIZE
  in
  let offset:usize = Rust_primitives.mk_usize 0 in
  let signature:t_Array u8 v_SIGNATURE_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range signature
      ({
          Core.Ops.Range.f_start = offset;
          Core.Ops.Range.f_end = offset +! v_COMMITMENT_HASH_SIZE <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (signature.[ {
                Core.Ops.Range.f_start = offset;
                Core.Ops.Range.f_end = offset +! v_COMMITMENT_HASH_SIZE <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (self.Libcrux_ml_dsa.Types.f_commitment_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! v_COMMITMENT_HASH_SIZE in
  let offset, signature:(usize & t_Array u8 v_SIGNATURE_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      v_COLUMNS_IN_A
      (fun temp_0_ temp_1_ ->
          let offset, signature:(usize & t_Array u8 v_SIGNATURE_SIZE) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (offset, signature <: (usize & t_Array u8 v_SIGNATURE_SIZE))
      (fun temp_0_ i ->
          let offset, signature:(usize & t_Array u8 v_SIGNATURE_SIZE) = temp_0_ in
          let i:usize = i in
          let signature:t_Array u8 v_SIGNATURE_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signature
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! v_GAMMA1_RING_ELEMENT_SIZE <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (signature.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! v_GAMMA1_RING_ELEMENT_SIZE <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_dsa.Encoding.Gamma1.serialize #v_SIMDUnit
                      v_GAMMA1_EXPONENT
                      v_GAMMA1_RING_ELEMENT_SIZE
                      (self.Libcrux_ml_dsa.Types.f_signer_response.[ i ]
                        <:
                        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! v_GAMMA1_RING_ELEMENT_SIZE in
          offset, signature <: (usize & t_Array u8 v_SIGNATURE_SIZE))
  in
  let true_hints_seen:usize = Rust_primitives.mk_usize 0 in
  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      v_ROWS_IN_A
      (fun temp_0_ temp_1_ ->
          let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize))
      (fun temp_0_ i ->
          let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
          let i:usize = i in
          let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (self.Libcrux_ml_dsa.Types.f_hint.[ i ]
                <:
                t_Array i32 (Rust_primitives.mk_usize 256))
              (fun temp_0_ temp_1_ ->
                  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
                  let _:usize = temp_1_ in
                  true)
              (signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize))
              (fun temp_0_ temp_1_ ->
                  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
                  let j, hint:(usize & i32) = temp_1_ in
                  if hint =. Rust_primitives.mk_i32 1 <: bool
                  then
                    let signature:t_Array u8 v_SIGNATURE_SIZE =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signature
                        (offset +! true_hints_seen <: usize)
                        (cast (j <: usize) <: u8)
                    in
                    let true_hints_seen:usize = true_hints_seen +! Rust_primitives.mk_usize 1 in
                    signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize)
                  else signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize))
          in
          let signature:t_Array u8 v_SIGNATURE_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signature
              ((offset +! v_MAX_ONES_IN_HINT <: usize) +! i <: usize)
              (cast (true_hints_seen <: usize) <: u8)
          in
          signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize))
  in
  signature
