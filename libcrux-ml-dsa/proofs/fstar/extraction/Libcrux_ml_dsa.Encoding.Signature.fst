module Libcrux_ml_dsa.Encoding.Signature
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let deserialize
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (columns_in_a rows_in_a commitment_hash_size gamma1_exponent gamma1_ring_element_size max_ones_in_hint signature_size:
          usize)
      (serialized out_commitment_hash: t_Slice u8)
      (out_signer_response: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (out_hint: t_Slice (t_Array i32 (sz 256)))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =. signature_size <: bool)
      in
      ()
  in
  let commitment_hash, rest_of_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 serialized commitment_hash_size
  in
  let out_commitment_hash:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out_commitment_hash
      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = commitment_hash_size }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out_commitment_hash.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = commitment_hash_size
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          commitment_hash
        <:
        t_Slice u8)
  in
  let signer_response_serialized, hint_serialized:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      rest_of_serialized
      (gamma1_ring_element_size *! columns_in_a <: usize)
  in
  let out_signer_response:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      columns_in_a
      (fun out_signer_response temp_1_ ->
          let out_signer_response:t_Slice
          (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            out_signer_response
          in
          let _:usize = temp_1_ in
          true)
      out_signer_response
      (fun out_signer_response i ->
          let out_signer_response:t_Slice
          (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            out_signer_response
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out_signer_response
            i
            (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
                gamma1_exponent
                (signer_response_serialized.[ {
                      Core.Ops.Range.f_start = i *! gamma1_ring_element_size <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! gamma1_ring_element_size <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (out_signer_response.[ i ]
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  let previous_true_hints_seen:usize = sz 0 in
  let i:usize = sz 0 in
  let malformed_hint:bool = false in
  let i, malformed_hint, out_hint, previous_true_hints_seen:(usize & bool &
    t_Slice (t_Array i32 (sz 256)) &
    usize) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let i, malformed_hint, out_hint, previous_true_hints_seen:(usize & bool &
            t_Slice (t_Array i32 (sz 256)) &
            usize) =
            temp_0_
          in
          (i <. rows_in_a <: bool) && (~.malformed_hint <: bool))
      (i, malformed_hint, out_hint, previous_true_hints_seen
        <:
        (usize & bool & t_Slice (t_Array i32 (sz 256)) & usize))
      (fun temp_0_ ->
          let i, malformed_hint, out_hint, previous_true_hints_seen:(usize & bool &
            t_Slice (t_Array i32 (sz 256)) &
            usize) =
            temp_0_
          in
          let current_true_hints_seen:usize =
            cast (hint_serialized.[ max_ones_in_hint +! i <: usize ] <: u8) <: usize
          in
          let malformed_hint:bool =
            if
              current_true_hints_seen <. previous_true_hints_seen ||
              previous_true_hints_seen >. max_ones_in_hint
            then
              let malformed_hint:bool = true in
              malformed_hint
            else malformed_hint
          in
          let j:usize = previous_true_hints_seen in
          let j, malformed_hint, out_hint:(usize & bool & t_Slice (t_Array i32 (sz 256))) =
            Rust_primitives.f_while_loop (fun temp_0_ ->
                  let j, malformed_hint, out_hint:(usize & bool & t_Slice (t_Array i32 (sz 256))) =
                    temp_0_
                  in
                  (~.malformed_hint <: bool) && (j <. current_true_hints_seen <: bool))
              (j, malformed_hint, out_hint <: (usize & bool & t_Slice (t_Array i32 (sz 256))))
              (fun temp_0_ ->
                  let j, malformed_hint, out_hint:(usize & bool & t_Slice (t_Array i32 (sz 256))) =
                    temp_0_
                  in
                  let malformed_hint:bool =
                    if
                      j >. previous_true_hints_seen &&
                      (hint_serialized.[ j ] <: u8) <=.
                      (hint_serialized.[ j -! sz 1 <: usize ] <: u8)
                    then
                      let malformed_hint:bool = true in
                      malformed_hint
                    else malformed_hint
                  in
                  if ~.malformed_hint
                  then
                    let out_hint:t_Slice (t_Array i32 (sz 256)) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out_hint
                        i
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (out_hint.[ i ]
                              <:
                              t_Array i32 (sz 256))
                            (cast (hint_serialized.[ j ] <: u8) <: usize)
                            1l
                          <:
                          t_Array i32 (sz 256))
                    in
                    let j:usize = j +! sz 1 in
                    j, malformed_hint, out_hint <: (usize & bool & t_Slice (t_Array i32 (sz 256)))
                  else
                    j, malformed_hint, out_hint <: (usize & bool & t_Slice (t_Array i32 (sz 256))))
          in
          if ~.malformed_hint
          then
            let previous_true_hints_seen:usize = current_true_hints_seen in
            let i:usize = i +! sz 1 in
            i, malformed_hint, out_hint, previous_true_hints_seen
            <:
            (usize & bool & t_Slice (t_Array i32 (sz 256)) & usize)
          else
            i, malformed_hint, out_hint, previous_true_hints_seen
            <:
            (usize & bool & t_Slice (t_Array i32 (sz 256)) & usize))
  in
  let i:usize = previous_true_hints_seen in
  let i, malformed_hint:(usize & bool) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let i, malformed_hint:(usize & bool) = temp_0_ in
          (i <. max_ones_in_hint <: bool) && (~.malformed_hint <: bool))
      (i, malformed_hint <: (usize & bool))
      (fun temp_0_ ->
          let i, malformed_hint:(usize & bool) = temp_0_ in
          let malformed_hint:bool =
            if (hint_serialized.[ i ] <: u8) <>. 0uy
            then
              let malformed_hint:bool = true in
              malformed_hint
            else malformed_hint
          in
          let i:usize = i +! sz 1 in
          i, malformed_hint <: (usize & bool))
  in
  if malformed_hint
  then
    out_commitment_hash,
    out_signer_response,
    out_hint,
    (Core.Result.Result_Err
      (Libcrux_ml_dsa.Types.VerificationError_MalformedHintError
        <:
        Libcrux_ml_dsa.Types.t_VerificationError)
      <:
      Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
    <:
    (t_Slice u8 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
      t_Slice (t_Array i32 (sz 256)) &
      Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
  else
    let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError =
      Core.Result.Result_Ok (() <: Prims.unit)
      <:
      Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError
    in
    out_commitment_hash, out_signer_response, out_hint, hax_temp_output
    <:
    (t_Slice u8 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
      t_Slice (t_Array i32 (sz 256)) &
      Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)

let serialize
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (commitment_hash: t_Slice u8)
      (signer_response: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (hint: t_Slice (t_Array i32 (sz 256)))
      (commitment_hash_size columns_in_a rows_in_a gamma1_exponent gamma1_ring_element_size max_ones_in_hint:
          usize)
      (signature: t_Slice u8)
     =
  let offset:usize = sz 0 in
  let signature:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range signature
      ({
          Core.Ops.Range.f_start = offset;
          Core.Ops.Range.f_end = offset +! commitment_hash_size <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (signature.[ {
                Core.Ops.Range.f_start = offset;
                Core.Ops.Range.f_end = offset +! commitment_hash_size <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          commitment_hash
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! commitment_hash_size in
  let offset, signature:(usize & t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      columns_in_a
      (fun temp_0_ temp_1_ ->
          let offset, signature:(usize & t_Slice u8) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (offset, signature <: (usize & t_Slice u8))
      (fun temp_0_ i ->
          let offset, signature:(usize & t_Slice u8) = temp_0_ in
          let i:usize = i in
          let signature:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range signature
              ({
                  Core.Ops.Range.f_start = offset;
                  Core.Ops.Range.f_end = offset +! gamma1_ring_element_size <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Libcrux_ml_dsa.Encoding.Gamma1.serialize #v_SIMDUnit
                  (signer_response.[ i ]
                    <:
                    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  (signature.[ {
                        Core.Ops.Range.f_start = offset;
                        Core.Ops.Range.f_end = offset +! gamma1_ring_element_size <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  gamma1_exponent
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! gamma1_ring_element_size in
          offset, signature <: (usize & t_Slice u8))
  in
  let true_hints_seen:usize = sz 0 in
  let signature, true_hints_seen:(t_Slice u8 & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      rows_in_a
      (fun temp_0_ temp_1_ ->
          let signature, true_hints_seen:(t_Slice u8 & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (signature, true_hints_seen <: (t_Slice u8 & usize))
      (fun temp_0_ i ->
          let signature, true_hints_seen:(t_Slice u8 & usize) = temp_0_ in
          let i:usize = i in
          let signature, true_hints_seen:(t_Slice u8 & usize) =
            Rust_primitives.Hax.Folds.fold_range (sz 0)
              (Core.Slice.impl__len #i32 (hint.[ i ] <: t_Slice i32) <: usize)
              (fun temp_0_ temp_1_ ->
                  let signature, true_hints_seen:(t_Slice u8 & usize) = temp_0_ in
                  let _:usize = temp_1_ in
                  true)
              (signature, true_hints_seen <: (t_Slice u8 & usize))
              (fun temp_0_ j ->
                  let signature, true_hints_seen:(t_Slice u8 & usize) = temp_0_ in
                  let j:usize = j in
                  if ((hint.[ i ] <: t_Array i32 (sz 256)).[ j ] <: i32) =. 1l <: bool
                  then
                    let signature:t_Slice u8 =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signature
                        (offset +! true_hints_seen <: usize)
                        (cast (j <: usize) <: u8)
                    in
                    let true_hints_seen:usize = true_hints_seen +! sz 1 in
                    signature, true_hints_seen <: (t_Slice u8 & usize)
                  else signature, true_hints_seen <: (t_Slice u8 & usize))
          in
          let signature:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signature
              ((offset +! max_ones_in_hint <: usize) +! i <: usize)
              (cast (true_hints_seen <: usize) <: u8)
          in
          signature, true_hints_seen <: (t_Slice u8 & usize))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  signature
