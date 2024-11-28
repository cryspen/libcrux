module Libcrux_ml_dsa.Ml_dsa_generic.Rec_bundle_908667160
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  let open Libcrux_sha3.Portable.Incremental in
  ()

type t_SigningError =
  | SigningError_RejectionSamplingError : t_SigningError
  | SigningError_ContextTooLongError : t_SigningError

let t_SigningError_cast_to_repr (x: t_SigningError) : isize =
  match x with
  | SigningError_RejectionSamplingError  -> isz 0
  | SigningError_ContextTooLongError  -> isz 1

type t_VerificationError =
  | VerificationError_MalformedHintError : t_VerificationError
  | VerificationError_SignerResponseExceedsBoundError : t_VerificationError
  | VerificationError_CommitmentHashesDontMatchError : t_VerificationError
  | VerificationError_ContextTooLongError : t_VerificationError

let t_VerificationError_cast_to_repr (x: t_VerificationError) : isize =
  match x with
  | VerificationError_MalformedHintError  -> isz 0
  | VerificationError_SignerResponseExceedsBoundError  -> isz 1
  | VerificationError_CommitmentHashesDontMatchError  -> isz 3
  | VerificationError_ContextTooLongError  -> isz 6

/// Binds the context string to an optional pre-hash OID identifying
/// the hash function or XOF used for pre-hashing.
type t_DomainSeparationContext = {
  f_context:t_Slice u8;
  f_pre_hash_oid:Core.Option.t_Option (t_Array u8 (sz 11))
}

/// Returns the context, guaranteed to be at most 255 bytes long.
let context (self: t_DomainSeparationContext) : t_Slice u8 = self.f_context

/// Returns the pre-hash OID, if any.
let pre_hash_oid (self: t_DomainSeparationContext) : Core.Option.t_Option (t_Array u8 (sz 11)) =
  self.f_pre_hash_oid

type t_DomainSeparationError = | DomainSeparationError_ContextTooLongError : t_DomainSeparationError

/// `context` must be at most 255 bytes long.
let v_new (context: t_Slice u8) (pre_hash_oid: Core.Option.t_Option (t_Array u8 (sz 11)))
    : Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError =
  if (Core.Slice.impl__len #u8 context <: usize) >. Libcrux_ml_dsa.Constants.v_CONTEXT_MAX_LEN
  then
    Core.Result.Result_Err (DomainSeparationError_ContextTooLongError <: t_DomainSeparationError)
    <:
    Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError
  else
    Core.Result.Result_Ok
    ({ f_context = context; f_pre_hash_oid = pre_hash_oid } <: t_DomainSeparationContext)
    <:
    Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_SigningError t_DomainSeparationError =
  {
    f_from_pre = (fun (e: t_DomainSeparationError) -> true);
    f_from_post = (fun (e: t_DomainSeparationError) (out: t_SigningError) -> true);
    f_from
    =
    fun (e: t_DomainSeparationError) ->
      match e with
      | DomainSeparationError_ContextTooLongError  ->
        SigningError_ContextTooLongError <: t_SigningError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From t_VerificationError t_DomainSeparationError =
  {
    f_from_pre = (fun (e: t_DomainSeparationError) -> true);
    f_from_post = (fun (e: t_DomainSeparationError) (out: t_VerificationError) -> true);
    f_from
    =
    fun (e: t_DomainSeparationError) ->
      match e with
      | DomainSeparationError_ContextTooLongError  ->
        VerificationError_ContextTooLongError <: t_VerificationError
  }

let t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError) : isize =
  match x with | DomainSeparationError_ContextTooLongError  -> isz 0

class v_PreHash (v_Self: Type0) (v_DIGEST_LEN: usize) = {
  f_oid_pre:Prims.unit -> Type0;
  f_oid_post:Prims.unit -> t_Array u8 (sz 11) -> Type0;
  f_oid:x0: Prims.unit
    -> Prims.Pure (t_Array u8 (sz 11)) (f_oid_pre x0) (fun result -> f_oid_post x0 result);
  f_hash_pre:t_Slice u8 -> Type0;
  f_hash_post:t_Slice u8 -> t_Array u8 v_DIGEST_LEN -> Type0;
  f_hash:x0: t_Slice u8
    -> Prims.Pure (t_Array u8 v_DIGEST_LEN) (f_hash_pre x0) (fun result -> f_hash_post x0 result)
}

/// An implementation of the pre-hash trait for the SHAKE-128 XOF with
/// digest length 256 bytes.
type t_SHAKE128_PH = | SHAKE128_PH : t_SHAKE128_PH

let v_PRE_HASH_OID_LEN: usize = sz 11

type t_Signature
  (v_SIMDUnit: Type0) (v_COMMITMENT_HASH_SIZE: usize) (v_COLUMNS_IN_A: usize) (v_ROWS_IN_A: usize)
  {| i1: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit |}
  = {
  f_commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE;
  f_signer_response:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_COLUMNS_IN_A;
  f_hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A
}

let deserialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Core.Result.t_Result
      (t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A) t_VerificationError =
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
    Rust_primitives.Hax.Folds.fold_range (sz 0)
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
                      (i +! sz 1 <: usize) *! v_GAMMA1_RING_ELEMENT_SIZE <: usize
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
  let hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0l (sz 256) <: t_Array i32 (sz 256))
      v_ROWS_IN_A
  in
  let previous_true_hints_seen:usize = sz 0 in
  let i:usize = sz 0 in
  let malformed_hint:bool = false in
  let hint, i, malformed_hint, previous_true_hints_seen:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A &
    usize &
    bool &
    usize) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let hint, i, malformed_hint, previous_true_hints_seen:(t_Array (t_Array i32 (sz 256))
              v_ROWS_IN_A &
            usize &
            bool &
            usize) =
            temp_0_
          in
          (i <. v_ROWS_IN_A <: bool) && (~.malformed_hint <: bool))
      (hint, i, malformed_hint, previous_true_hints_seen
        <:
        (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool & usize))
      (fun temp_0_ ->
          let hint, i, malformed_hint, previous_true_hints_seen:(t_Array (t_Array i32 (sz 256))
              v_ROWS_IN_A &
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
          let hint, j, malformed_hint:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool) =
            Rust_primitives.f_while_loop (fun temp_0_ ->
                  let hint, j, malformed_hint:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize &
                    bool) =
                    temp_0_
                  in
                  (~.malformed_hint <: bool) && (j <. current_true_hints_seen <: bool))
              (hint, j, malformed_hint
                <:
                (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool))
              (fun temp_0_ ->
                  let hint, j, malformed_hint:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize &
                    bool) =
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
                    let hint:t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hint
                        i
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (hint.[ i ]
                              <:
                              t_Array i32 (sz 256))
                            (cast (hint_serialized.[ j ] <: u8) <: usize)
                            1l
                          <:
                          t_Array i32 (sz 256))
                    in
                    let j:usize = j +! sz 1 in
                    hint, j, malformed_hint
                    <:
                    (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool)
                  else
                    hint, j, malformed_hint
                    <:
                    (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool))
          in
          if ~.malformed_hint
          then
            let previous_true_hints_seen:usize = current_true_hints_seen in
            let i:usize = i +! sz 1 in
            hint, i, malformed_hint, previous_true_hints_seen
            <:
            (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool & usize)
          else
            hint, i, malformed_hint, previous_true_hints_seen
            <:
            (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize & bool & usize))
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
    Core.Result.Result_Err (VerificationError_MalformedHintError <: t_VerificationError)
    <:
    Core.Result.t_Result (t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
      t_VerificationError
  else
    Core.Result.Result_Ok
    ({
        f_commitment_hash
        =
        Core.Result.impl__unwrap #(t_Array u8 v_COMMITMENT_HASH_SIZE)
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 v_COMMITMENT_HASH_SIZE)
              #FStar.Tactics.Typeclasses.solve
              commitment_hash
            <:
            Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) Core.Array.t_TryFromSliceError);
        f_signer_response = signer_response;
        f_hint = hint
      }
      <:
      t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
    <:
    Core.Result.t_Result (t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
      t_VerificationError

let serialize
      (#v_SIMDUnit: Type0)
      (v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_MAX_ONES_IN_HINT v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (self: t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
    : t_Array u8 v_SIGNATURE_SIZE =
  let signature:t_Array u8 v_SIGNATURE_SIZE = Rust_primitives.Hax.repeat 0uy v_SIGNATURE_SIZE in
  let offset:usize = sz 0 in
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
          (self.f_commitment_hash <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = offset +! v_COMMITMENT_HASH_SIZE in
  let offset, signature:(usize & t_Array u8 v_SIGNATURE_SIZE) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
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
                      (self.f_signer_response.[ i ]
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
  let true_hints_seen:usize = sz 0 in
  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
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
            Rust_primitives.Hax.Folds.fold_enumerated_slice (self.f_hint.[ i ]
                <:
                t_Array i32 (sz 256))
              (fun temp_0_ temp_1_ ->
                  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
                  let _:usize = temp_1_ in
                  true)
              (signature, true_hints_seen <: (t_Array u8 v_SIGNATURE_SIZE & usize))
              (fun temp_0_ temp_1_ ->
                  let signature, true_hints_seen:(t_Array u8 v_SIGNATURE_SIZE & usize) = temp_0_ in
                  let j, hint:(usize & i32) = temp_1_ in
                  if hint =. 1l <: bool
                  then
                    let signature:t_Array u8 v_SIGNATURE_SIZE =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize signature
                        (offset +! true_hints_seen <: usize)
                        (cast (j <: usize) <: u8)
                    in
                    let true_hints_seen:usize = true_hints_seen +! sz 1 in
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

/// This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
/// 8, resp.).
/// If `domain_separation_context` is supplied, applies domain
/// separation and length encoding to the context string,
/// before appending the message (in the regular variant) or the
/// pre-hash OID as well as the pre-hashed message digest. Otherwise,
/// it is assumed that `message` already contains domain separation
/// information.
/// In FIPS 204 M' is the concatenation of the domain separated context, any
/// potential pre-hash OID and the message (or the message pre-hash). We do not
/// explicitely construct the concatenation in memory since it is of statically unknown
/// length, but feed its components directly into the incremental XOF.
/// Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
/// 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
/// for details on the domain separation for regular ML-DSA. Line
/// 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation for the HashMl-DSA
/// variant.
let derive_message_representative
      (verification_key_hash: t_Array u8 (sz 64))
      (domain_separation_context: Core.Option.t_Option t_DomainSeparationContext)
      (message: t_Slice u8)
      (message_representative: t_Array u8 (sz 64))
    : t_Array u8 (sz 64) =
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (verification_key_hash <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    match domain_separation_context with
    | Core.Option.Option_Some domain_separation_context ->
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Option.impl__is_some #(t_Array u8 (sz 11))
                        (pre_hash_oid domain_separation_context
                          <:
                          Core.Option.t_Option (t_Array u8 (sz 11)))
                      <:
                      bool)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          ((let list =
                [
                  cast (Core.Slice.impl__len #u8 (context domain_separation_context <: t_Slice u8)
                      <:
                      usize)
                  <:
                  u8
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (context domain_separation_context <: t_Slice u8)
      in
      (match pre_hash_oid domain_separation_context with
        | Core.Option.Option_Some pre_hash_oid ->
          Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
            #(sz 136)
            #FStar.Tactics.Typeclasses.solve
            shake
            (pre_hash_oid <: t_Slice u8)
        | _ -> shake)
    | _ -> shake
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
    Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      message
  in
  let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 64)) =
    Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      message_representative
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
  let message_representative:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  message_representative

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: v_PreHash t_SHAKE128_PH (sz 256) =
  {
    f_oid_pre = (fun (_: Prims.unit) -> true);
    f_oid_post = (fun (_: Prims.unit) (out: t_Array u8 (sz 11)) -> true);
    f_oid
    =
    (fun (_: Prims.unit) ->
        let list = [6uy; 9uy; 96uy; 134uy; 72uy; 1uy; 101uy; 3uy; 4uy; 2uy; 11uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
        Rust_primitives.Hax.array_of_list 11 list);
    f_hash_pre = (fun (message: t_Slice u8) -> true);
    f_hash_post = (fun (message: t_Slice u8) (out: t_Array u8 (sz 256)) -> true);
    f_hash
    =
    fun (message: t_Slice u8) ->
      let output:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
      let output:t_Array u8 (sz 256) =
        Libcrux_ml_dsa.Hash_functions.Shake128.f_shake128 #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128
          #FStar.Tactics.Typeclasses.solve
          (sz 256)
          message
          output
      in
      output
  }

/// The internal signing API.
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
let sign_internal
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context: Core.Option.t_Option t_DomainSeparationContext)
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError =
  let seed_for_A, seed_for_signing, verification_key_hash, s1_as_ntt, s2_as_ntt, t0_as_ntt:(t_Array
      u8 (sz 32) &
    t_Array u8 (sz 32) &
    t_Array u8 (sz 64) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Encoding.Signing_key.deserialize_then_ntt #v_SIMDUnit
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      v_ETA
      v_ERROR_RING_ELEMENT_SIZE
      v_SIGNING_KEY_SIZE
      signing_key
  in
  let v_A_as_ntt:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
      #v_Shake128X4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) (seed_for_A <: t_Slice u8)
        <:
        t_Array u8 (sz 34))
  in
  let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let message_representative:t_Array u8 (sz 64) =
    derive_message_representative verification_key_hash
      domain_separation_context
      message
      message_representative
  in
  let mask_seed:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (seed_for_signing <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
    Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (message_representative <: t_Slice u8)
  in
  let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 64)) =
    Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      mask_seed
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
  let mask_seed:t_Array u8 (sz 64) = tmp1 in
  let _:Prims.unit = () in
  let _:Prims.unit = () in
  let (domain_separator_for_mask: u16):u16 = 0us in
  let v_BETA:i32 = cast (v_ONES_IN_VERIFIER_CHALLENGE *! v_ETA <: usize) <: i32 in
  let attempt:usize = sz 0 in
  let commitment_hash:Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) =
    Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE)
  in
  let signer_response:Core.Option.t_Option
  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
    Core.Option.Option_None
    <:
    Core.Option.t_Option
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
  in
  let hint:Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) =
    Core.Option.Option_None <: Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A)
  in
  let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
    Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
    u16 &
    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
    Core.Option.t_Option
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
            Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
            u16 &
            Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
            Core.Option.t_Option
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
          =
            temp_0_
          in
          attempt <. Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND_SIGN <: bool)
      (attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
        <:
        (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
          Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
          Core.Option.t_Option
          (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)))
      (fun temp_0_ ->
          let attempt, commitment_hash, domain_separator_for_mask, hint, signer_response:(usize &
            Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) &
            u16 &
            Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
            Core.Option.t_Option
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A))
          =
            temp_0_
          in
          let attempt:usize = attempt +! sz 1 in
          let tmp0, out:(u16 &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A) =
            Libcrux_ml_dsa.Sample.sample_mask_vector #v_SIMDUnit
              #v_Shake256
              #v_Shake256X4
              v_COLUMNS_IN_A
              v_GAMMA1_EXPONENT
              (Libcrux_ml_dsa.Utils.into_padded_array (sz 66) (mask_seed <: t_Slice u8)
                <:
                t_Array u8 (sz 66))
              domain_separator_for_mask
          in
          let domain_separator_for_mask:u16 = tmp0 in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_COLUMNS_IN_A =
            out
          in
          let v_A_times_mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.compute_A_times_mask #v_SIMDUnit
              v_ROWS_IN_A
              v_COLUMNS_IN_A
              v_A_as_ntt
              mask
          in
          let w0, commitment:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              v_ROWS_IN_A &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
            Libcrux_ml_dsa.Arithmetic.decompose_vector #v_SIMDUnit
              v_ROWS_IN_A
              v_GAMMA2
              v_A_times_mask
          in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE =
            Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
          in
          let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
            Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
              v_ROWS_IN_A
              v_COMMITMENT_RING_ELEMENT_SIZE
              v_COMMITMENT_VECTOR_SIZE
              commitment
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
            Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              ()
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
            Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              (message_representative <: t_Slice u8)
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
            Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              (commitment_serialized <: t_Slice u8)
          in
          let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze &
            t_Array u8 v_COMMITMENT_HASH_SIZE) =
            Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
              #(sz 136)
              #FStar.Tactics.Typeclasses.solve
              shake
              commitment_hash_candidate
          in
          let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
          let commitment_hash_candidate:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
          let _:Prims.unit = () in
          let _:Prims.unit = () in
          let verifier_challenge_as_ntt:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit
          =
            Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
              (Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
                  #v_Shake256
                  v_ONES_IN_VERIFIER_CHALLENGE
                  v_COMMITMENT_HASH_SIZE
                  commitment_hash_candidate
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          let challenge_times_s1:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              v_COLUMNS_IN_A
              s1_as_ntt
              verifier_challenge_as_ntt
          in
          let challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
              v_ROWS_IN_A
              s2_as_ntt
              verifier_challenge_as_ntt
          in
          let signer_response_candidate:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A =
            Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit v_COLUMNS_IN_A mask challenge_times_s1
          in
          let w0_minus_challenge_times_s2:t_Array
            (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
            Libcrux_ml_dsa.Matrix.subtract_vectors #v_SIMDUnit v_ROWS_IN_A w0 challenge_times_s2
          in
          if
            Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
              v_COLUMNS_IN_A
              signer_response_candidate
              ((1l <<! v_GAMMA1_EXPONENT <: i32) -! v_BETA <: i32)
          then
            attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
            <:
            (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
              Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
              Core.Option.t_Option
              (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A
              ))
          else
            if
              Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
                v_ROWS_IN_A
                w0_minus_challenge_times_s2
                (v_GAMMA2 -! v_BETA <: i32)
            then
              attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
              <:
              (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                Core.Option.t_Option
                (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                    v_COLUMNS_IN_A))
            else
              let challenge_times_t0:t_Array
                (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
                Libcrux_ml_dsa.Matrix.vector_times_ring_element #v_SIMDUnit
                  v_ROWS_IN_A
                  t0_as_ntt
                  verifier_challenge_as_ntt
              in
              if
                Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
                  v_ROWS_IN_A
                  challenge_times_t0
                  v_GAMMA2
              then
                attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                <:
                (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                  Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                  Core.Option.t_Option
                  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      v_COLUMNS_IN_A))
              else
                let w0_minus_c_times_s2_plus_c_times_t0:t_Array
                  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
                  Libcrux_ml_dsa.Matrix.add_vectors #v_SIMDUnit
                    v_ROWS_IN_A
                    w0_minus_challenge_times_s2
                    challenge_times_t0
                in
                let hint_candidate, ones_in_hint:(t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A & usize
                ) =
                  Libcrux_ml_dsa.Arithmetic.make_hint #v_SIMDUnit
                    v_ROWS_IN_A
                    v_GAMMA2
                    w0_minus_c_times_s2_plus_c_times_t0
                    commitment
                in
                if ones_in_hint >. v_MAX_ONES_IN_HINT
                then
                  attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                  <:
                  (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A))
                else
                  let attempt:usize = Libcrux_ml_dsa.Constants.v_REJECTION_SAMPLE_BOUND_SIGN in
                  let commitment_hash:Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) =
                    Core.Option.Option_Some commitment_hash_candidate
                    <:
                    Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE)
                  in
                  let signer_response:Core.Option.t_Option
                  (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                      v_COLUMNS_IN_A) =
                    Core.Option.Option_Some signer_response_candidate
                    <:
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A)
                  in
                  let hint:Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) =
                    Core.Option.Option_Some hint_candidate
                    <:
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A)
                  in
                  attempt, commitment_hash, domain_separator_for_mask, hint, signer_response
                  <:
                  (usize & Core.Option.t_Option (t_Array u8 v_COMMITMENT_HASH_SIZE) & u16 &
                    Core.Option.t_Option (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) &
                    Core.Option.t_Option
                    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                        v_COLUMNS_IN_A)))
  in
  match
    match commitment_hash with
    | Core.Option.Option_Some commitment_hash ->
      Core.Result.Result_Ok commitment_hash
      <:
      Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) t_SigningError
    | Core.Option.Option_None  ->
      Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
      <:
      Core.Result.t_Result (t_Array u8 v_COMMITMENT_HASH_SIZE) t_SigningError
  with
  | Core.Result.Result_Ok commitment_hash ->
    (match
        match signer_response with
        | Core.Option.Option_Some signer_response ->
          Core.Result.Result_Ok signer_response
          <:
          Core.Result.t_Result
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            t_SigningError
        | Core.Option.Option_None  ->
          Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
          <:
          Core.Result.t_Result
            (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
            t_SigningError
      with
      | Core.Result.Result_Ok signer_response ->
        (match
            match hint with
            | Core.Option.Option_Some hint ->
              Core.Result.Result_Ok hint
              <:
              Core.Result.t_Result (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) t_SigningError
            | Core.Option.Option_None  ->
              Core.Result.Result_Err (SigningError_RejectionSamplingError <: t_SigningError)
              <:
              Core.Result.t_Result (t_Array (t_Array i32 (sz 256)) v_ROWS_IN_A) t_SigningError
          with
          | Core.Result.Result_Ok hint ->
            let signature:t_Array u8 v_SIGNATURE_SIZE =
              serialize #v_SIMDUnit
                v_COMMITMENT_HASH_SIZE
                v_COLUMNS_IN_A
                v_ROWS_IN_A
                v_GAMMA1_EXPONENT
                v_GAMMA1_RING_ELEMENT_SIZE
                v_MAX_ONES_IN_HINT
                v_SIGNATURE_SIZE
                ({
                    f_commitment_hash = commitment_hash;
                    f_signer_response = signer_response;
                    f_hint = hint
                  }
                  <:
                  t_Signature v_SIMDUnit v_COMMITMENT_HASH_SIZE v_COLUMNS_IN_A v_ROWS_IN_A)
            in
            Core.Result.Result_Ok
            (Libcrux_ml_dsa.Types.MLDSASignature signature
              <:
              Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              t_SigningError
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE)
              t_SigningError)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError
    )
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError

let sign
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT: usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError =
  match v_new context (Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 (sz 11))) with
  | Core.Result.Result_Ok hoist36 ->
    sign_internal #v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4 v_ROWS_IN_A v_COLUMNS_IN_A
      v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
      v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
      v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE signing_key
      message (Core.Option.Option_Some hoist36 <: Core.Option.t_Option t_DomainSeparationContext)
      randomness
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err (Core.Convert.f_from #FStar.Tactics.Typeclasses.solve err)
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError

let sign_pre_hashed
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4 #v_PH: Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT:
          usize)
      (v_GAMMA2: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: v_PreHash v_PH v_PH_DIGEST_LEN)
      (signing_key: t_Array u8 v_SIGNING_KEY_SIZE)
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
    : Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError =
  if (Core.Slice.impl__len #u8 context <: usize) >. Libcrux_ml_dsa.Constants.v_CONTEXT_MAX_LEN
  then
    Core.Result.Result_Err (SigningError_ContextTooLongError <: t_SigningError)
    <:
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError
  else
    let pre_hashed_message:t_Array u8 v_PH_DIGEST_LEN =
      Libcrux_ml_dsa.Pre_hash.f_hash #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve message
    in
    match
      v_new context
        (Core.Option.Option_Some
          (Libcrux_ml_dsa.Pre_hash.f_oid #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve ()
            <:
            t_Array u8 (sz 11))
          <:
          Core.Option.t_Option (t_Array u8 (sz 11)))
    with
    | Core.Result.Result_Ok hoist39 ->
      sign_internal #v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4 v_ROWS_IN_A v_COLUMNS_IN_A
        v_ETA v_ERROR_RING_ELEMENT_SIZE v_GAMMA1_EXPONENT v_GAMMA2 v_COMMITMENT_RING_ELEMENT_SIZE
        v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE
        v_MAX_ONES_IN_HINT v_GAMMA1_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_SIGNATURE_SIZE
        signing_key (pre_hashed_message <: t_Slice u8)
        (Core.Option.Option_Some hoist39 <: Core.Option.t_Option t_DomainSeparationContext)
        randomness
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err (Core.Convert.f_from #FStar.Tactics.Typeclasses.solve err)
      <:
      Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature v_SIGNATURE_SIZE) t_SigningError

/// The internal verification API.
/// If no `domain_separation_context` is supplied, it is assumed that
/// `message` already contains the domain separation.
let verify_internal
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message: t_Slice u8)
      (domain_separation_context: Core.Option.t_Option t_DomainSeparationContext)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Core.Result.t_Result Prims.unit t_VerificationError =
  let seed_for_A, t1:(t_Array u8 (sz 32) &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Encoding.Verification_key.deserialize #v_SIMDUnit
      v_ROWS_IN_A
      v_VERIFICATION_KEY_SIZE
      verification_key_serialized
  in
  match
    deserialize #v_SIMDUnit
      v_COMMITMENT_HASH_SIZE
      v_COLUMNS_IN_A
      v_ROWS_IN_A
      v_GAMMA1_EXPONENT
      v_GAMMA1_RING_ELEMENT_SIZE
      v_MAX_ONES_IN_HINT
      v_SIGNATURE_SIZE
      signature_serialized
  with
  | Core.Result.Result_Ok signature ->
    if
      ~.(Libcrux_ml_dsa.Arithmetic.vector_infinity_norm_exceeds #v_SIMDUnit
          v_COLUMNS_IN_A
          signature.f_signer_response
          ((2l <<! v_GAMMA1_EXPONENT <: i32) -! v_BETA <: i32)
        <:
        bool)
    then
      let v_A_as_ntt:t_Array
        (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
          #v_Shake128X4
          v_ROWS_IN_A
          v_COLUMNS_IN_A
          (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) (seed_for_A <: t_Slice u8)
            <:
            t_Array u8 (sz 34))
      in
      let verification_key_hash:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let verification_key_hash:t_Array u8 (sz 64) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
          #FStar.Tactics.Typeclasses.solve
          (sz 64)
          (verification_key_serialized <: t_Slice u8)
          verification_key_hash
      in
      let message_representative:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
      let message_representative:t_Array u8 (sz 64) =
        derive_message_representative verification_key_hash
          domain_separation_context
          message
          message_representative
      in
      let verifier_challenge_as_ntt:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Ntt.ntt #v_SIMDUnit
          (Libcrux_ml_dsa.Sample.sample_challenge_ring_element #v_SIMDUnit
              #v_Shake256
              v_ONES_IN_VERIFIER_CHALLENGE
              v_COMMITMENT_HASH_SIZE
              signature.f_commitment_hash
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let w_approx:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Matrix.compute_w_approx #v_SIMDUnit
          v_ROWS_IN_A
          v_COLUMNS_IN_A
          v_A_as_ntt
          signature.f_signer_response
          verifier_challenge_as_ntt
          t1
      in
      let commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE =
        Rust_primitives.Hax.repeat 0uy v_COMMITMENT_HASH_SIZE
      in
      let commitment:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
        v_ROWS_IN_A =
        Libcrux_ml_dsa.Arithmetic.use_hint #v_SIMDUnit
          v_ROWS_IN_A
          v_GAMMA2
          signature.f_hint
          w_approx
      in
      let commitment_serialized:t_Array u8 v_COMMITMENT_VECTOR_SIZE =
        Libcrux_ml_dsa.Encoding.Commitment.serialize_vector #v_SIMDUnit
          v_ROWS_IN_A
          v_COMMITMENT_RING_ELEMENT_SIZE
          v_COMMITMENT_VECTOR_SIZE
          commitment
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          ()
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
        Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (message_representative <: t_Slice u8)
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
        Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          (commitment_serialized <: t_Slice u8)
      in
      let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze &
        t_Array u8 v_COMMITMENT_HASH_SIZE) =
        Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
          #(sz 136)
          #FStar.Tactics.Typeclasses.solve
          shake
          commitment_hash
      in
      let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
      let commitment_hash:t_Array u8 v_COMMITMENT_HASH_SIZE = tmp1 in
      let _:Prims.unit = () in
      let _:Prims.unit = () in
      if signature.f_commitment_hash <>. commitment_hash
      then
        Core.Result.Result_Err
        (VerificationError_CommitmentHashesDontMatchError <: t_VerificationError)
        <:
        Core.Result.t_Result Prims.unit t_VerificationError
      else
        Core.Result.Result_Ok (() <: Prims.unit)
        <:
        Core.Result.t_Result Prims.unit t_VerificationError
    else
      Core.Result.Result_Err
      (VerificationError_SignerResponseExceedsBoundError <: t_VerificationError)
      <:
      Core.Result.t_Result Prims.unit t_VerificationError
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit t_VerificationError

let verify
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Core.Result.t_Result Prims.unit t_VerificationError =
  match v_new context (Core.Option.Option_None <: Core.Option.t_Option (t_Array u8 (sz 11))) with
  | Core.Result.Result_Ok hoist41 ->
    verify_internal #v_SIMDUnit #v_Shake128X4 #v_Shake256 v_ROWS_IN_A v_COLUMNS_IN_A
      v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2
      v_BETA v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT verification_key_serialized message
      (Core.Option.Option_Some hoist41 <: Core.Option.t_Option t_DomainSeparationContext)
      signature_serialized
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err (Core.Convert.f_from #FStar.Tactics.Typeclasses.solve err)
    <:
    Core.Result.t_Result Prims.unit t_VerificationError

let verify_pre_hashed
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_PH: Type0)
      (v_PH_DIGEST_LEN v_ROWS_IN_A v_COLUMNS_IN_A v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE:
          usize)
      (v_GAMMA2 v_BETA: i32)
      (v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: v_PreHash v_PH v_PH_DIGEST_LEN)
      (verification_key_serialized: t_Array u8 v_VERIFICATION_KEY_SIZE)
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 v_SIGNATURE_SIZE)
    : Core.Result.t_Result Prims.unit t_VerificationError =
  let pre_hashed_message:t_Array u8 v_PH_DIGEST_LEN =
    Libcrux_ml_dsa.Pre_hash.f_hash #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve message
  in
  match
    v_new context
      (Core.Option.Option_Some
        (Libcrux_ml_dsa.Pre_hash.f_oid #v_PH #v_PH_DIGEST_LEN #FStar.Tactics.Typeclasses.solve ()
          <:
          t_Array u8 (sz 11))
        <:
        Core.Option.t_Option (t_Array u8 (sz 11)))
  with
  | Core.Result.Result_Ok hoist43 ->
    verify_internal #v_SIMDUnit #v_Shake128X4 #v_Shake256 v_ROWS_IN_A v_COLUMNS_IN_A
      v_SIGNATURE_SIZE v_VERIFICATION_KEY_SIZE v_GAMMA1_EXPONENT v_GAMMA1_RING_ELEMENT_SIZE v_GAMMA2
      v_BETA v_COMMITMENT_RING_ELEMENT_SIZE v_COMMITMENT_VECTOR_SIZE v_COMMITMENT_HASH_SIZE
      v_ONES_IN_VERIFIER_CHALLENGE v_MAX_ONES_IN_HINT verification_key_serialized
      (pre_hashed_message <: t_Slice u8)
      (Core.Option.Option_Some hoist43 <: Core.Option.t_Option t_DomainSeparationContext)
      signature_serialized
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err (Core.Convert.f_from #FStar.Tactics.Typeclasses.solve err)
    <:
    Core.Result.t_Result Prims.unit t_VerificationError

/// Generate a key pair.
let generate_key_pair
      (#v_SIMDUnit #v_Shake128X4 #v_Shake256 #v_Shake256X4: Type0)
      (v_ROWS_IN_A v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE v_VERIFICATION_KEY_SIZE:
          usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128X4)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i6:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i7:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (randomness: t_Array u8 (sz 32))
    : (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE) =
  let seed_expanded:t_Array u8 (sz 128) = Rust_primitives.Hax.repeat 0uy (sz 128) in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_new #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Absorb =
    Libcrux_sha3.Portable.Incremental.f_absorb #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      (randomness <: t_Slice u8)
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze =
    Libcrux_sha3.Portable.Incremental.f_absorb_final #Libcrux_sha3.Portable.Incremental.t_Shake256Absorb
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      ((let list = [cast (v_ROWS_IN_A <: usize) <: u8; cast (v_COLUMNS_IN_A <: usize) <: u8] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
  in
  let tmp0, tmp1:(Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze & t_Array u8 (sz 128)) =
    Libcrux_sha3.Portable.Incremental.f_squeeze #Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze
      #(sz 136)
      #FStar.Tactics.Typeclasses.solve
      shake
      seed_expanded
  in
  let shake:Libcrux_sha3.Portable.Incremental.t_Shake256Squeeze = tmp0 in
  let seed_expanded:t_Array u8 (sz 128) = tmp1 in
  let _:Prims.unit = () in
  let seed_for_a, seed_expanded:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      (seed_expanded <: t_Slice u8)
      Libcrux_ml_dsa.Constants.v_SEED_FOR_A_SIZE
  in
  let seed_for_error_vectors, seed_for_signing:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8
      seed_expanded
      Libcrux_ml_dsa.Constants.v_SEED_FOR_ERROR_VECTORS_SIZE
  in
  let a_as_ntt:t_Array
    (t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A)
    v_ROWS_IN_A =
    Libcrux_ml_dsa.Samplex4.matrix_A #v_SIMDUnit
      #v_Shake128X4
      v_ROWS_IN_A
      v_COLUMNS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 34) seed_for_a <: t_Array u8 (sz 34))
  in
  let s1, s2:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_COLUMNS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Samplex4.sample_s1_and_s2 #v_SIMDUnit
      #v_Shake256X4
      v_ETA
      v_COLUMNS_IN_A
      v_ROWS_IN_A
      (Libcrux_ml_dsa.Utils.into_padded_array (sz 66) seed_for_error_vectors <: t_Array u8 (sz 66))
  in
  let t:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A =
    Libcrux_ml_dsa.Matrix.compute_As1_plus_s2 #v_SIMDUnit v_ROWS_IN_A v_COLUMNS_IN_A a_as_ntt s1 s2
  in
  let t0, t1:(t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_ROWS_IN_A) =
    Libcrux_ml_dsa.Arithmetic.power2round_vector #v_SIMDUnit v_ROWS_IN_A t
  in
  let verification_key_serialized:t_Array u8 v_VERIFICATION_KEY_SIZE =
    Libcrux_ml_dsa.Encoding.Verification_key.generate_serialized #v_SIMDUnit
      v_ROWS_IN_A
      v_VERIFICATION_KEY_SIZE
      seed_for_a
      t1
  in
  let signing_key_serialized:t_Array u8 v_SIGNING_KEY_SIZE =
    Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized #v_SIMDUnit #v_Shake256 v_ROWS_IN_A
      v_COLUMNS_IN_A v_ETA v_ERROR_RING_ELEMENT_SIZE v_SIGNING_KEY_SIZE seed_for_a seed_for_signing
      (verification_key_serialized <: t_Slice u8) s1 s2 t0
  in
  signing_key_serialized, verification_key_serialized
  <:
  (t_Array u8 v_SIGNING_KEY_SIZE & t_Array u8 v_VERIFICATION_KEY_SIZE)
