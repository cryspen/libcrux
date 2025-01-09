module Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Neon in
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Pre_hash in
  let open Libcrux_ml_dsa.Samplex4 in
  let open Libcrux_ml_dsa.Samplex4.Neon in
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_key_pair
      (randomness: t_Array u8 (sz 32))
      (signing_key: t_Array u8 (sz 2560))
      (verification_key: t_Array u8 (sz 1312))
     =
  let tmp0, tmp1:(t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) =
    Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.generate_key_pair #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4
      randomness
      signing_key
      verification_key
  in
  let signing_key:t_Array u8 (sz 2560) = tmp0 in
  let verification_key:t_Array u8 (sz 1312) = tmp1 in
  let hax_temp_output:Prims.unit = () in
  signing_key, verification_key <: (t_Array u8 (sz 2560) & t_Array u8 (sz 1312))

let sign
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.sign #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
    #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4 (signing_key <: t_Slice u8) message context
    randomness

let sign_mut
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
      (signature: t_Array u8 (sz 2420))
     =
  let tmp0, out:(t_Array u8 (sz 2420) &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.sign_mut #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4 (signing_key <: t_Slice u8) message context
      randomness signature
  in
  let signature:t_Array u8 (sz 2420) = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError = out in
  signature, hax_temp_output
  <:
  (t_Array u8 (sz 2420) & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_SigningError)

let sign_pre_hashed_shake128
      (signing_key: t_Array u8 (sz 2560))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  let tmp0, out:(t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
      Libcrux_ml_dsa.Types.t_SigningError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.sign_pre_hashed #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake256x4 #Libcrux_ml_dsa.Pre_hash.t_SHAKE128_PH
      (signing_key <: t_Slice u8) message context pre_hash_buffer randomness
  in
  let pre_hash_buffer:t_Slice u8 = tmp0 in
  let hax_temp_output:Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
    Libcrux_ml_dsa.Types.t_SigningError =
    out
  in
  pre_hash_buffer, hax_temp_output
  <:
  (t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
      Libcrux_ml_dsa.Types.t_SigningError)

let verify
      (verification_key: t_Array u8 (sz 1312))
      (message context: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
     =
  Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.verify #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
    #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler
    #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
    #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof
    verification_key
    message
    context
    signature

let verify_pre_hashed_shake128
      (verification_key: t_Array u8 (sz 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature: t_Array u8 (sz 2420))
     =
  let tmp0, out:(t_Slice u8 &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.verify_pre_hashed #Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      #Libcrux_ml_dsa.Samplex4.Neon.t_NeonSampler #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128
      #Libcrux_ml_dsa.Hash_functions.Neon.t_Shake128x4
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256
      #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake256Xof #Libcrux_ml_dsa.Pre_hash.t_SHAKE128_PH
      verification_key message context pre_hash_buffer signature
  in
  let pre_hash_buffer:t_Slice u8 = tmp0 in
  let hax_temp_output:Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError =
    out
  in
  pre_hash_buffer, hax_temp_output
  <:
  (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
