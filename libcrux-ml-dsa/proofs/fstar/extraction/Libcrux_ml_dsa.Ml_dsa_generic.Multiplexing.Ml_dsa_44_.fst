module Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let generate_key_pair
      (randomness: t_Array u8 (sz 32))
      (signing_key: t_Array u8 (sz 2560))
      (verification_key: t_Array u8 (sz 1312))
     =
  let (signing_key, verification_key), hax_temp_output:((t_Array u8 (sz 2560) & t_Array u8 (sz 1312)
    ) &
    Prims.unit) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, tmp1:(t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.generate_key_pair randomness
          signing_key
          verification_key
      in
      let signing_key:t_Array u8 (sz 2560) = tmp0 in
      let verification_key:t_Array u8 (sz 1312) = tmp1 in
      let _:Prims.unit = () in
      (signing_key, verification_key <: (t_Array u8 (sz 2560) & t_Array u8 (sz 1312))), ()
      <:
      ((t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) & Prims.unit)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, tmp1:(t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.generate_key_pair randomness
            signing_key
            verification_key
        in
        let signing_key:t_Array u8 (sz 2560) = tmp0 in
        let verification_key:t_Array u8 (sz 1312) = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Array u8 (sz 2560) & t_Array u8 (sz 1312))), ()
        <:
        ((t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) & Prims.unit)
      else
        let tmp0, tmp1:(t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.generate_key_pair randomness
            signing_key
            verification_key
        in
        let signing_key:t_Array u8 (sz 2560) = tmp0 in
        let verification_key:t_Array u8 (sz 1312) = tmp1 in
        let _:Prims.unit = () in
        (signing_key, verification_key <: (t_Array u8 (sz 2560) & t_Array u8 (sz 1312))), ()
        <:
        ((t_Array u8 (sz 2560) & t_Array u8 (sz 1312)) & Prims.unit)
  in
  signing_key, verification_key <: (t_Array u8 (sz 2560) & t_Array u8 (sz 1312))

let sign
      (signing_key: t_Array u8 (sz 2560))
      (message context: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.sign signing_key
      message
      context
      randomness
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.sign signing_key
        message
        context
        randomness
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.sign signing_key
        message
        context
        randomness

let sign_pre_hashed_shake128
      (signing_key: t_Array u8 (sz 2560))
      (message context pre_hash_buffer: t_Slice u8)
      (randomness: t_Array u8 (sz 32))
     =
  let pre_hash_buffer, hax_temp_output:(t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
      Libcrux_ml_dsa.Types.t_SigningError) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, out:(t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.sign_pre_hashed_shake128 signing_key
          message
          context
          pre_hash_buffer
          randomness
      in
      let pre_hash_buffer:t_Slice u8 = tmp0 in
      pre_hash_buffer, out
      <:
      (t_Slice u8 &
        Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
          Libcrux_ml_dsa.Types.t_SigningError)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
            Libcrux_ml_dsa.Types.t_SigningError) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.sign_pre_hashed_shake128 signing_key
            message
            context
            pre_hash_buffer
            randomness
        in
        let pre_hash_buffer:t_Slice u8 = tmp0 in
        pre_hash_buffer, out
        <:
        (t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
            Libcrux_ml_dsa.Types.t_SigningError)
      else
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
            Libcrux_ml_dsa.Types.t_SigningError) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.sign_pre_hashed_shake128 signing_key
            message
            context
            pre_hash_buffer
            randomness
        in
        let pre_hash_buffer:t_Slice u8 = tmp0 in
        pre_hash_buffer, out
        <:
        (t_Slice u8 &
          Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
            Libcrux_ml_dsa.Types.t_SigningError)
  in
  pre_hash_buffer, hax_temp_output
  <:
  (t_Slice u8 &
    Core.Result.t_Result (Libcrux_ml_dsa.Types.t_MLDSASignature (sz 2420))
      Libcrux_ml_dsa.Types.t_SigningError)

let verify
      (verification_key_serialized: t_Array u8 (sz 1312))
      (message context: t_Slice u8)
      (signature_serialized: t_Array u8 (sz 2420))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.verify verification_key_serialized
      message
      context
      signature_serialized
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.verify verification_key_serialized
        message
        context
        signature_serialized
    else
      Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.verify verification_key_serialized
        message
        context
        signature_serialized

let verify_pre_hashed_shake128
      (verification_key_serialized: t_Array u8 (sz 1312))
      (message context pre_hash_buffer: t_Slice u8)
      (signature_serialized: t_Array u8 (sz 2420))
     =
  let pre_hash_buffer, hax_temp_output:(t_Slice u8 &
    Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
    if Libcrux_platform.Platform.simd256_support ()
    then
      let tmp0, out:(t_Slice u8 &
        Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
        Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.verify_pre_hashed_shake128 verification_key_serialized
          message
          context
          pre_hash_buffer
          signature_serialized
      in
      let pre_hash_buffer:t_Slice u8 = tmp0 in
      pre_hash_buffer, out
      <:
      (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
    else
      if Libcrux_platform.Platform.simd128_support ()
      then
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.verify_pre_hashed_shake128 verification_key_serialized
            message
            context
            pre_hash_buffer
            signature_serialized
        in
        let pre_hash_buffer:t_Slice u8 = tmp0 in
        pre_hash_buffer, out
        <:
        (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
      else
        let tmp0, out:(t_Slice u8 &
          Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError) =
          Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.verify_pre_hashed_shake128
            verification_key_serialized
            message
            context
            pre_hash_buffer
            signature_serialized
        in
        let pre_hash_buffer:t_Slice u8 = tmp0 in
        pre_hash_buffer, out
        <:
        (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
  in
  pre_hash_buffer, hax_temp_output
  <:
  (t_Slice u8 & Core.Result.t_Result Prims.unit Libcrux_ml_dsa.Types.t_VerificationError)
