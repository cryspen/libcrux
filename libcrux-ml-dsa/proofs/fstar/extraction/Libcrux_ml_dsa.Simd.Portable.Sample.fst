module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_field_modulus_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_field_modulus_post randomness
            out_future
            r) =
  let sampled:usize = mk_usize 0 in
  let e_out_len:usize = Core.Slice.impl__len #i32 out in
  let _:Prims.unit =
    Spec.Utils.eq_repeati0 (sz 0)
      (Spec.MLDSA.Math.rejection_sample_field_modulus_inner randomness)
      Seq.empty
  in
  let out, sampled:(t_Slice i32 & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      ((Core.Slice.impl__len #u8 randomness <: usize) /! mk_usize 3 <: usize)
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          v sampled <= v i /\ Seq.length out == v e_out_len /\
          (let samples =
              Spec.Utils.repeati (i)
                (Spec.MLDSA.Math.rejection_sample_field_modulus_inner randomness)
                Seq.empty
            in
            v sampled == Seq.length samples /\ Seq.slice out 0 (Seq.length samples) == samples))
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          let b0:i32 = cast (randomness.[ i *! mk_usize 3 <: usize ] <: u8) <: i32 in
          let b1:i32 =
            cast (randomness.[ (i *! mk_usize 3 <: usize) +! mk_usize 1 <: usize ] <: u8) <: i32
          in
          let b2:i32 =
            cast (randomness.[ (i *! mk_usize 3 <: usize) +! mk_usize 2 <: usize ] <: u8) <: i32
          in
          let coefficient:i32 =
            (((b2 <<! mk_i32 16 <: i32) |. (b1 <<! mk_i32 8 <: i32) <: i32) |. b0 <: i32) &.
            mk_i32 8388607
          in
          let _:Prims.unit =
            Spec.MLDSA.Math.rejection_sample_coefficient_lemma randomness (i);
            Spec.Utils.unfold_repeati (i +! sz 1)
              (Spec.MLDSA.Math.rejection_sample_field_modulus_inner randomness)
              Seq.empty
              (i)
          in
          let out, sampled:(t_Slice i32 & usize) =
            if coefficient <. Libcrux_ml_dsa.Constants.v_FIELD_MODULUS
            then
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out sampled coefficient
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          let _:Prims.unit =
            let samples =
              Spec.Utils.repeati (i +! sz 1)
                (Spec.MLDSA.Math.rejection_sample_field_modulus_inner randomness)
                Seq.empty
            in
            eq_intro (Seq.slice out 0 (Seq.length samples)) samples
          in
          out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

#push-options "--z3rlimit 800 --ext context_pruning --z3refresh"

let rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_post randomness
            out_future
            r) =
  let sampled:usize = mk_usize 0 in
  let e_out_len:usize = Core.Slice.impl__len #i32 out in
  let _:Prims.unit =
    Spec.Utils.eq_repeati0 (sz 0)
      (Spec.MLDSA.Math.rejection_sample_eta_2_inner randomness)
      Seq.empty
  in
  let out, sampled:(t_Slice i32 & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #u8 randomness <: usize)
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          v i >= 0 /\ v i <= Seq.length randomness /\ v sampled <= v i * 2 /\
          Seq.length out == v e_out_len /\
          (let samples =
              Spec.Utils.repeati (i)
                (Spec.MLDSA.Math.rejection_sample_eta_2_inner randomness)
                Seq.empty
            in
            v sampled == Seq.length samples /\ Seq.slice out 0 (Seq.length samples) == samples))
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          let byte:u8 = randomness.[ i ] in
          let try_0_:u8 = byte &. mk_u8 15 in
          let try_1_:u8 = byte >>! mk_i32 4 in
          let _:Prims.unit =
            Spec.Utils.unfold_repeati (i +! sz 1)
              (Spec.MLDSA.Math.rejection_sample_eta_2_inner randomness)
              Seq.empty
              (i)
          in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. mk_u8 15
            then
              let try_0_:i32 = cast (try_0_ <: u8) <: i32 in
              let try_0_mod_5_:i32 =
                try_0_ -! (((try_0_ *! mk_i32 26 <: i32) >>! mk_i32 7 <: i32) *! mk_i32 5 <: i32)
              in
              let _:Prims.unit =
                assert (try_0_mod_5_ == (try_0_ %! mk_i32 5));
                assert ((mk_i32 2 -. try_0_mod_5_) == (mk_i32 2 -! try_0_mod_5_))
              in
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 2 -! try_0_mod_5_ <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          let out, sampled:(t_Slice i32 & usize) =
            if try_1_ <. mk_u8 15
            then
              let try_1_:i32 = cast (try_1_ <: u8) <: i32 in
              let try_1_mod_5_:i32 =
                try_1_ -! (((try_1_ *! mk_i32 26 <: i32) >>! mk_i32 7 <: i32) *! mk_i32 5 <: i32)
              in
              let _:Prims.unit =
                assert (try_1_mod_5_ == (try_1_ %! mk_i32 5));
                assert ((mk_i32 2 -. try_1_mod_5_) == (mk_i32 2 -! try_1_mod_5_))
              in
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 2 -! try_1_mod_5_ <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          let _:Prims.unit =
            let samples =
              Spec.Utils.repeati (i +! sz 1)
                (Spec.MLDSA.Math.rejection_sample_eta_2_inner randomness)
                Seq.empty
            in
            eq_intro (Seq.slice out 0 (Seq.length samples)) samples
          in
          out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

#pop-options

#push-options "--ext context_pruning --z3refresh"

let rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_post randomness
            out_future
            r) =
  let sampled:usize = mk_usize 0 in
  let e_out_len:usize = Core.Slice.impl__len #i32 out in
  let _:Prims.unit =
    Spec.Utils.eq_repeati0 (sz 0)
      (Spec.MLDSA.Math.rejection_sample_eta_4_inner randomness)
      Seq.empty
  in
  let out, sampled:(t_Slice i32 & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #u8 randomness <: usize)
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          v i >= 0 /\ v i <= Seq.length randomness /\ v sampled <= v i * 2 /\
          Seq.length out == v e_out_len /\
          (let samples =
              Spec.Utils.repeati (i)
                (Spec.MLDSA.Math.rejection_sample_eta_4_inner randomness)
                Seq.empty
            in
            v sampled == Seq.length samples /\ Seq.slice out 0 (Seq.length samples) == samples))
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ i ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let i:usize = i in
          let byte:u8 = randomness.[ i ] in
          let try_0_:u8 = byte &. mk_u8 15 in
          let try_1_:u8 = byte >>! mk_i32 4 in
          let _:Prims.unit =
            Spec.Utils.unfold_repeati (i +! sz 1)
              (Spec.MLDSA.Math.rejection_sample_eta_4_inner randomness)
              Seq.empty
              (i)
          in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. mk_u8 9
            then
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 4 -! (cast (try_0_ <: u8) <: i32) <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          let out, sampled:(t_Slice i32 & usize) =
            if try_1_ <. mk_u8 9
            then
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 4 -! (cast (try_1_ <: u8) <: i32) <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          let _:Prims.unit =
            let samples =
              Spec.Utils.repeati (i +! sz 1)
                (Spec.MLDSA.Math.rejection_sample_eta_4_inner randomness)
                Seq.empty
            in
            eq_intro (Seq.slice out 0 (Seq.length samples)) samples
          in
          out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

#pop-options
