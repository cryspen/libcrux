module Libcrux_sha3.Generic_keccak.Xof
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_sha3.Traits in
  ()

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
type t_KeccakXofState
  (v_PARALLEL_LANES: usize) (v_RATE: usize) (v_STATE: Type0)
  {| i0: Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES |}
  = {
  f_inner:Libcrux_sha3.Generic_keccak.t_KeccakState v_PARALLEL_LANES v_STATE;
  f_buf:t_Array (t_Array u8 v_RATE) v_PARALLEL_LANES;
  f_buf_len:usize;
  f_sponge:bool
}

/// An all zero block
let impl_1__zero_block
      (v_PARALLEL_LANES: usize)
      (v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (_: Prims.unit)
    : t_Array u8 v_RATE = Rust_primitives.Hax.repeat (mk_u8 0) v_RATE

/// Generate a new keccak xof state.
let impl_1__new
      (v_PARALLEL_LANES: usize)
      (v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (_: Prims.unit)
    : t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
  {
    f_inner = Libcrux_sha3.Generic_keccak.impl_2__new v_PARALLEL_LANES #v_STATE ();
    f_buf
    =
    Rust_primitives.Hax.repeat (impl_1__zero_block v_PARALLEL_LANES v_RATE #v_STATE ()
        <:
        t_Array u8 v_RATE)
      v_PARALLEL_LANES;
    f_buf_len = mk_usize 0;
    f_sponge = false
  }
  <:
  t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE

/// Consume the internal buffer and the required amount of the input to pad to
/// `RATE`.
/// Returns the `consumed` bytes from `inputs` if there\'s enough buffered
/// content to consume, and `0` otherwise.
/// If `consumed > 0` is returned, `self.buf` contains a full block to be
/// loaded.
let impl_1__fill_buffer
      (v_PARALLEL_LANES v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (self: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      (inputs: t_Array (t_Slice u8) v_PARALLEL_LANES)
    : Prims.Pure (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)
      (requires
        v_PARALLEL_LANES =. mk_usize 1 && self.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (Core.Slice.impl__len #u8
                  (inputs.[ mk_usize 0 ] <: t_Slice u8)
                <:
                usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let self_e_future, result:(t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize) =
            temp_0_
          in
          result =. mk_usize 0 && self_e_future.f_buf_len =. self.f_buf_len ||
          result >. mk_usize 0 && self_e_future.f_buf_len =. v_RATE &&
          result =. (v_RATE -! self.f_buf_len <: usize)) =
  let input_len:usize = Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ] <: t_Slice u8) in
  let self, hax_temp_output:(t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize) =
    if self.f_buf_len >. mk_usize 0 && (self.f_buf_len +! input_len <: usize) >=. v_RATE
    then
      let consumed:usize = v_RATE -! self.f_buf_len in
      let start:usize = self.f_buf_len in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          v_PARALLEL_LANES
          (fun self temp_1_ ->
              let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
              let _:usize = temp_1_ in
              self.f_buf_len =. start <: bool)
          self
          (fun self i ->
              let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
              let i:usize = i in
              let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
                {
                  self with
                  f_buf
                  =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_buf
                    i
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from (self.f_buf.[ i
                          ]
                          <:
                          t_Array u8 v_RATE)
                        ({ Core.Ops.Range.f_start = self.f_buf_len }
                          <:
                          Core.Ops.Range.t_RangeFrom usize)
                        (Core.Slice.impl__copy_from_slice #u8
                            ((self.f_buf.[ i ] <: t_Array u8 v_RATE).[ {
                                  Core.Ops.Range.f_start = self.f_buf_len
                                }
                                <:
                                Core.Ops.Range.t_RangeFrom usize ]
                              <:
                              t_Slice u8)
                            ((inputs.[ i ] <: t_Slice u8).[ { Core.Ops.Range.f_end = consumed }
                                <:
                                Core.Ops.Range.t_RangeTo usize ]
                              <:
                              t_Slice u8)
                          <:
                          t_Slice u8)
                      <:
                      t_Array u8 v_RATE)
                }
                <:
                t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
              in
              self)
      in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        { self with f_buf_len = v_RATE } <: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
      in
      self, consumed <: (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)
    else self, mk_usize 0 <: (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)
  in
  self, hax_temp_output <: (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)
  
#push-options "--split_queries always --query_stats --z3rlimit 300"

let impl_1__absorb_full
      (v_PARALLEL_LANES v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.t_Absorb
            (Libcrux_sha3.Generic_keccak.t_KeccakState v_PARALLEL_LANES v_STATE) v_PARALLEL_LANES)
      (self: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      (inputs: t_Array (t_Slice u8) v_PARALLEL_LANES)
    : Prims.Pure (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)
      (requires
        v_PARALLEL_LANES =. mk_usize 1 && v_RATE <. mk_usize 192 &&
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        self.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (Core.Slice.impl__len #u8
                  (inputs.[ mk_usize 0 ] <: t_Slice u8)
                <:
                usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if false
    then
      let _:Prims.unit = Hax_lib.v_assert (v_PARALLEL_LANES >. mk_usize 0 <: bool) in
      ()
  in
  let _:Prims.unit =
    if false
    then
      let _:Prims.unit = Hax_lib.v_assert (self.f_buf_len <. v_RATE <: bool) in
      ()
  in
  let tmp0, out:(t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize) =
    impl_1__fill_buffer v_PARALLEL_LANES v_RATE #v_STATE self inputs
  in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = tmp0 in
  let input_consumed:usize = out in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    if input_consumed >. mk_usize 0
    then
      let (borrowed: t_Array (t_Slice u8) v_PARALLEL_LANES):t_Array (t_Slice u8) v_PARALLEL_LANES =
        Core.Array.from_fn #(t_Slice u8)
          v_PARALLEL_LANES
          (fun i ->
              let i:usize = i in
              Core.Array.impl_23__as_slice #u8 v_RATE (self.f_buf.[ i ] <: t_Array u8 v_RATE)
              <:
              t_Slice u8)
      in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        {
          self with
          f_inner
          =
          Libcrux_sha3.Traits.f_load_block #(Libcrux_sha3.Generic_keccak.t_KeccakState
                v_PARALLEL_LANES v_STATE)
            #v_PARALLEL_LANES
            #FStar.Tactics.Typeclasses.solve
            v_RATE
            self.f_inner
            borrowed
            (mk_usize 0)
        }
        <:
        t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
      in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        {
          self with
          f_inner
          =
          Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_PARALLEL_LANES #v_STATE self.f_inner
        }
        <:
        t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
      in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        { self with f_buf_len = mk_usize 0 } <: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
      in
      self
    else self
  in
  let input_to_consume:usize =
    (Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ] <: t_Slice u8) <: usize) -! input_consumed
  in
  let buf_len:usize = self.f_buf_len in
  let num_blocks:usize = input_to_consume /! v_RATE in
  let remainder:usize = input_to_consume %! v_RATE in
  let v_end:usize = input_consumed +! (num_blocks *! v_RATE <: usize) in
  
  let lemma_input_rate_bounds (i: usize) 
    : Lemma
        (requires i <. num_blocks)
        (ensures v input_consumed + v i * v v_RATE + v v_RATE <= v (Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ])))
        // (ensures input_consumed +! i *! v_RATE +! v_RATE <=. Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ]))
  =
    // Nat-level recursive lemma: for i < n, prove a + i*rate + rate <= a + n*rate
    let rec lemma_monotonic_offset_bound_nat (a: nat) (i: nat) (n: nat) (rate: nat)
      : Lemma
          (requires i < n /\ rate > 0)
          (ensures a + i * rate + rate <= a + n * rate)
          (decreases n)
      =
        if n = 0 then
          // Base case: unreachable
          ()
        else if i = n - 1 then
          // Direct case: a + (n-1)*rate + rate = a + n*rate
          ()
        else
          // Recursive case: i < n-1, so apply inductive hypothesis
          lemma_monotonic_offset_bound_nat a i (n - 1) rate
    in
    
    // Machine-level wrapper
    // let lemma_monotonic_offset_bound_usize (a: usize) (i: usize) (n: usize) (rate: usize)
    //   : Lemma
    //       (requires 
    //         i <. n /\ rate >. mk_usize 0 /\
    //         v a + v n * v rate <= v Core.Num.impl_usize__MAX)   // Prevent overflow in right side
    //       (ensures a +! i *! rate +! rate <=. a +! n *! rate)
    //   =
    //     lemma_monotonic_offset_bound_nat (v a) (v i) (v n) (v rate);
    //     ()
    // in

    // Total bound lemma: proves input_consumed + num_blocks*RATE <= len(inputs[0])
    // This uses the fact that num_blocks = input_to_consume / v_RATE
    // and input_to_consume = len(inputs[0]) - input_consumed
    let lemma_total_bound ()
      : Lemma
          (ensures v input_consumed + v num_blocks * v v_RATE <= v (Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ])))
      = 
        ()
    in

    // Chain both bounds to establish the final result:
    lemma_monotonic_offset_bound_nat (v input_consumed) (v i) (v num_blocks) (v v_RATE);
    lemma_total_bound ();
    ()
  in
  
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      num_blocks
      (fun self temp_1_ ->
          let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
          let _:usize = temp_1_ in
          true)
      self
      (fun self i ->
          let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
          let i:usize = i in
          lemma_input_rate_bounds i;
          let start:usize = (i *! v_RATE <: usize) +! input_consumed in
          assert (start +! v_RATE <=. (Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ])));
          // let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
          //   {
          //     self with
          //     f_inner
          //     =
          //     Libcrux_sha3.Traits.f_load_block #(Libcrux_sha3.Generic_keccak.t_KeccakState
          //           v_PARALLEL_LANES v_STATE)
          //       #v_PARALLEL_LANES
          //       #FStar.Tactics.Typeclasses.solve
          //       v_RATE
          //       self.f_inner
          //       inputs
          //       start
          //   }
          //   <:
          //   t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
          // in
          let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
            {
              self with
              f_inner
              =
              Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_PARALLEL_LANES #v_STATE self.f_inner
            }
            <:
            t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
          in
          self)
  in
  let hax_temp_output:usize = remainder in
  self, hax_temp_output <: (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize)

/// Absorb
/// This function takes any number of bytes to absorb and buffers if it\'s not enough.
/// The function assumes that all input slices in `inputs` have the same length.
/// Only a multiple of `RATE` blocks are absorbed.
/// For the remaining bytes [`absorb_final`] needs to be called.
/// This works best with relatively small `inputs`.
let impl_1__absorb
      (v_PARALLEL_LANES v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.t_Absorb
            (Libcrux_sha3.Generic_keccak.t_KeccakState v_PARALLEL_LANES v_STATE) v_PARALLEL_LANES)
      (self: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      (inputs: t_Array (t_Slice u8) v_PARALLEL_LANES)
    : Prims.Pure (t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      (requires
        v_PARALLEL_LANES =. mk_usize 1 && v_RATE <>. mk_usize 0 && v_RATE <. mk_usize 192 &&
        self.f_buf_len <=. v_RATE &&
        self.f_buf_len <=.
        (Core.Num.impl_usize__MAX -!
          (Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ] <: t_Slice u8) <: usize)
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let tmp0, out:(t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE & usize) =
    impl_1__absorb_full v_PARALLEL_LANES v_RATE #v_STATE self inputs
  in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = tmp0 in
  let input_remainder_len:usize = out in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    if input_remainder_len >. mk_usize 0
    then
      let _:Prims.unit =
        if false
        then
          let _:Prims.unit =
            Hax_lib.v_assert ((self.f_buf_len =. mk_usize 0 <: bool) ||
                ((self.f_buf_len +! input_remainder_len <: usize) <=. v_RATE <: bool))
          in
          ()
      in
      let input_len:usize = Core.Slice.impl__len #u8 (inputs.[ mk_usize 0 ] <: t_Slice u8) in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          v_PARALLEL_LANES
          (fun self temp_1_ ->
              let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
              let _:usize = temp_1_ in
              true)
          self
          (fun self i ->
              let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE = self in
              let i:usize = i in
              {
                self with
                f_buf
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_buf
                  i
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (self.f_buf.[ i ]
                        <:
                        t_Array u8 v_RATE)
                      ({
                          Core.Ops.Range.f_start = self.f_buf_len;
                          Core.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                      (Core.Slice.impl__copy_from_slice #u8
                          ((self.f_buf.[ i ] <: t_Array u8 v_RATE).[ {
                                Core.Ops.Range.f_start = self.f_buf_len;
                                Core.Ops.Range.f_end
                                =
                                self.f_buf_len +! input_remainder_len <: usize
                              }
                              <:
                              Core.Ops.Range.t_Range usize ]
                            <:
                            t_Slice u8)
                          ((inputs.[ i ] <: t_Slice u8).[ {
                                Core.Ops.Range.f_start = input_len -! input_remainder_len <: usize
                              }
                              <:
                              Core.Ops.Range.t_RangeFrom usize ]
                            <:
                            t_Slice u8)
                        <:
                        t_Slice u8)
                    <:
                    t_Array u8 v_RATE)
                <:
                t_Array (t_Array u8 v_RATE) v_PARALLEL_LANES
              }
              <:
              t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      in
      let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
        { self with f_buf_len = self.f_buf_len +! input_remainder_len }
        <:
        t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
      in
      self
    else self
  in
  self

/// Absorb a final block.
/// The `inputs` block may be empty. Everything in the `inputs` block beyond
/// `RATE` bytes is ignored.
let impl_1__absorb_final
      (v_PARALLEL_LANES v_RATE: usize)
      (#v_STATE: Type0)
      (v_DELIMITER: u8)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE v_PARALLEL_LANES)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.t_Absorb
            (Libcrux_sha3.Generic_keccak.t_KeccakState v_PARALLEL_LANES v_STATE) v_PARALLEL_LANES)
      (self: t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE)
      (inputs: t_Array (t_Slice u8) v_PARALLEL_LANES)
    : t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    impl_1__absorb v_PARALLEL_LANES v_RATE #v_STATE self inputs
  in
  let borrowed:t_Array (t_Slice u8) v_PARALLEL_LANES =
    Rust_primitives.Hax.repeat (Core.Array.impl_23__as_slice #u8
          v_RATE
          (Rust_primitives.Hax.repeat (mk_u8 0) v_RATE <: t_Array u8 v_RATE)
        <:
        t_Slice u8)
      v_PARALLEL_LANES
  in
  let borrowed:t_Array (t_Slice u8) v_PARALLEL_LANES =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_PARALLEL_LANES
      (fun borrowed temp_1_ ->
          let borrowed:t_Array (t_Slice u8) v_PARALLEL_LANES = borrowed in
          let _:usize = temp_1_ in
          true)
      borrowed
      (fun borrowed i ->
          let borrowed:t_Array (t_Slice u8) v_PARALLEL_LANES = borrowed in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize borrowed
            i
            (self.f_buf.[ i ] <: t_Slice u8)
          <:
          t_Array (t_Slice u8) v_PARALLEL_LANES)
  in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    {
      self with
      f_inner
      =
      Libcrux_sha3.Traits.f_load_last #(Libcrux_sha3.Generic_keccak.t_KeccakState v_PARALLEL_LANES
            v_STATE)
        #v_PARALLEL_LANES
        #FStar.Tactics.Typeclasses.solve
        v_RATE
        v_DELIMITER
        self.f_inner
        borrowed
        (mk_usize 0)
        self.f_buf_len
    }
    <:
    t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
  in
  let self:t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE =
    {
      self with
      f_inner
      =
      Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 v_PARALLEL_LANES #v_STATE self.f_inner
    }
    <:
    t_KeccakXofState v_PARALLEL_LANES v_RATE v_STATE
  in
  self

/// Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
let impl__squeeze
      (v_RATE: usize)
      (#v_STATE: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_sha3.Traits.t_KeccakItem v_STATE (mk_usize 1))
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_sha3.Traits.t_Squeeze
            (Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1) v_STATE) v_STATE)
      (self: t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
      (out: t_Slice u8)
    : (t_KeccakXofState (mk_usize 1) v_RATE v_STATE & t_Slice u8) =
  let self:t_KeccakXofState (mk_usize 1) v_RATE v_STATE =
    if self.f_sponge
    then
      let self:t_KeccakXofState (mk_usize 1) v_RATE v_STATE =
        {
          self with
          f_inner
          =
          Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #v_STATE self.f_inner
        }
        <:
        t_KeccakXofState (mk_usize 1) v_RATE v_STATE
      in
      self
    else self
  in
  let out_len:usize = Core.Slice.impl__len #u8 out in
  let out, self:(t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE) =
    if out_len >. mk_usize 0
    then
      let out, self:(t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE) =
        if out_len <=. v_RATE
        then
          let out:t_Slice u8 =
            Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1)
                  v_STATE)
              #v_STATE
              #FStar.Tactics.Typeclasses.solve
              v_RATE
              self.f_inner
              out
              (mk_usize 0)
              out_len
          in
          out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
        else
          let blocks:usize = out_len /! v_RATE in
          let out, self:(t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE) =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              blocks
              (fun temp_0_ temp_1_ ->
                  let out, self:(t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE) =
                    temp_0_
                  in
                  let _:usize = temp_1_ in
                  true)
              (out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE))
              (fun temp_0_ i ->
                  let out, self:(t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE) =
                    temp_0_
                  in
                  let i:usize = i in
                  let self:t_KeccakXofState (mk_usize 1) v_RATE v_STATE =
                    {
                      self with
                      f_inner
                      =
                      Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1)
                        #v_STATE
                        self.f_inner
                    }
                    <:
                    t_KeccakXofState (mk_usize 1) v_RATE v_STATE
                  in
                  let out:t_Slice u8 =
                    Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState
                          (mk_usize 1) v_STATE)
                      #v_STATE
                      #FStar.Tactics.Typeclasses.solve
                      v_RATE
                      self.f_inner
                      out
                      (i *! v_RATE <: usize)
                      v_RATE
                  in
                  out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE))
          in
          let remaining:usize = out_len %! v_RATE in
          if remaining >. mk_usize 0
          then
            let self:t_KeccakXofState (mk_usize 1) v_RATE v_STATE =
              {
                self with
                f_inner
                =
                Libcrux_sha3.Generic_keccak.impl_2__keccakf1600 (mk_usize 1) #v_STATE self.f_inner
              }
              <:
              t_KeccakXofState (mk_usize 1) v_RATE v_STATE
            in
            let out:t_Slice u8 =
              Libcrux_sha3.Traits.f_squeeze #(Libcrux_sha3.Generic_keccak.t_KeccakState (mk_usize 1)
                    v_STATE)
                #v_STATE
                #FStar.Tactics.Typeclasses.solve
                v_RATE
                self.f_inner
                out
                (blocks *! v_RATE <: usize)
                remaining
            in
            out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
          else out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
      in
      let self:t_KeccakXofState (mk_usize 1) v_RATE v_STATE =
        { self with f_sponge = true } <: t_KeccakXofState (mk_usize 1) v_RATE v_STATE
      in
      out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
    else out, self <: (t_Slice u8 & t_KeccakXofState (mk_usize 1) v_RATE v_STATE)
  in
  self, out <: (t_KeccakXofState (mk_usize 1) v_RATE v_STATE & t_Slice u8)
