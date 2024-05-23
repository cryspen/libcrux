module Libcrux_ml_kem.Types.Index_impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) (index: usize) -> true);
    f_index_post
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) (index: usize) (out: u8) -> true);
    f_index
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) (index: usize) ->
      self.Libcrux_ml_kem.Types.f_value.[ index ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) usize =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) (range: usize) -> true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE) (range: usize) ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut int = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (core::ops::index::Index::index(\n                        proj_libcrux_ml_kem::types::f_value(self),\n                        range,\n                    )),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_Range<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeTo<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemCiphertext v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeFrom<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) (index: usize) -> true);
    f_index_post
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) (index: usize) (out: u8) -> true);
    f_index
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) (index: usize) ->
      self.Libcrux_ml_kem.Types.f_value.[ index ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) usize =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) (range: usize) -> true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE) (range: usize) ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut int = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (core::ops::index::Index::index(\n                        proj_libcrux_ml_kem::types::f_value(self),\n                        range,\n                    )),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_Range<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeTo<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPrivateKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeFrom<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) usize =
  {
    f_Output = u8;
    f_index_pre = (fun (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) (index: usize) -> true);
    f_index_post
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) (index: usize) (out: u8) -> true);
    f_index
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) (index: usize) ->
      self.Libcrux_ml_kem.Types.f_value.[ index ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) usize =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) (range: usize) -> true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE) (range: usize) ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut int = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (core::ops::index::Index::index(\n                        proj_libcrux_ml_kem::types::f_value(self),\n                        range,\n                    )),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_Range usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_Range usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_Range usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_Range<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_RangeTo usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeTo usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeTo usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeTo<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22 (v_SIZE: usize)
    : Core.Ops.Index.t_Index (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice u8;
    f_index_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: t_Slice u8)
        ->
        true);
    f_index
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      self.Libcrux_ml_kem.Types.f_value.[ range ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23 (v_SIZE: usize)
    : Core.Ops.Index.t_IndexMut (Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (Core.Ops.Range.t_RangeFrom usize) =
  {
    _super_8588880431872084022 = FStar.Tactics.Typeclasses.solve;
    f_index_mut_pre
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        ->
        true);
    f_index_mut_post
    =
    (fun
        (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
        (range: Core.Ops.Range.t_RangeFrom usize)
        (out: Rust_primitives.Hax.t_failure)
        ->
        true);
    f_index_mut
    =
    fun
      (self: Libcrux_ml_kem.Types.t_MlKemPublicKey v_SIZE)
      (range: Core.Ops.Range.t_RangeFrom usize)
      ->
      Rust_primitives.Hax.failure ""
        "{\n        let hax_temp_output: &mut [int] = {\n            &mut (deref({\n                &mut (deref(\n                    &mut (deref(core::ops::index::f_index_mut::<\n                        [int; SIZE],\n                        core::ops::range::t_RangeFrom<int>,\n                    >(\n                        &mut (proj_libcrux_ml_kem::types::f_value(self)), range\n                    ))),\n                ))\n            }))\n        };\n        Tuple2(self, hax_temp_output)\n    }"

  }
