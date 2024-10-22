module Libcrux_ml_dsa.Simd.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY486617197 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY671965844 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY879052313 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY359502844 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY91690999 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY782304655 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY344990702 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY410925233 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {v_DUMMY997570341 as v_DUMMY}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {invert_ntt_at_layer_0_ as invert_ntt_at_layer_0_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {invert_ntt_at_layer_1_ as invert_ntt_at_layer_1_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {invert_ntt_at_layer_2_ as invert_ntt_at_layer_2_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {simd_unit_ntt_at_layer_0_ as simd_unit_ntt_at_layer_0_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {simd_unit_ntt_at_layer_1_ as simd_unit_ntt_at_layer_1_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {simd_unit_ntt_at_layer_2_ as simd_unit_ntt_at_layer_2_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {ntt_at_layer_0_ as ntt_at_layer_0_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {ntt_at_layer_1_ as ntt_at_layer_1_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {ntt_at_layer_2_ as ntt_at_layer_2_}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {ntt as ntt}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_437004224 {ntt_at_layer_3_plus as ntt_at_layer_3_plus}
