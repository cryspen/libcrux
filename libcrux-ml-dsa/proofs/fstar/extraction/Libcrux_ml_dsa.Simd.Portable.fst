module Libcrux_ml_dsa.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {t_PortableSIMDUnit as t_PortableSIMDUnit}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {f_coefficients as f_coefficients}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {arithmetic as arithmetic}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {encoding as encoding}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {ntt as ntt}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {sample as sample}

include Libcrux_ml_dsa.Simd.Portable.Rec_bundle_8182905 {impl as impl}
