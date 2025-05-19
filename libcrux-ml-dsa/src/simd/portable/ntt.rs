use hax_lib::loop_invariant;

use super::arithmetic::{self, montgomery_multiply_by_constant, montgomery_multiply_fe_by_fer};
use super::vector_type::Coefficients;
use crate::simd::traits::{COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT};



#[cfg(hax)]
const PRIME: u32 = 8380417;
#[cfg(hax)]
const MONT_R: u32 = 8380417;
#[cfg(hax)]
const FIELD_MAX: u32 = 8380416;
#[cfg(hax)]
const FIELD_MID: u32 = 4190208;
#[cfg(hax)]
const NTT_BASE_BOUND: u32 = FIELD_MID;

#[cfg(hax)]
#[hax_lib::requires(i < 256)]
#[hax_lib::ensures(|result| result >= 0 && result <= FIELD_MAX as i32)]
const fn zeta(i:usize) -> i32 {
    match i {
        0 => 0,
        1 => 4808194,
        2 => 3765607,
        3 => 3761513,
        4 => 5178923,
        5 => 5496691,
        6 => 5234739,
        7 => 5178987,
        8 => 7778734,
        9 => 3542485,
        10 => 2682288,
        11 => 2129892,
        12 => 3764867,
        13 => 7375178,
        14 => 557458,
        15 => 7159240,
        16 => 5010068,
        17 => 4317364,
        18 => 2663378,
        19 => 6705802,
        20 => 4855975,
        21 => 7946292,
        22 => 676590,
        23 => 7044481,
        24 => 5152541,
        25 => 1714295,
        26 => 2453983,
        27 => 1460718,
        28 => 7737789,
        29 => 4795319,
        30 => 2815639,
        31 => 2283733,
        32 => 3602218,
        33 => 3182878,
        34 => 2740543,
        35 => 4793971,
        36 => 5269599,
        37 => 2101410,
        38 => 3704823,
        39 => 1159875,
        40 => 394148,
        41 => 928749,
        42 => 1095468,
        43 => 4874037,
        44 => 2071829,
        45 => 4361428,
        46 => 3241972,
        47 => 2156050,
        48 => 3415069,
        49 => 1759347,
        50 => 7562881,
        51 => 4805951,
        52 => 3756790,
        53 => 6444618,
        54 => 6663429,
        55 => 4430364,
        56 => 5483103,
        57 => 3192354,
        58 => 556856,
        59 => 3870317,
        60 => 2917338,
        61 => 1853806,
        62 => 3345963,
        63 => 1858416,
        64 => 3073009,
        65 => 1277625,
        66 => 5744944,
        67 => 3852015,
        68 => 4183372,
        69 => 5157610,
        70 => 5258977,
        71 => 8106357,
        72 => 2508980,
        73 => 2028118,
        74 => 1937570,
        75 => 4564692,
        76 => 2811291,
        77 => 5396636,
        78 => 7270901,
        79 => 4158088,
        80 => 1528066,
        81 => 482649,
        82 => 1148858,
        83 => 5418153,
        84 => 7814814,
        85 => 169688,
        86 => 2462444,
        87 => 5046034,
        88 => 4213992,
        89 => 4892034,
        90 => 1987814,
        91 => 5183169,
        92 => 1736313,
        93 => 235407,
        94 => 5130263,
        95 => 3258457,
        96 => 5801164,
        97 => 1787943,
        98 => 5989328,
        99 => 6125690,
        100 => 3482206,
        101 => 4197502,
        102 => 7080401,
        103 => 6018354,
        104 => 7062739,
        105 => 2461387,
        106 => 3035980,
        107 => 621164,
        108 => 3901472,
        109 => 7153756,
        110 => 2925816,
        111 => 3374250,
        112 => 1356448,
        113 => 5604662,
        114 => 2683270,
        115 => 5601629,
        116 => 4912752,
        117 => 2312838,
        118 => 7727142,
        119 => 7921254,
        120 => 348812,
        121 => 8052569,
        122 => 1011223,
        123 => 6026202,
        124 => 4561790,
        125 => 6458164,
        126 => 6143691,
        127 => 1744507,
        128 => 1753,
        129 => 6444997,
        130 => 5720892,
        131 => 6924527,
        132 => 2660408,
        133 => 6600190,
        134 => 8321269,
        135 => 2772600,
        136 => 1182243,
        137 => 87208,
        138 => 636927,
        139 => 4415111,
        140 => 4423672,
        141 => 6084020,
        142 => 5095502,
        143 => 4663471,
        144 => 8352605,
        145 => 822541,
        146 => 1009365,
        147 => 5926272,
        148 => 6400920,
        149 => 1596822,
        150 => 4423473,
        151 => 4620952,
        152 => 6695264,
        153 => 4969849,
        154 => 2678278,
        155 => 4611469,
        156 => 4829411,
        157 => 635956,
        158 => 8129971,
        159 => 5925040,
        160 => 4234153,
        161 => 6607829,
        162 => 2192938,
        163 => 6653329,
        164 => 2387513,
        165 => 4768667,
        166 => 8111961,
        167 => 5199961,
        168 => 3747250,
        169 => 2296099,
        170 => 1239911,
        171 => 4541938,
        172 => 3195676,
        173 => 2642980,
        174 => 1254190,
        175 => 8368000,
        176 => 2998219,
        177 => 141835,
        178 => 8291116,
        179 => 2513018,
        180 => 7025525,
        181 => 613238,
        182 => 7070156,
        183 => 6161950,
        184 => 7921677,
        185 => 6458423,
        186 => 4040196,
        187 => 4908348,
        188 => 2039144,
        189 => 6500539,
        190 => 7561656,
        191 => 6201452,
        192 => 6757063,
        193 => 2105286,
        194 => 6006015,
        195 => 6346610,
        196 => 586241,
        197 => 7200804,
        198 => 527981,
        199 => 5637006,
        200 => 6903432,
        201 => 1994046,
        202 => 2491325,
        203 => 6987258,
        204 => 507927,
        205 => 7192532,
        206 => 7655613,
        207 => 6545891,
        208 => 5346675,
        209 => 8041997,
        210 => 2647994,
        211 => 3009748,
        212 => 5767564,
        213 => 4148469,
        214 => 749577,
        215 => 4357667,
        216 => 3980599,
        217 => 2569011,
        218 => 6764887,
        219 => 1723229,
        220 => 1665318,
        221 => 2028038,
        222 => 1163598,
        223 => 5011144,
        224 => 3994671,
        225 => 8368538,
        226 => 7009900,
        227 => 3020393,
        228 => 3363542,
        229 => 214880,
        230 => 545376,
        231 => 7609976,
        232 => 3105558,
        233 => 7277073,
        234 => 508145,
        235 => 7826699,
        236 => 860144,
        237 => 3430436,
        238 => 140244,
        239 => 6866265,
        240 => 6195333,
        241 => 3123762,
        242 => 2358373,
        243 => 6187330,
        244 => 5365997,
        245 => 6663603,
        246 => 2926054,
        247 => 7987710,
        248 => 8077412,
        249 => 3531229,
        250 => 4405932,
        251 => 4606686,
        252 => 1900052,
        253 => 7598542,
        254 => 1054478,
        255 => 7648983,
        _ => unreachable!()
    }
}

#[cfg(hax)]
#[hax_lib::requires(i < 256)]
#[hax_lib::ensures(|result| 
    fstar!(r#"
     Spec.Utils.is_i32b (v $FIELD_MID) $result /\
     v $result % (v $PRIME) ==
     (v (${zeta} i) * pow2 32) % (v $PRIME)"#))]
const fn zeta_r(i:usize) -> i32 {
    match i {
        0 => 0,
        1 => 25847,
        2 => -2608894,
        3 => -518909,
        4 => 237124,
        5 => -777960,
        6 => -876248,
        7 => 466468,
        8 => 1826347,
        9 => 2353451,
        10 => -359251,
        11 => -2091905,
        12 => 3119733,
        13 => -2884855,
        14 => 3111497,
        15 => 2680103,
        16 => 2725464,
        17 => 1024112,
        18 => -1079900,
        19 => 3585928,
        20 => -549488,
        21 => -1119584,
        22 => 2619752,
        23 => -2108549,
        24 => -2118186,
        25 => -3859737,
        26 => -1399561,
        27 => -3277672,
        28 => 1757237,
        29 => -19422,
        30 => 4010497,
        31 => 280005,
        32 => 2706023,
        33 => 95776,
        34 => 3077325,
        35 => 3530437,
        36 => -1661693,
        37 => -3592148,
        38 => -2537516,
        39 => 3915439,
        40 => -3861115,
        41 => -3043716,
        42 => 3574422,
        43 => -2867647,
        44 => 3539968,
        45 => -300467,
        46 => 2348700,
        47 => -539299,
        48 => -1699267,
        49 => -1643818,
        50 => 3505694,
        51 => -3821735,
        52 => 3507263,
        53 => -2140649,
        54 => -1600420,
        55 => 3699596,
        56 => 811944,
        57 => 531354,
        58 => 954230,
        59 => 3881043,
        60 => 3900724,
        61 => -2556880,
        62 => 2071892,
        63 => -2797779,
        64 => -3930395,
        65 => -1528703,
        66 => -3677745,
        67 => -3041255,
        68 => -1452451,
        69 => 3475950,
        70 => 2176455,
        71 => -1585221,
        72 => -1257611,
        73 => 1939314,
        74 => -4083598,
        75 => -1000202,
        76 => -3190144,
        77 => -3157330,
        78 => -3632928,
        79 => 126922,
        80 => 3412210,
        81 => -983419,
        82 => 2147896,
        83 => 2715295,
        84 => -2967645,
        85 => -3693493,
        86 => -411027,
        87 => -2477047,
        88 => -671102,
        89 => -1228525,
        90 => -22981,
        91 => -1308169,
        92 => -381987,
        93 => 1349076,
        94 => 1852771,
        95 => -1430430,
        96 => -3343383,
        97 => 264944,
        98 => 508951,
        99 => 3097992,
        100 => 44288,
        101 => -1100098,
        102 => 904516,
        103 => 3958618,
        104 => -3724342,
        105 => -8578,
        106 => 1653064,
        107 => -3249728,
        108 => 2389356,
        109 => -210977,
        110 => 759969,
        111 => -1316856,
        112 => 189548,
        113 => -3553272,
        114 => 3159746,
        115 => -1851402,
        116 => -2409325,
        117 => -177440,
        118 => 1315589,
        119 => 1341330,
        120 => 1285669,
        121 => -1584928,
        122 => -812732,
        123 => -1439742,
        124 => -3019102,
        125 => -3881060,
        126 => -3628969,
        127 => 3839961,
        128 => 2091667,
        129 => 3407706,
        130 => 2316500,
        131 => 3817976,
        132 => -3342478,
        133 => 2244091,
        134 => -2446433,
        135 => -3562462,
        136 => 266997,
        137 => 2434439,
        138 => -1235728,
        139 => 3513181,
        140 => -3520352,
        141 => -3759364,
        142 => -1197226,
        143 => -3193378,
        144 => 900702,
        145 => 1859098,
        146 => 909542,
        147 => 819034,
        148 => 495491,
        149 => -1613174,
        150 => -43260,
        151 => -522500,
        152 => -655327,
        153 => -3122442,
        154 => 2031748,
        155 => 3207046,
        156 => -3556995,
        157 => -525098,
        158 => -768622,
        159 => -3595838,
        160 => 342297,
        161 => 286988,
        162 => -2437823,
        163 => 4108315,
        164 => 3437287,
        165 => -3342277,
        166 => 1735879,
        167 => 203044,
        168 => 2842341,
        169 => 2691481,
        170 => -2590150,
        171 => 1265009,
        172 => 4055324,
        173 => 1247620,
        174 => 2486353,
        175 => 1595974,
        176 => -3767016,
        177 => 1250494,
        178 => 2635921,
        179 => -3548272,
        180 => -2994039,
        181 => 1869119,
        182 => 1903435,
        183 => -1050970,
        184 => -1333058,
        185 => 1237275,
        186 => -3318210,
        187 => -1430225,
        188 => -451100,
        189 => 1312455,
        190 => 3306115,
        191 => -1962642,
        192 => -1279661,
        193 => 1917081,
        194 => -2546312,
        195 => -1374803,
        196 => 1500165,
        197 => 777191,
        198 => 2235880,
        199 => 3406031,
        200 => -542412,
        201 => -2831860,
        202 => -1671176,
        203 => -1846953,
        204 => -2584293,
        205 => -3724270,
        206 => 594136,
        207 => -3776993,
        208 => -2013608,
        209 => 2432395,
        210 => 2454455,
        211 => -164721,
        212 => 1957272,
        213 => 3369112,
        214 => 185531,
        215 => -1207385,
        216 => -3183426,
        217 => 162844,
        218 => 1616392,
        219 => 3014001,
        220 => 810149,
        221 => 1652634,
        222 => -3694233,
        223 => -1799107,
        224 => -3038916,
        225 => 3523897,
        226 => 3866901,
        227 => 269760,
        228 => 2213111,
        229 => -975884,
        230 => 1717735,
        231 => 472078,
        232 => -426683,
        233 => 1723600,
        234 => -1803090,
        235 => 1910376,
        236 => -1667432,
        237 => -1104333,
        238 => -260646,
        239 => -3833893,
        240 => -2939036,
        241 => -2235985,
        242 => -420899,
        243 => -2286327,
        244 => 183443,
        245 => -976891,
        246 => 1612842,
        247 => -3545687,
        248 => -554416,
        249 => 3919660,
        250 => -48306,
        251 => -1362209,
        252 => 3937738,
        253 => 1400424,
        254 => -846154,
        255 => 1976782,
        _ => unreachable!()
    }
}        

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"
let simd_layer_bound (step:usize) =
    match step with
    | MkInt 1 -> 7
    | MkInt 2 -> 6
    | MkInt 4 -> 5
    | _ -> 5
"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    v step <= 4 /\ v index + v step < 8 /\    
    Spec.Utils.is_i32b 
        (v $NTT_BASE_BOUND + (simd_layer_bound $step * v $FIELD_MAX))
        (Seq.index ${simd_unit}.f_values (v $index)) /\
    Spec.Utils.is_i32b 
        (v $NTT_BASE_BOUND + (simd_layer_bound $step * v $FIELD_MAX))
        (Seq.index ${simd_unit}.f_values (v $index + v $step)) /\
    Spec.Utils.is_i32b 4190208 $zeta 
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.modifies2_8 ${simd_unit}.f_values ${simd_unit}_future.f_values index (index +! step) /\
    Spec.Utils.is_i32b 
        (v $NTT_BASE_BOUND + ((simd_layer_bound $step + 1)  * v $FIELD_MAX))
        (Seq.index ${simd_unit}_future.f_values (v $index)) /\
    Spec.Utils.is_i32b 
        (v $NTT_BASE_BOUND + ((simd_layer_bound $step + 1)  * v $FIELD_MAX))
        (Seq.index ${simd_unit}_future.f_values (v $index + v $step))
"#) )]
fn simd_unit_ntt_step(simd_unit: &mut Coefficients, zeta : i32, index : usize, step: usize){
    let t = montgomery_multiply_fe_by_fer(simd_unit.values[index+step], zeta);
    simd_unit.values[index+step] = simd_unit.values[index] - t;
    simd_unit.values[index] = simd_unit.values[index] + t;
} 

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta0 /\
    Spec.Utils.is_i32b 4190208 $zeta1 /\
    Spec.Utils.is_i32b 4190208 $zeta2 /\
    Spec.Utils.is_i32b 4190208 $zeta3
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 8 * v $FIELD_MAX) ${simd_unit}_future.f_values
"#) )]
pub fn simd_unit_ntt_at_layer_0(
    simd_unit: &mut Coefficients,
    zeta0: i32,
    zeta1: i32,
    zeta2: i32,
    zeta3: i32,
) {
    simd_unit_ntt_step(simd_unit, zeta0, 0, 1);
    simd_unit_ntt_step(simd_unit, zeta1, 2, 1);
    simd_unit_ntt_step(simd_unit, zeta2, 4, 1);
    simd_unit_ntt_step(simd_unit, zeta3, 6, 1); 
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta1 /\
    Spec.Utils.is_i32b 4190208 $zeta2
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) ${simd_unit}_future.f_values
"#) )]
pub fn simd_unit_ntt_at_layer_1(simd_unit: &mut Coefficients, zeta1: i32, zeta2: i32) {
    simd_unit_ntt_step(simd_unit, zeta1, 0, 2);
    simd_unit_ntt_step(simd_unit, zeta1, 1, 2);
    simd_unit_ntt_step(simd_unit, zeta2, 4, 2);
    simd_unit_ntt_step(simd_unit, zeta2, 5, 2); 
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 5 * v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) ${simd_unit}_future.f_values
"#) )]
pub fn simd_unit_ntt_at_layer_2(simd_unit: &mut Coefficients, zeta: i32) {
    simd_unit_ntt_step(simd_unit, zeta, 0, 4);
    simd_unit_ntt_step(simd_unit, zeta, 1, 4);
    simd_unit_ntt_step(simd_unit, zeta, 2, 4);
    simd_unit_ntt_step(simd_unit, zeta, 3, 4); 
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"
    let is_i32b_polynomial (b:nat) (re:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) =
        Spec.Utils.forall32 (fun x -> Spec.Utils.is_i32b_array_opaque b (Seq.index re x).f_values)
"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 8 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_0(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) 
            (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta_0 /\
        Spec.Utils.is_i32b 4190208 $zeta_1 /\
        Spec.Utils.is_i32b 4190208 $zeta_2 /\
        Spec.Utils.is_i32b 4190208 $zeta_3
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 8 * v $FIELD_MAX)
            (Seq.index ${re}_future (v index)).f_values
     "#))]
    fn round(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
        zeta_2: i32,
        zeta_3: i32,
    ) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_0(&mut re[index], zeta_0, zeta_1, zeta_2, zeta_3);
    }

    round(re, 0, 2091667, 3407706, 2316500, 3817976);
    round(re, 1, -3342478, 2244091, -2446433, -3562462);
    round(re, 2, 266997, 2434439, -1235728, 3513181);
    round(re, 3, -3520352, -3759364, -1197226, -3193378);
    round(re, 4, 900702, 1859098, 909542, 819034);
    round(re, 5, 495491, -1613174, -43260, -522500);
    round(re, 6, -655327, -3122442, 2031748, 3207046);
    round(re, 7, -3556995, -525098, -768622, -3595838);
    round(re, 8, 342297, 286988, -2437823, 4108315);
    round(re, 9, 3437287, -3342277, 1735879, 203044);
    round(re, 10, 2842341, 2691481, -2590150, 1265009);
    round(re, 11, 4055324, 1247620, 2486353, 1595974);
    round(re, 12, -3767016, 1250494, 2635921, -3548272);
    round(re, 13, -2994039, 1869119, 1903435, -1050970);
    round(re, 14, -1333058, 1237275, -3318210, -1430225);
    round(re, 15, -451100, 1312455, 3306115, -1962642);
    round(re, 16, -1279661, 1917081, -2546312, -1374803);
    round(re, 17, 1500165, 777191, 2235880, 3406031);
    round(re, 18, -542412, -2831860, -1671176, -1846953);
    round(re, 19, -2584293, -3724270, 594136, -3776993);
    round(re, 20, -2013608, 2432395, 2454455, -164721);
    round(re, 21, 1957272, 3369112, 185531, -1207385);
    round(re, 22, -3183426, 162844, 1616392, 3014001);
    round(re, 23, 810149, 1652634, -3694233, -1799107);
    round(re, 24, -3038916, 3523897, 3866901, 269760);
    round(re, 25, 2213111, -975884, 1717735, 472078);
    round(re, 26, -426683, 1723600, -1803090, 1910376);
    round(re, 27, -1667432, -1104333, -260646, -3833893);
    round(re, 28, -2939036, -2235985, -420899, -2286327);
    round(re, 29, 183443, -976891, 1612842, -3545687);
    round(re, 30, -554416, 3919660, -48306, -1362209);
    round(re, 31, 3937738, 1400424, -846154, 1976782);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_1(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) 
                                 (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta_0 /\
        Spec.Utils.is_i32b 4190208 $zeta_1
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX)
            (Seq.index ${re}_future (v index)).f_values
     "#))]
    fn round(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
    ) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_1(&mut re[index], zeta_0, zeta_1);
    }

    round(re, 0, -3930395, -1528703);
    round(re, 1, -3677745, -3041255);
    round(re, 2, -1452451, 3475950);
    round(re, 3, 2176455, -1585221);
    round(re, 4, -1257611, 1939314);
    round(re, 5, -4083598, -1000202);
    round(re, 6, -3190144, -3157330);
    round(re, 7, -3632928, 126922);
    round(re, 8, 3412210, -983419);
    round(re, 9, 2147896, 2715295);
    round(re, 10, -2967645, -3693493);
    round(re, 11, -411027, -2477047);
    round(re, 12, -671102, -1228525);
    round(re, 13, -22981, -1308169);
    round(re, 14, -381987, 1349076);
    round(re, 15, 1852771, -1430430);
    round(re, 16, -3343383, 264944);
    round(re, 17, 508951, 3097992);
    round(re, 18, 44288, -1100098);
    round(re, 19, 904516, 3958618);
    round(re, 20, -3724342, -8578);
    round(re, 21, 1653064, -3249728);
    round(re, 22, 2389356, -210977);
    round(re, 23, 759969, -1316856);
    round(re, 24, 189548, -3553272);
    round(re, 25, 3159746, -1851402);
    round(re, 26, -2409325, -177440);
    round(re, 27, 1315589, 1341330);
    round(re, 28, 1285669, -1584928);
    round(re, 29, -812732, -1439742);
    round(re, 30, -3019102, -3881060);
    round(re, 31, -3628969, 3839961);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 5 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_2(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 200")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 5 * v $FIELD_MAX) 
                                        (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX)
            (Seq.index ${re}_future (v index)).f_values
    "#))]
    fn round(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT], index: usize, zeta: i32) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_2(&mut re[index], zeta);
    }

    round(re, 0, 2706023);
    round(re, 1, 95776);
    round(re, 2, 3077325);
    round(re, 3, 3530437);
    round(re, 4, -1661693);
    round(re, 5, -3592148);
    round(re, 6, -2537516);
    round(re, 7, 3915439);
    round(re, 8, -3861115);
    round(re, 9, -3043716);
    round(re, 10, 3574422);
    round(re, 11, -2867647);
    round(re, 12, 3539968);
    round(re, 13, -300467);
    round(re, 14, 2348700);
    round(re, 15, -539299);
    round(re, 16, -1699267);
    round(re, 17, -1643818);
    round(re, 18, 3505694);
    round(re, 19, -3821735);
    round(re, 20, 3507263);
    round(re, 21, -2140649);
    round(re, 22, -1600420);
    round(re, 23, 3699596);
    round(re, 24, 811944);
    round(re, 25, 531354);
    round(re, 26, 954230);
    round(re, 27, 3881043);
    round(re, 28, 3900724);
    round(re, 29, -2556880);
    round(re, 30, 2071892);
    round(re, 31, -2797779);
}

#[inline(always)]
#[hax_lib::fstar::before(r#"
[@ "opaque_to_smt"]
let layer_bound (step_by:usize) : n:nat{n <= 4} =
    match step_by with
    | MkInt 1 -> 4
    | MkInt 2 -> 3
    | MkInt 4 -> 2
    | MkInt 8 -> 1
    | MkInt 16 -> 0
    | _ -> 0

let bounded_sub_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
  Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
        (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b)) = admit()

let bounded_sub_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
  Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                   b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future))
        (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future)) = admit()

let bounded_add_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
  Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
        (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b)) = admit()

let bounded_add_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
  Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                   b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future))
        (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future)) = admit()
"#)]
#[hax_lib::fstar::options("--z3rlimit 600 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    (v $OFFSET + v $STEP_BY < v $SIMD_UNITS_IN_RING_ELEMENT) /\
    (v $OFFSET + 2 * v $STEP_BY <= v $SIMD_UNITS_IN_RING_ELEMENT) /\
    (Spec.Utils.forall32 (fun i -> (i >= v $OFFSET /\ i < (v $OFFSET + 2 * v $STEP_BY)) ==>
              Spec.Utils.is_i32b_array_opaque 
                (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX)) 
                (Seq.index ${re} i).f_values)) /\
    Spec.Utils.is_i32b 4190208 $ZETA
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.modifies_range_32 ${re} ${re}_future $OFFSET (${OFFSET + STEP_BY + STEP_BY}) /\
    (Spec.Utils.forall32 (fun i -> (i >= v $OFFSET /\ i < (v $OFFSET + 2 * v $STEP_BY)) ==>
              Spec.Utils.is_i32b_array_opaque 
                (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY + 1) * v $FIELD_MAX)) 
                (Seq.index ${re}_future i).f_values))
"#))]
fn outer_3_plus<const OFFSET: usize, const STEP_BY: usize, const ZETA: i32>(
    re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
) {
    #[cfg(hax)]
    let orig_re = re.clone();
    
    for j in OFFSET..OFFSET + STEP_BY {
        hax_lib::loop_invariant!(|j: usize| fstar!(r#"
            (Spec.Utils.modifies_range2_32 $orig_re $re 
                $OFFSET $j ($OFFSET +! $STEP_BY) ($j +! $STEP_BY)) /\
            (Spec.Utils.forall32 (fun i -> ((i >= v $OFFSET /\ i < v $j) \/ 
                        (i >= v $OFFSET + v $STEP_BY /\ i < v $j + v $STEP_BY)) ==>
                Spec.Utils.is_i32b_array_opaque 
                    (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY + 1) * v $FIELD_MAX)) 
                    (Seq.index ${re} i).f_values))
        "#));

        let mut tmp = re[j + STEP_BY];
        montgomery_multiply_by_constant(&mut tmp, ZETA);

        re[j + STEP_BY] = re[j];

        hax_lib::fstar!(r#"
        bounded_sub_pre (Seq.index $orig_re (v $j)).f_values ${tmp}.f_values
            (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX))
            (v $FIELD_MAX)"#);
        hax_lib::fstar!(r#"
            bounded_add_pre (Seq.index orig_re (v $j)).f_values ${tmp}.f_values
                (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX))
                (v $FIELD_MAX)"#);

        arithmetic::subtract(&mut re[j + STEP_BY], &tmp);
        arithmetic::add(&mut re[j], &tmp);

        hax_lib::fstar!(r#"
        assert ((v v_NTT_BASE_BOUND + ((layer_bound v_STEP_BY) * v v_FIELD_MAX)) + (v v_FIELD_MAX) 
                == (v v_NTT_BASE_BOUND + ((layer_bound v_STEP_BY + 1) * v v_FIELD_MAX)))"#);
        hax_lib::fstar!(r#"
        bounded_sub_post (Seq.index $orig_re (v $j)).f_values ${tmp}.f_values
            (Seq.index $re (v $j + v $STEP_BY)).f_values
            (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX))
            (v $FIELD_MAX)
            (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY + 1) * v $FIELD_MAX))"#);
        hax_lib::fstar!(r#"
        bounded_add_post (Seq.index $orig_re (v $j)).f_values ${tmp}.f_values
            (Seq.index $re (v $j)).f_values
            (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX))
            (v $FIELD_MAX)
            (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY + 1) * v $FIELD_MAX))"#);
    }
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 4 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 5 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_3(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 8; // 1 << LAYER;
    const STEP_BY: usize = 1; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2725464>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1024112>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1079900>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3585928>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -549488>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1119584>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2619752>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2108549>(re);
    outer_3_plus::<{ (8 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2118186>(re);
    outer_3_plus::<{ (9 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3859737>(re);
    outer_3_plus::<{ (10 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1399561>(re);
    outer_3_plus::<{ (11 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3277672>(re);
    outer_3_plus::<{ (12 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1757237>(re);
    outer_3_plus::<{ (13 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -19422>(re);
    outer_3_plus::<{ (14 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 4010497>(re);
    outer_3_plus::<{ (15 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 280005>(re);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 3 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 4 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_4(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 16; // 1 << LAYER;
    const STEP_BY: usize = 2; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1826347>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2353451>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -359251>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2091905>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3119733>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2884855>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3111497>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2680103>(re);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 2 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 3 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_5(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 32; // 1 << LAYER;
    const STEP_BY: usize = 4; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 237124>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -777960>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -876248>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 466468>(re);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 1 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 2 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_6(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 64; // 1 << LAYER;
    const STEP_BY: usize = 8; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2608894>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -518909>(re);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND) $re
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND + 1 * v $FIELD_MAX) ${re}_future
"#) )]
fn ntt_at_layer_7(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 128; // 1 << LAYER;
    const STEP_BY: usize = 16; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 25847>(re);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    is_i32b_polynomial (v $NTT_BASE_BOUND) ${re}
"#))]
pub(crate) fn ntt(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    ntt_at_layer_7(re);
    ntt_at_layer_6(re);
    ntt_at_layer_5(re);
    ntt_at_layer_4(re);
    ntt_at_layer_3(re);
    ntt_at_layer_2(re);
    ntt_at_layer_1(re);
    ntt_at_layer_0(re);
}
