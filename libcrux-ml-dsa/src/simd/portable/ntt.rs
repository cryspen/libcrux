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
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
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

#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(i < 256)]
#[hax_lib::ensures(|result| 
    fstar!(r#"
     Spec.Utils.is_i32b (v $FIELD_MID) $result /\
     v $result % (v $PRIME) ==
     (v (${zeta} i) * pow2 32) % (v $PRIME)"#))]
#[inline(always)]
const fn zeta_r(i:usize) -> i32 {
    hax_lib::fstar!("reveal_opaque (`%zeta) (zeta)");
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
        v $IDX < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX) 
            (Seq.index ${re} (v $IDX)).f_values /\
        $ZETA0 == ${zeta_r(128 + 4*IDX)} /\
        $ZETA1 == ${zeta_r(128 + 4*IDX + 1)} /\
        $ZETA2 == ${zeta_r(128 + 4*IDX + 2)} /\
        $ZETA3 == ${zeta_r(128 + 4*IDX + 3)}
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $IDX /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 8 * v $FIELD_MAX)
            (Seq.index ${re}_future (v $IDX)).f_values
     "#))]
    fn round<const IDX:usize, const ZETA0:i32, const ZETA1:i32, const ZETA2: i32, const ZETA3: i32>(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
    ) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_0(&mut re[IDX], ZETA0, ZETA1, ZETA2, ZETA3);
    }

    round::<0, { zeta_r(128) }, { zeta_r(129) }, { zeta_r(130) }, { zeta_r(131) }>(re);
    round::<1, { zeta_r(132) }, { zeta_r(133) }, { zeta_r(134) }, { zeta_r(135) }>(re);
    round::<2, { zeta_r(136) }, { zeta_r(137) }, { zeta_r(138) }, { zeta_r(139) }>(re);
    round::<3, { zeta_r(140) }, { zeta_r(141) }, { zeta_r(142) }, { zeta_r(143) }>(re);
    round::<4, { zeta_r(144) }, { zeta_r(145) }, { zeta_r(146) }, { zeta_r(147) }>(re);
    round::<5, { zeta_r(148) }, { zeta_r(149) }, { zeta_r(150) }, { zeta_r(151) }>(re);
    round::<6, { zeta_r(152) }, { zeta_r(153) }, { zeta_r(154) }, { zeta_r(155) }>(re);
    round::<7, { zeta_r(156) }, { zeta_r(157) }, { zeta_r(158) }, { zeta_r(159) }>(re);
    round::<8, { zeta_r(160) }, { zeta_r(161) }, { zeta_r(162) }, { zeta_r(163) }>(re);
    round::<9, { zeta_r(164) }, { zeta_r(165) }, { zeta_r(166) }, { zeta_r(167) }>(re);
    round::<10,{ zeta_r(168) }, { zeta_r(169) }, { zeta_r(170) }, { zeta_r(171) }>(re);
    round::<11,{ zeta_r(172) }, { zeta_r(173) }, { zeta_r(174) }, { zeta_r(175) }>(re);
    round::<12,{ zeta_r(176) }, { zeta_r(177) }, { zeta_r(178) }, { zeta_r(179) }>(re);
    round::<13,{ zeta_r(180) }, { zeta_r(181) }, { zeta_r(182) }, { zeta_r(183) }>(re);
    round::<14,{ zeta_r(184) }, { zeta_r(185) }, { zeta_r(186) }, { zeta_r(187) }>(re);
    round::<15,{ zeta_r(188) }, { zeta_r(189) }, { zeta_r(190) }, { zeta_r(191) }>(re);
    round::<16,{ zeta_r(192) }, { zeta_r(193) }, { zeta_r(194) }, { zeta_r(195) }>(re);
    round::<17,{ zeta_r(196) }, { zeta_r(197) }, { zeta_r(198) }, { zeta_r(199) }>(re);
    round::<18,{ zeta_r(200) }, { zeta_r(201) }, { zeta_r(202) }, { zeta_r(203) }>(re);
    round::<19,{ zeta_r(204) }, { zeta_r(205) }, { zeta_r(206) }, { zeta_r(207) }>(re);
    round::<20,{ zeta_r(208) }, { zeta_r(209) }, { zeta_r(210) }, { zeta_r(211) }>(re);
    round::<21,{ zeta_r(212) }, { zeta_r(213) }, { zeta_r(214) }, { zeta_r(215) }>(re);
    round::<22,{ zeta_r(216) }, { zeta_r(217) }, { zeta_r(218) }, { zeta_r(219) }>(re);
    round::<23,{ zeta_r(220) }, { zeta_r(221) }, { zeta_r(222) }, { zeta_r(223) }>(re);
    round::<24,{ zeta_r(224) }, { zeta_r(225) }, { zeta_r(226) }, { zeta_r(227) }>(re);
    round::<25,{ zeta_r(228) }, { zeta_r(229) }, { zeta_r(230) }, { zeta_r(231) }>(re);
    round::<26,{ zeta_r(232) }, { zeta_r(233) }, { zeta_r(234) }, { zeta_r(235) }>(re);
    round::<27,{ zeta_r(236) }, { zeta_r(237) }, { zeta_r(238) }, { zeta_r(239) }>(re);
    round::<28,{ zeta_r(240) }, { zeta_r(241) }, { zeta_r(242) }, { zeta_r(243) }>(re);
    round::<29,{ zeta_r(244) }, { zeta_r(245) }, { zeta_r(246) }, { zeta_r(247) }>(re);
    round::<30,{ zeta_r(248) }, { zeta_r(249) }, { zeta_r(250) }, { zeta_r(251) }>(re);
    round::<31,{ zeta_r(252) }, { zeta_r(253) }, { zeta_r(254) }, { zeta_r(255) }>(re);
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
        v $IDX < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX) 
                                 (Seq.index ${re} (v $IDX)).f_values /\
        $ZETA0 == ${zeta_r(64 + 2*IDX)} /\
        $ZETA1 == ${zeta_r(64 + 2*IDX + 1)}
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $IDX /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 7 * v $FIELD_MAX)
            (Seq.index ${re}_future (v $IDX)).f_values
     "#))]
    fn round<const IDX:usize, const ZETA0:i32, const ZETA1:i32>(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
    ) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_1(&mut re[IDX], ZETA0, ZETA1);
    }

    round::<0 , { zeta_r(64) }, { zeta_r(65) }>(re);
    round::<1 , { zeta_r(66) }, { zeta_r(67) }>(re);
    round::<2 , { zeta_r(68) }, { zeta_r(69) }>(re);
    round::<3 , { zeta_r(70) }, { zeta_r(71) }>(re);
    round::<4 , { zeta_r(72) }, { zeta_r(73) }>(re);
    round::<5 , { zeta_r(74) }, { zeta_r(75) }>(re);
    round::<6 , { zeta_r(76) }, { zeta_r(77) }>(re);
    round::<7 , { zeta_r(78) }, { zeta_r(79) }>(re);
    round::<8 , { zeta_r(80) }, { zeta_r(81) }>(re);
    round::<9 , { zeta_r(82) }, { zeta_r(83) }>(re);
    round::<10, { zeta_r(84) }, { zeta_r(85) }>(re);
    round::<11, { zeta_r(86) }, { zeta_r(87) }>(re);
    round::<12, { zeta_r(88) }, { zeta_r(89) }>(re);
    round::<13, { zeta_r(90) }, { zeta_r(91) }>(re);
    round::<14, { zeta_r(92) }, { zeta_r(93) }>(re);
    round::<15, { zeta_r(94) }, { zeta_r(95) }>(re);
    round::<16, { zeta_r(96) }, { zeta_r(97) }>(re);
    round::<17, { zeta_r(98) }, { zeta_r(99) }>(re);
    round::<18, { zeta_r(100) }, { zeta_r(101) }>(re);
    round::<19, { zeta_r(102) }, { zeta_r(103) }>(re);
    round::<20, { zeta_r(104) }, { zeta_r(105) }>(re);
    round::<21, { zeta_r(106) }, { zeta_r(107) }>(re);
    round::<22, { zeta_r(108) }, { zeta_r(109) }>(re);
    round::<23, { zeta_r(110) }, { zeta_r(111) }>(re);
    round::<24, { zeta_r(112) }, { zeta_r(113) }>(re);
    round::<25, { zeta_r(114) }, { zeta_r(115) }>(re);
    round::<26, { zeta_r(116) }, { zeta_r(117) }>(re);
    round::<27, { zeta_r(118) }, { zeta_r(119) }>(re);
    round::<28, { zeta_r(120) }, { zeta_r(121) }>(re);
    round::<29, { zeta_r(122) }, { zeta_r(123) }>(re);
    round::<30, { zeta_r(124) }, { zeta_r(125) }>(re);
    round::<31, { zeta_r(126) }, { zeta_r(127) }>(re);
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
        v $IDX < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 5 * v $FIELD_MAX) 
                                        (Seq.index ${re} (v $IDX)).f_values /\
        $ZETA = ${zeta_r(32+IDX)}
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $IDX /\
        Spec.Utils.is_i32b_array_opaque (v $NTT_BASE_BOUND + 6 * v $FIELD_MAX)
            (Seq.index ${re}_future (v $IDX)).f_values
    "#))]
    fn round<const IDX:usize, const ZETA:i32>(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        simd_unit_ntt_at_layer_2(&mut re[IDX], ZETA);
    }

    round::<0 , { zeta_r(32) }>(re);
    round::<1 , { zeta_r(33) }>(re);
    round::<2 , { zeta_r(34) }>(re);
    round::<3 , { zeta_r(35) }>(re);
    round::<4 , { zeta_r(36) }>(re);
    round::<5 , { zeta_r(37) }>(re);
    round::<6 , { zeta_r(38) }>(re);
    round::<7 , { zeta_r(39) }>(re);
    round::<8 , { zeta_r(40) }>(re);
    round::<9 , { zeta_r(41) }>(re);
    round::<10, { zeta_r(42) }>(re);
    round::<11, { zeta_r(43) }>(re);
    round::<12, { zeta_r(44) }>(re);
    round::<13, { zeta_r(45) }>(re);
    round::<14, { zeta_r(46) }>(re);
    round::<15, { zeta_r(47) }>(re);
    round::<16, { zeta_r(48) }>(re);
    round::<17, { zeta_r(49) }>(re);
    round::<18, { zeta_r(50) }>(re);
    round::<19, { zeta_r(51) }>(re);
    round::<20, { zeta_r(52) }>(re);
    round::<21, { zeta_r(53) }>(re);
    round::<22, { zeta_r(54) }>(re);
    round::<23, { zeta_r(55) }>(re);
    round::<24, { zeta_r(56) }>(re);
    round::<25, { zeta_r(57) }>(re);
    round::<26, { zeta_r(58) }>(re);
    round::<27, { zeta_r(59) }>(re);
    round::<28, { zeta_r(60) }>(re);
    round::<29, { zeta_r(61) }>(re);
    round::<30, { zeta_r(62) }>(re);
    round::<31, { zeta_r(63) }>(re);
}

#[inline(always)]
#[hax_lib::fstar::before(r#"
let layer_bound (step_by:usize) =
    match step_by with
    | MkInt 1 -> 4
    | MkInt 2 -> 3
    | MkInt 4 -> 2
    | MkInt 8 -> 1
    | MkInt 16 -> 0
    | _ -> 0"#)]
#[hax_lib::fstar::options("--z3rlimit 600 --split_queries always")]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    (v $OFFSET + 2 * v $STEP_BY <= v $SIMD_UNITS_IN_RING_ELEMENT) /\
    (Spec.Utils.forall32 (fun i -> (i >= v $OFFSET /\ i < (v $OFFSET + 2 * v $STEP_BY)) ==>
              Spec.Utils.is_i32b_array_opaque 
                (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY) * v $FIELD_MAX)) 
                (Seq.index ${re} i).f_values)) /\
    $ZETA == ${zeta_r(16+OFFSET/2)}
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
            (Spec.Utils.forall32 (fun i -> (i < v $OFFSET \/ 
                        (i >= v $j /\ i < v $OFFSET + v $STEP_BY) \/ 
                        (i >= v $j + v $STEP_BY /\ i < v $SIMD_UNITS_IN_RING_ELEMENT)) 
                ==> Seq.index re i == Seq.index orig_re i)) /\
            (Spec.Utils.forall32 (fun i -> ((i >= v $OFFSET /\ i < v $j) \/ 
                        (i >= v $OFFSET + v $STEP_BY /\ i < v $j + v $STEP_BY)) ==>
                Spec.Utils.is_i32b_array_opaque 
                    (v $NTT_BASE_BOUND + ((layer_bound $STEP_BY + 1) * v $FIELD_MAX)) 
                    (Seq.index ${re} i).f_values))
        "#));

        let mut tmp = re[j + STEP_BY];
        montgomery_multiply_by_constant(&mut tmp, ZETA);

        re[j + STEP_BY] = re[j];

        hax_lib::fstar!("reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)");
        arithmetic::subtract(&mut re[j + STEP_BY], &tmp);
        arithmetic::add(&mut re[j], &tmp);
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

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(16) }>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(17) }>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(18) }>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(19) }>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(20) }>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(21) }>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(22) }>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(23) }>(re);
    outer_3_plus::<{ (8 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(24) }>(re);
    outer_3_plus::<{ (9 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT },  STEP_BY, { zeta_r(25) }>(re);
    outer_3_plus::<{ (10 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(26) }>(re);
    outer_3_plus::<{ (11 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(27) }>(re);
    outer_3_plus::<{ (12 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(28) }>(re);
    outer_3_plus::<{ (13 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(29) }>(re);
    outer_3_plus::<{ (14 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(30) }>(re);
    outer_3_plus::<{ (15 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(31) }>(re);
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

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(8) }>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(9) }>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(10) }>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(11) }>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(12) }>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(13) }>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(14) }>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(15) }>(re);
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

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(4) }>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(5) }>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(6) }>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(7) }>(re);
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

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(2) }>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(3) }>(re);
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

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, { zeta_r(1) }>(re);
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
