use crate::constants::{Eta, Gamma2};

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub(crate) trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];
}

#[cfg(hax)]
pub(crate) mod specs {
    use hax_lib::*;

    pub(crate) const PRIME: u32 = 8380417;

    pub(crate) const MONT_R: u32 = 8380417;

    pub(crate) const FIELD_MAX: u32 = 8380416;

    pub(crate) const FIELD_MID: u32 = 4190208;

    pub(crate) const NTT_BASE_BOUND: u32 = FIELD_MID;

    const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

    type SIMDContent = [i32; COEFFICIENTS_IN_SIMD_UNIT];

    pub(crate) fn int_is_i32(i: Int) -> bool {
        i <= i32::MAX.to_int() && i >= i32::MIN.to_int()
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_add_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
                (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b))
               [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_pre a b); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%$add_pre) ($add_pre)
    "#)]
    pub(crate) fn add_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                int_is_i32(lhs[i].to_int() + rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_add_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                    b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future))
            (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
            [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.add_post a b a_future); 
            SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
            SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
            SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
        reveal_opaque (`%$add_post) ($add_post)
    "#)]
    pub(crate) fn add_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                future_lhs[i].to_int() == (lhs[i].to_int() + rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_sub_pre (a b: t_Array i32 (sz 8)) (b1:nat) (b2:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\ b1 + b2 <= 4294967295))
              (ensures (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b))
              [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_pre a b); 
               SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
               SMTPat (Spec.Utils.is_i32b_array_opaque b2 b)] = 
        reveal_opaque (`%$sub_pre) ($sub_pre)
    "#)]
    pub(crate) fn sub_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                int_is_i32(lhs[i].to_int() - rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::fstar::after(r#"
    let bounded_sub_post (a b a_future: t_Array i32 (sz 8)) (b1 b2 b3:nat):
        Lemma (requires (Spec.Utils.is_i32b_array_opaque b1 a /\ Spec.Utils.is_i32b_array_opaque b2 b /\
                        b1 + b2 <= b3 /\ Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future))
                (ensures (Spec.Utils.is_i32b_array_opaque b3 a_future))
                [SMTPat (Libcrux_ml_dsa.Simd.Traits.Specs.sub_post a b a_future); 
                SMTPat (Spec.Utils.is_i32b_array_opaque b1 a);
                SMTPat (Spec.Utils.is_i32b_array_opaque b2 b);
                SMTPat (Spec.Utils.is_i32b_array_opaque b3 a_future)] = 
                reveal_opaque (`%$sub_post) ($sub_post)
    "#)]
    pub(crate) fn sub_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
        forall(|i: usize| {
            implies(
                i < COEFFICIENTS_IN_SIMD_UNIT,
                future_lhs[i].to_int() == (lhs[i].to_int() - rhs[i].to_int()),
            )
        })
    }

    #[hax_lib::requires(i < 256)]
    #[hax_lib::ensures(|result| result >= 0 && result <= FIELD_MAX as i32)]
    const fn zeta(i: usize) -> i32 {
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
            _ => unreachable!(),
        }
    }

    #[hax_lib::requires(i < 256)]
    #[hax_lib::ensures(|result| fstar!(r#"
        Spec.Utils.is_i32b (v $FIELD_MID) $result /\
        v $result % (v $PRIME) ==
        (v (${zeta} i) * pow2 32) % (v $PRIME)"#))]
    const fn zeta_r(i: usize) -> i32 {
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
            _ => unreachable!(),
        }
    }
}

#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub(crate) trait Operations: Copy + Clone + Repr {
    #[hax_lib::ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Self;

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).repr() == array)]
    fn from_coefficient_array(array: &[i32], out: &mut Self);

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out) == value.repr())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(specs::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self);

    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    #[hax_lib::requires(serialized.len() == 4 || serialized.len() == 6)]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}

#[cfg(eurydice)]
pub(crate) trait Operations: Copy + Clone {
    fn zero() -> Self;

    fn from_coefficient_array(array: &[i32], out: &mut Self);
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    fn add(lhs: &mut Self, rhs: &Self);
    fn subtract(lhs: &mut Self, rhs: &Self);
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
