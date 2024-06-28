use crate::{
    arithmetic::PolynomialRingElement,
    constants::FIELD_MODULUS,
    encoding,
    hash_functions::{H, H_128},
};

#[inline(always)]
fn rejection_sample_less_than_field_modulus(
    randomness: &[u8],
    sampled: &mut usize,
    out: &mut PolynomialRingElement,
) -> bool {
    let mut done = false;

    for bytes in randomness.chunks(3) {
        if !done {
            let b0 = bytes[0] as i32;
            let b1 = bytes[1] as i32;
            let b2 = bytes[2] as i32;

            let potential_coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

            if potential_coefficient < FIELD_MODULUS && *sampled < out.coefficients.len() {
                out.coefficients[*sampled] = potential_coefficient;
                *sampled += 1;
            }

            if *sampled == out.coefficients.len() {
                done = true;
            }
        }
    }

    done
}

#[inline(always)]
pub(crate) fn sample_ring_element_uniform(seed: [u8; 34]) -> PolynomialRingElement {
    let mut state = H_128::new(seed);
    let randomness = H_128::squeeze_first_five_blocks(&mut state);

    let mut out = PolynomialRingElement::ZERO;

    let mut sampled = 0;
    let mut done = rejection_sample_less_than_field_modulus(&randomness, &mut sampled, &mut out);

    while !done {
        let randomness = H_128::squeeze_next_block(&mut state);
        done = rejection_sample_less_than_field_modulus(&randomness, &mut sampled, &mut out);
    }

    out
}

#[inline(always)]
fn rejection_sample_less_than_eta_equals_2(
    randomness: &[u8],
    sampled: &mut usize,
    out: &mut PolynomialRingElement,
) -> bool {
    let mut done = false;

    for byte in randomness {
        if !done {
            let try_0 = byte & 0xF;
            let try_1 = byte >> 4;

            if try_0 < 15 && *sampled < out.coefficients.len() {
                let try_0 = try_0 as i32;

                // (try_0 * 26) >> 7 computes ⌊try_0 / 5⌋
                let try_0_mod_5 = try_0 - ((try_0 * 26) >> 7) * 5;

                out.coefficients[*sampled] = 2 - try_0_mod_5;

                *sampled += 1;
            }

            if try_1 < 15 && *sampled < out.coefficients.len() {
                let try_1 = try_1 as i32;
                let try_1_mod_5 = try_1 - ((try_1 * 26) >> 7) * 5;

                out.coefficients[*sampled] = 2 - try_1_mod_5;

                *sampled += 1;
            }

            if *sampled == out.coefficients.len() {
                done = true;
            }
        }
    }

    done
}

#[inline(always)]
fn rejection_sample_less_than_eta_equals_4(
    randomness: &[u8],
    sampled: &mut usize,
    out: &mut PolynomialRingElement,
) -> bool {
    let mut done = false;

    for byte in randomness {
        if !done {
            let try_0 = byte & 0xF;
            let try_1 = byte >> 4;

            if try_0 < 9 && *sampled < out.coefficients.len() {
                out.coefficients[*sampled] = 4 - (try_0 as i32);
                *sampled += 1;
            }

            if try_1 < 9 && *sampled < out.coefficients.len() {
                out.coefficients[*sampled] = 4 - (try_1 as i32);
                *sampled += 1;
            }

            if *sampled == out.coefficients.len() {
                done = true;
            }
        }
    }

    done
}

#[inline(always)]
pub(crate) fn rejection_sample_less_than_eta<const ETA: usize>(
    randomness: &[u8],
    sampled: &mut usize,
    out: &mut PolynomialRingElement,
) -> bool {
    match ETA {
        2 => rejection_sample_less_than_eta_equals_2(randomness, sampled, out),
        4 => rejection_sample_less_than_eta_equals_4(randomness, sampled, out),
        _ => unreachable!(),
    }
}

#[allow(non_snake_case)]
#[inline(always)]
fn sample_error_ring_element<const ETA: usize>(seed: [u8; 66]) -> PolynomialRingElement {
    let mut state = H::new(&seed);
    let randomness = H::squeeze_first_block(&mut state);

    let mut out = PolynomialRingElement::ZERO;

    let mut sampled = 0;
    let mut done = rejection_sample_less_than_eta::<ETA>(&randomness, &mut sampled, &mut out);

    while !done {
        let randomness = H::squeeze_next_block(&mut state);
        done = rejection_sample_less_than_eta::<ETA>(&randomness, &mut sampled, &mut out);
    }

    out
}

#[inline(always)]
pub(crate) fn sample_error_vector<const DIMENSION: usize, const ETA: usize>(
    mut seed: [u8; 66],
    domain_separator: &mut u16,
) -> [PolynomialRingElement; DIMENSION] {
    let mut error = [PolynomialRingElement::ZERO; DIMENSION];

    #[allow(clippy::needless_range_loop)]
    for i in 0..DIMENSION {
        seed[64] = *domain_separator as u8;
        seed[65] = (*domain_separator >> 8) as u8;
        *domain_separator += 1;

        error[i] = sample_error_ring_element::<ETA>(seed);
    }

    error
}

#[inline(always)]
fn sample_mask_ring_element<const GAMMA1_EXPONENT: usize>(seed: [u8; 66]) -> PolynomialRingElement {
    match GAMMA1_EXPONENT {
        17 => encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(&H::one_shot::<576>(&seed)),
        19 => encoding::gamma1::deserialize::<GAMMA1_EXPONENT>(&H::one_shot::<640>(&seed)),
        _ => unreachable!(),
    }
}

#[inline(always)]
pub(crate) fn sample_mask_vector<const DIMENSION: usize, const GAMMA1_EXPONENT: usize>(
    mut seed: [u8; 66],
    domain_separator: &mut u16,
) -> [PolynomialRingElement; DIMENSION] {
    let mut error = [PolynomialRingElement::ZERO; DIMENSION];

    #[allow(clippy::needless_range_loop)]
    for i in 0..DIMENSION {
        seed[64] = *domain_separator as u8;
        seed[65] = (*domain_separator >> 8) as u8;
        *domain_separator += 1;

        error[i] = sample_mask_ring_element::<GAMMA1_EXPONENT>(seed);
    }

    error
}

#[inline(always)]
fn inside_out_shuffle(
    randomness: &[u8],
    out_index: &mut usize,
    signs: &mut u64,
    result: &mut PolynomialRingElement,
) -> bool {
    let mut done = false;

    for byte in randomness {
        if !done {
            let sample_at = *byte as usize;
            if sample_at <= *out_index {
                result.coefficients[*out_index] = result.coefficients[sample_at];
                *out_index += 1;

                result.coefficients[sample_at] = 1 - 2 * ((*signs & 1) as i32);
                *signs >>= 1;
            }

            if *out_index == result.coefficients.len() {
                done = true;
            }
        }
    }

    done
}
#[inline(always)]
pub(crate) fn sample_challenge_ring_element<const NUMBER_OF_ONES: usize>(
    seed: [u8; 32],
) -> PolynomialRingElement {
    let mut state = H::new(&seed);
    let randomness = H::squeeze_first_block(&mut state);

    let mut signs = u64::from_le_bytes(randomness[0..8].try_into().unwrap());

    let mut result = PolynomialRingElement::ZERO;

    let mut out_index = result.coefficients.len() - NUMBER_OF_ONES;
    let mut done = inside_out_shuffle(&randomness[8..], &mut out_index, &mut signs, &mut result);

    while !done {
        let randomness = H::squeeze_next_block(&mut state);
        done = inside_out_shuffle(&randomness, &mut out_index, &mut signs, &mut result);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{arithmetic::FieldElement, constants::COEFFICIENTS_IN_RING_ELEMENT};

    #[test]
    fn test_sample_ring_element_uniform() {
        let seed: [u8; 34] = [
            33, 192, 250, 216, 117, 61, 16, 12, 248, 51, 213, 110, 64, 57, 119, 80, 164, 83, 73,
            91, 80, 128, 195, 219, 203, 149, 170, 233, 16, 232, 209, 105, 4, 5,
        ];

        let expected_coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT] = [
            886541, 1468422, 793958, 7610434, 3986512, 913782, 2546456, 5820798, 1940159, 10062,
            3303190, 3831326, 4834267, 3500674, 16909, 8314529, 7469249, 5611755, 6181076, 269257,
            3566448, 2968856, 7556314, 6685884, 129963, 8017973, 1087829, 5842199, 6867133, 442098,
            3473053, 3812349, 556165, 55620, 4367526, 798402, 5317265, 2828265, 3808240, 3065841,
            6340895, 2710831, 715345, 5806109, 3689225, 4088547, 4258029, 2877620, 6867225,
            3275166, 4626484, 6596723, 5180488, 3836050, 1115576, 2086584, 749098, 4980044,
            7626966, 961947, 4695118, 6488634, 7898263, 841160, 1186851, 6958928, 4995591, 6829719,
            5910175, 2590788, 987365, 5983050, 7039561, 1406907, 4054912, 3093314, 237981, 6184639,
            515190, 5209488, 6460375, 4417602, 7890594, 6584284, 1729237, 5851336, 8226663,
            1843549, 5872244, 1375077, 6275711, 997136, 2593411, 5739784, 6621377, 7180456,
            1437441, 2607410, 197226, 4753353, 5086363, 6096080, 3057564, 5040851, 886178, 699532,
            3772666, 7983776, 1235995, 1960665, 1233119, 317423, 442071, 4649134, 5043634, 4164756,
            3166873, 2343835, 6256400, 6132302, 4124098, 6087733, 5371278, 3484545, 1020458,
            3688444, 7263864, 2413270, 4449757, 5561507, 7464292, 1176556, 8294481, 2892372,
            5509298, 194732, 7976046, 5907126, 4792878, 5059916, 3122481, 7009119, 5476286,
            4905623, 7374799, 7284599, 4929839, 538055, 5611660, 233595, 6125390, 7441322, 3752658,
            6655759, 4907614, 2281767, 1659504, 5490352, 4235568, 7143494, 6217399, 1581266,
            2455222, 1015526, 8366150, 2002613, 185543, 7904386, 8206829, 5380721, 2226008,
            7713547, 6961768, 7911095, 5604679, 6839785, 7573702, 1113136, 5563352, 7446030,
            6694003, 1725163, 4749689, 6474727, 7125683, 1830230, 5300491, 7927815, 5808662,
            2345184, 5462894, 5760340, 1949317, 1853703, 5060631, 5935138, 4873466, 3302619,
            5351360, 5707708, 2715882, 2050173, 52173, 5463772, 2851164, 1702574, 7167630, 1132010,
            1418205, 4182063, 4919187, 2707143, 6241533, 3241235, 2286591, 268487, 3799838, 558302,
            5882605, 6165192, 6702794, 5578115, 1893372, 7246495, 4974148, 2633723, 1522313,
            7636103, 6639058, 6765356, 3588710, 7011438, 4798122, 2329503, 4671411, 6787853,
            1838957, 306944, 5112958, 853077, 7844176, 384195, 839634, 1860349, 7289878, 4054796,
            703698, 5147821, 7632328, 5993194, 6329638, 5959986, 3073141, 675737, 7364844, 4124952,
        ];

        assert_eq!(
            sample_ring_element_uniform(seed).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_sample_error_ring_element_when_eta_is_2() {
        let seed: [u8; 66] = [
            51, 203, 133, 235, 126, 210, 169, 81, 4, 134, 147, 168, 252, 67, 176, 99, 130, 186,
            254, 103, 241, 199, 173, 78, 121, 232, 12, 244, 4, 143, 8, 174, 122, 170, 124, 35, 53,
            49, 202, 94, 27, 249, 200, 186, 175, 198, 169, 116, 244, 227, 133, 111, 205, 140, 233,
            110, 227, 67, 35, 226, 194, 75, 130, 105, 5, 0,
        ];

        let expected_coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT] = [
            1, 0, -1, 0, 1, -2, -1, 0, -2, 2, -1, -2, 1, -2, 1, -2, 1, 2, -2, 2, -2, -1, 0, -2, -1,
            -2, -2, 1, 1, -1, 1, 1, 2, -2, 2, -1, 1, 2, 0, 2, -1, 0, 2, -2, -2, 2, 0, 2, 1, 1, 2,
            1, 1, -2, 1, -1, 2, -2, -2, 2, -2, -2, 0, 0, -1, 0, 2, 0, 1, 2, 0, 2, -1, 2, 0, 2, 1,
            -2, -2, 0, -1, -2, 2, -2, -1, 2, 1, -1, 2, 1, -2, -1, 1, -1, -1, -1, 2, -1, -2, -2, 2,
            2, 0, -1, -1, -2, 0, -1, 0, 1, 2, -2, 0, 2, 2, 1, 0, -1, -1, 0, -2, 2, 2, -2, 2, 1, -1,
            -2, -1, -2, -1, 1, 2, 2, -1, 0, 1, 2, -1, 0, 0, 0, 1, 1, -1, -1, -1, -2, 2, 0, -2, 0,
            2, -1, 1, 1, 2, -2, 2, -2, 1, 0, -2, 1, 0, 0, -2, -2, 2, 2, -2, -1, 2, -2, 1, 0, 0, -1,
            0, -2, 2, -1, -2, 2, -1, 1, -2, -1, 0, -2, 2, 1, 2, 2, 2, 0, 2, 2, 2, 0, 2, 2, 2, -1,
            -2, 1, 1, 0, -2, 1, 0, 0, -2, 1, -2, -1, 2, 0, 0, 2, 0, -2, -1, -1, 2, 2, -1, -1, -1,
            -2, -2, -1, -2, 2, -2, 0, 1, 0, -2, -2, 2, 0, 1, 0, 0, -2, -1, 1, -1, 1, -1, -1, -1, 2,
            2, 0,
        ];

        assert_eq!(
            sample_error_ring_element::<2>(seed).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_sample_error_ring_element_when_eta_is_4() {
        let seed: [u8; 66] = [
            236, 4, 148, 239, 41, 178, 188, 226, 130, 212, 6, 144, 208, 180, 180, 105, 47, 148, 75,
            195, 181, 177, 5, 140, 204, 68, 24, 132, 169, 19, 68, 118, 67, 203, 13, 152, 29, 194,
            235, 123, 101, 109, 162, 137, 198, 164, 97, 247, 11, 44, 34, 49, 235, 251, 243, 177,
            213, 141, 65, 232, 136, 163, 85, 54, 10, 0,
        ];

        let expected_coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT] = [
            2, -4, 2, -2, 1, 2, 4, 2, 4, -1, -4, 3, 2, 4, -1, 2, -3, 3, 1, -2, 0, 3, -2, 3, 4, 1,
            -3, -2, 0, -4, -1, -4, 3, -4, 0, -3, -2, -3, 2, -3, -3, 3, -4, -3, -4, 1, -2, 4, -3, 4,
            4, 1, -3, -3, 4, 0, -2, 2, 4, -4, 4, -4, -1, -3, 4, 3, 2, -1, 3, -2, -2, -4, -1, -1, 4,
            1, 4, 0, 3, 4, -1, -3, 4, -4, 4, 1, -3, 0, -4, 2, 1, 4, -1, 0, -2, -2, -3, 3, -3, 4, 3,
            2, -2, -2, -1, 2, -1, -4, 3, 0, -2, 4, -1, 0, 4, -2, 4, -3, 2, -4, 2, 3, 3, 2, -4, 2,
            0, -2, 1, -4, 0, -4, -3, 2, 0, -2, -4, 1, 2, 3, 4, -4, 2, 2, 1, -4, 0, -4, -3, -2, -2,
            -2, -1, 1, 4, 1, 0, -2, 2, 1, 4, -4, -1, 0, -1, -3, 2, 1, 3, 3, 4, -2, -2, 3, 1, 3, 3,
            -4, -2, -1, -4, -3, 4, 1, 2, -3, -1, 3, 4, -3, 0, -1, -1, -4, -2, 1, -2, 3, -1, -2, 2,
            -1, -2, 0, -2, 2, 3, 3, 2, 3, 4, 3, -3, -4, 1, 4, -3, 2, 0, -4, 4, -4, 2, 4, -2, -3,
            -4, 3, 0, 1, -2, 2, -1, 4, 4, 0, -1, 1, 4, -2, -3, 2, -2, 4, 2, 1, 1, 1, -3, -2, -2, 2,
            2, -4, -1, 1,
        ];

        assert_eq!(
            sample_error_ring_element::<4>(seed).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_sample_challenge_ring_element_when_tau_is_39() {
        let seed: [u8; 32] = [
            3, 9, 159, 119, 236, 6, 207, 7, 103, 108, 187, 137, 222, 35, 37, 30, 79, 224, 204, 186,
            41, 38, 148, 188, 201, 50, 105, 155, 129, 217, 124, 57,
        ];

        let expected_coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT] = [
            0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1,
            -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1,
            -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 0, -1, 1, 0, 0, 1,
            0, 0, 0, 1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1,
            0,
        ];

        assert_eq!(
            sample_challenge_ring_element::<39>(seed).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_sample_challenge_ring_element_when_tau_is_49() {
        let seed: [u8; 32] = [
            147, 7, 165, 152, 200, 20, 4, 38, 107, 110, 111, 176, 108, 84, 109, 201, 232, 125, 52,
            83, 160, 120, 106, 44, 76, 41, 76, 144, 8, 184, 4, 74,
        ];

        let expected_coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT] = [
            0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -1, -1, 0,
            1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
            -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            -1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
            0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
            -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0,
            -1, 0, -1, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0,
            0, -1, 0, 0, 0,
        ];

        assert_eq!(
            sample_challenge_ring_element::<49>(seed).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_sample_challenge_ring_element_when_tau_is_60() {
        let seed: [u8; 32] = [
            188, 193, 17, 175, 172, 179, 13, 23, 90, 238, 237, 230, 143, 113, 24, 65, 250, 86, 234,
            229, 251, 57, 199, 158, 9, 4, 102, 249, 11, 68, 140, 107,
        ];

        let expected_coefficients: [i32; COEFFICIENTS_IN_RING_ELEMENT] = [
            0, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0,
            0, 0, 1, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1,
            0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
            0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1,
            0, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
            0, 1, 0, -1, 1, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 1, -1, 0,
            0, 0, 0, 1, -1, 0,
        ];

        assert_eq!(
            sample_challenge_ring_element::<60>(seed).coefficients,
            expected_coefficients
        );
    }
}
