use crate::{
    arithmetic::PolynomialRingElement,
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    hash_functions::XOF,
};

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

            if potential_coefficient < FIELD_MODULUS && *sampled < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[*sampled] = potential_coefficient;
                *sampled += 1;
            }

            if *sampled == COEFFICIENTS_IN_RING_ELEMENT {
                done = true;
            }
        }
    }

    done
}
#[allow(non_snake_case)]
pub(crate) fn sample_ring_element_uniform(seed: [u8; 34]) -> PolynomialRingElement {
    let mut state = XOF::new(seed);
    let randomness = XOF::squeeze_first_five_blocks(&mut state);

    let mut out = PolynomialRingElement::ZERO;

    let mut sampled = 0;
    let mut done = rejection_sample_less_than_field_modulus(&randomness, &mut sampled, &mut out);

    while !done {
        let randomness = XOF::squeeze_next_block(&mut state);
        done = rejection_sample_less_than_field_modulus(&randomness, &mut sampled, &mut out);
    }

    out
}

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

            if try_0 < (2 * 4) + 1 && *sampled < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[*sampled] = 4 - (try_0 as i32);
                *sampled += 1;
            }

            if try_1 < (2 * 4) + 1 && *sampled < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[*sampled] = 4 - (try_1 as i32);
                *sampled += 1;
            }

            if *sampled == COEFFICIENTS_IN_RING_ELEMENT {
                done = true;
            }
        }
    }

    done
}
#[allow(non_snake_case)]
pub(crate) fn sample_error_ring_element_uniform(seed: [u8; 34]) -> PolynomialRingElement {
    let mut state = XOF::new(seed);
    let randomness = XOF::squeeze_next_block(&mut state);

    let mut out = PolynomialRingElement::ZERO;

    let mut sampled = 0;
    let mut done = rejection_sample_less_than_eta_equals_4(&randomness, &mut sampled, &mut out);

    while !done {
        let randomness = XOF::squeeze_next_block(&mut state);
        done = rejection_sample_less_than_eta_equals_4(&randomness, &mut sampled, &mut out);
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::arithmetic::FieldElement;

    #[allow(non_snake_case)]
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
}