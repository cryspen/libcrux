use crate::platform::*;

pub struct GF128State<T: GF128FieldElement> {
    accumulator: T,
    r: T,
}

pub fn gf128_init<T: GF128FieldElement>(key: &[u8]) -> GF128State<T> {
    debug_assert!(key.len() == 16);

    GF128State {
        accumulator: T::zero(),
        r: T::load_elem(key),
    }
}

#[inline(always)]
pub fn gf128_update<T: GF128FieldElement>(st: &mut GF128State<T>, block: &[u8]) {
    debug_assert!(block.len() == 16);

    let block_elem = T::load_elem(block);
    st.accumulator.add(&block_elem);
    st.accumulator.mul(&st.r);
}

pub fn gf128_update_blocks<T: GF128FieldElement>(st: &mut GF128State<T>, input: &[u8]) {
    debug_assert!(input.len() % 16 == 0);

    let blocks = input.len() / 16;
    for i in 0..blocks {
        gf128_update(st, &input[i * 16..i * 16 + 16]);
    }
}

pub fn gf128_update_last<T: GF128FieldElement>(st: &mut GF128State<T>, partial_block: &[u8]) {
    debug_assert!(partial_block.len() < 16);

    let mut block = [0u8; 16];
    block[0..partial_block.len()].copy_from_slice(partial_block);
    gf128_update(st, &block);
}

pub fn gf128_update_padded<T: GF128FieldElement>(st: &mut GF128State<T>, input: &[u8]) {
    let blocks = input.len() / 16;
    gf128_update_blocks(st, &input[0..blocks * 16]);

    let last = input.len() - input.len() % 16;
    if last < input.len() {
        gf128_update_last(st, &input[last..]);
    }
}

pub fn gf128_emit<T: GF128FieldElement>(st: &GF128State<T>, out: &mut [u8]) {
    debug_assert!(out.len() == 16);

    st.accumulator.store_elem(out);
}

#[cfg(test)]
mod test {
    use super::*;

    fn gf128<T: GF128FieldElement>(key: &[u8], inp: &[u8], out: &mut [u8]) {
        debug_assert!(key.len() == 16);
        debug_assert!(out.len() == 16);

        let mut st = gf128_init::<T>(key);
        gf128_update_padded(&mut st, inp);
        gf128_emit(&st, out);
    }

    const INPUT: [u8; 132] = [
        0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef, 0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe,
        0xef, 0xab, 0xad, 0xda, 0xd2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x5a, 0x8d, 0xef, 0x2f, 0x0c, 0x9e, 0x53, 0xf1, 0xf7, 0x5d, 0x78, 0x53, 0x65,
        0x9e, 0x2a, 0x20, 0xee, 0xb2, 0xb2, 0x2a, 0xaf, 0xde, 0x64, 0x19, 0xa0, 0x58, 0xab, 0x4f,
        0x6f, 0x74, 0x6b, 0xf4, 0x0f, 0xc0, 0xc3, 0xb7, 0x80, 0xf2, 0x44, 0x45, 0x2d, 0xa3, 0xeb,
        0xf1, 0xc5, 0xd8, 0x2c, 0xde, 0xa2, 0x41, 0x89, 0x97, 0x20, 0x0e, 0xf8, 0x2e, 0x5a, 0x8d,
        0xef, 0x2f, 0x0c, 0x9e, 0x53, 0xf1, 0xf7, 0x5d, 0x78, 0x53, 0x65, 0x9e, 0x2a, 0x20, 0xee,
        0xb2, 0xb2, 0x2a, 0xaf, 0xde, 0x64, 0x19, 0xa0, 0x58, 0xab, 0x4f, 0x6f, 0x74, 0x6b, 0xf4,
        0x0f, 0xc0, 0xc3, 0xb7, 0x80, 0xf2, 0x44, 0x45, 0x44, 0xae, 0x7e, 0x3f,
    ];

    const KEY: [u8; 16] = [
        0xac, 0xbe, 0xf2, 0x05, 0x79, 0xb4, 0xb8, 0xeb, 0xce, 0x88, 0x9b, 0xac, 0x87, 0x32, 0xda,
        0xd7,
    ];

    const EXPECTED: [u8; 16] = [
        0xfb, 0xba, 0xaa, 0x70, 0xa0, 0x73, 0x6f, 0xf9, 0xed, 0x2f, 0xc4, 0x62, 0xde, 0x72, 0x61,
        0xe0,
    ];

    #[test]
    fn test_gf128() {
        let mut computed: [u8; 16] = [0u8; 16];
        gf128::<crate::platform::portable::FieldElement>(&KEY, &INPUT, &mut computed);
        for i in 0..16 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn test_gf128_neon() {
        let mut computed: [u8; 16] = [0u8; 16];
        gf128::<crate::platform::neon::FieldElement>(&KEY, &INPUT, &mut computed);
        for i in 0..16 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }

    #[cfg(all(target_arch = "x86_64"))] // ENABLE: target_feature="aes"
    #[test]
    fn test_gf128_intel() {
        let mut computed: [u8; 16] = [0u8; 16];
        gf128::<crate::platform::intel_ni::FieldElement>(&KEY, &INPUT, &mut computed);
        for i in 0..16 {
            if computed[i] != EXPECTED[i] {
                println!(
                    "mismatch at {}: expected is {}, computed is {}",
                    i, EXPECTED[i], computed[i]
                );
                assert!(false);
            }
        }
    }
}
