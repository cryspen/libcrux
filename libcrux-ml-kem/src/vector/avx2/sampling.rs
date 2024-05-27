use super::{
    super::traits::FIELD_MODULUS,
    serialize::{deserialize_12, serialize_1},
    *,
};

// XXX: Eurydice can't handle the multi-dimensional array. So we construct it in
//      two steps.
const REJECTION_SAMPLE_SHUFFLE_TABLE0: [u8; 16] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE1: [u8; 16] = [
    0, 1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE2: [u8; 16] = [
    2, 3, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE3: [u8; 16] = [
    0, 1, 2, 3, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE4: [u8; 16] = [
    4, 5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE5: [u8; 16] = [
    0, 1, 4, 5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE6: [u8; 16] = [
    2, 3, 4, 5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE7: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE8: [u8; 16] = [
    6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE9: [u8; 16] = [
    0, 1, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE10: [u8; 16] = [
    2, 3, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE11: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE12: [u8; 16] = [
    4, 5, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE13: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE14: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE15: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE16: [u8; 16] = [
    8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE17: [u8; 16] = [
    0, 1, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE18: [u8; 16] = [
    2, 3, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE19: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE20: [u8; 16] = [
    4, 5, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE21: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE22: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE23: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE24: [u8; 16] = [
    6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE25: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE26: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE27: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE28: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE29: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE30: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE31: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE32: [u8; 16] = [
    10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE33: [u8; 16] = [
    0, 1, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE34: [u8; 16] = [
    2, 3, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE35: [u8; 16] = [
    0, 1, 2, 3, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE36: [u8; 16] = [
    4, 5, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE37: [u8; 16] = [
    0, 1, 4, 5, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE38: [u8; 16] = [
    2, 3, 4, 5, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE39: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE40: [u8; 16] = [
    6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE41: [u8; 16] = [
    0, 1, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE42: [u8; 16] = [
    2, 3, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE43: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE44: [u8; 16] = [
    4, 5, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE45: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE46: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE47: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE48: [u8; 16] = [
    8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE49: [u8; 16] = [
    0, 1, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE50: [u8; 16] = [
    2, 3, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE51: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE52: [u8; 16] = [
    4, 5, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE53: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE54: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE55: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE56: [u8; 16] = [
    6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE57: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE58: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE59: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE60: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE61: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE62: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE63: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0xff, 0xff, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE64: [u8; 16] = [
    12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE65: [u8; 16] = [
    0, 1, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE66: [u8; 16] = [
    2, 3, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE67: [u8; 16] = [
    0, 1, 2, 3, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE68: [u8; 16] = [
    4, 5, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE69: [u8; 16] = [
    0, 1, 4, 5, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE70: [u8; 16] = [
    2, 3, 4, 5, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE71: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE72: [u8; 16] = [
    6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE73: [u8; 16] = [
    0, 1, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE74: [u8; 16] = [
    2, 3, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE75: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE76: [u8; 16] = [
    4, 5, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE77: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE78: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE79: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE80: [u8; 16] = [
    8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE81: [u8; 16] = [
    0, 1, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE82: [u8; 16] = [
    2, 3, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE83: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE84: [u8; 16] = [
    4, 5, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE85: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE86: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE87: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE88: [u8; 16] = [
    6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE89: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE90: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE91: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE92: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE93: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE94: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE95: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 0xff, 0xff, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE96: [u8; 16] = [
    10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE97: [u8; 16] = [
    0, 1, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE98: [u8; 16] = [
    2, 3, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE99: [u8; 16] = [
    0, 1, 2, 3, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE100: [u8; 16] = [
    4, 5, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE101: [u8; 16] = [
    0, 1, 4, 5, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE102: [u8; 16] = [
    2, 3, 4, 5, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE103: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE104: [u8; 16] = [
    6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE105: [u8; 16] = [
    0, 1, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE106: [u8; 16] = [
    2, 3, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE107: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE108: [u8; 16] = [
    4, 5, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE109: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE110: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE111: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE112: [u8; 16] = [
    8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE113: [u8; 16] = [
    0, 1, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE114: [u8; 16] = [
    2, 3, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE115: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE116: [u8; 16] = [
    4, 5, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE117: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE118: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE119: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE120: [u8; 16] = [
    6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE121: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE122: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE123: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE124: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE125: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE126: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE127: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE128: [u8; 16] = [
    14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE129: [u8; 16] = [
    0, 1, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE130: [u8; 16] = [
    2, 3, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE131: [u8; 16] = [
    0, 1, 2, 3, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE132: [u8; 16] = [
    4, 5, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE133: [u8; 16] = [
    0, 1, 4, 5, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE134: [u8; 16] = [
    2, 3, 4, 5, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE135: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE136: [u8; 16] = [
    6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE137: [u8; 16] = [
    0, 1, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE138: [u8; 16] = [
    2, 3, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE139: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE140: [u8; 16] = [
    4, 5, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE141: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE142: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE143: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE144: [u8; 16] = [
    8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE145: [u8; 16] = [
    0, 1, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE146: [u8; 16] = [
    2, 3, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE147: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE148: [u8; 16] = [
    4, 5, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE149: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE150: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE151: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE152: [u8; 16] = [
    6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE153: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE154: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE155: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE156: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE157: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE158: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE159: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 0xff, 0xff, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE160: [u8; 16] = [
    10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE161: [u8; 16] = [
    0, 1, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE162: [u8; 16] = [
    2, 3, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE163: [u8; 16] = [
    0, 1, 2, 3, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE164: [u8; 16] = [
    4, 5, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE165: [u8; 16] = [
    0, 1, 4, 5, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE166: [u8; 16] = [
    2, 3, 4, 5, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE167: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE168: [u8; 16] = [
    6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE169: [u8; 16] = [
    0, 1, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE170: [u8; 16] = [
    2, 3, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE171: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE172: [u8; 16] = [
    4, 5, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE173: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE174: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE175: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE176: [u8; 16] = [
    8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE177: [u8; 16] = [
    0, 1, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE178: [u8; 16] = [
    2, 3, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE179: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE180: [u8; 16] = [
    4, 5, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE181: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE182: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE183: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE184: [u8; 16] = [
    6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE185: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE186: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE187: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE188: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE189: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE190: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE191: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE192: [u8; 16] = [
    12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE193: [u8; 16] = [
    0, 1, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE194: [u8; 16] = [
    2, 3, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE195: [u8; 16] = [
    0, 1, 2, 3, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE196: [u8; 16] = [
    4, 5, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE197: [u8; 16] = [
    0, 1, 4, 5, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE198: [u8; 16] = [
    2, 3, 4, 5, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE199: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE200: [u8; 16] = [
    6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE201: [u8; 16] = [
    0, 1, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE202: [u8; 16] = [
    2, 3, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE203: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE204: [u8; 16] = [
    4, 5, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE205: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE206: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE207: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE208: [u8; 16] = [
    8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE209: [u8; 16] = [
    0, 1, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE210: [u8; 16] = [
    2, 3, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE211: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE212: [u8; 16] = [
    4, 5, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE213: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE214: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE215: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE216: [u8; 16] = [
    6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE217: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE218: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE219: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE220: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE221: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE222: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE223: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE224: [u8; 16] = [
    10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE225: [u8; 16] = [
    0, 1, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE226: [u8; 16] = [
    2, 3, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE227: [u8; 16] = [
    0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE228: [u8; 16] = [
    4, 5, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE229: [u8; 16] = [
    0, 1, 4, 5, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE230: [u8; 16] = [
    2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE231: [u8; 16] = [
    0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE232: [u8; 16] = [
    6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE233: [u8; 16] = [
    0, 1, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE234: [u8; 16] = [
    2, 3, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE235: [u8; 16] = [
    0, 1, 2, 3, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE236: [u8; 16] = [
    4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE237: [u8; 16] = [
    0, 1, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE238: [u8; 16] = [
    2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE239: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE240: [u8; 16] = [
    8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE241: [u8; 16] = [
    0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE242: [u8; 16] = [
    2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE243: [u8; 16] = [
    0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE244: [u8; 16] = [
    4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE245: [u8; 16] = [
    0, 1, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE246: [u8; 16] = [
    2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE247: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE248: [u8; 16] = [
    6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE249: [u8; 16] = [
    0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE250: [u8; 16] = [
    2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE251: [u8; 16] =
    [0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE252: [u8; 16] = [
    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff, 0xff, 0xff,
];
const REJECTION_SAMPLE_SHUFFLE_TABLE253: [u8; 16] =
    [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE254: [u8; 16] =
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0xff, 0xff];
const REJECTION_SAMPLE_SHUFFLE_TABLE255: [u8; 16] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

const REJECTION_SAMPLE_SHUFFLE_TABLE: [[u8; 16]; 256] = [
    REJECTION_SAMPLE_SHUFFLE_TABLE0,
    REJECTION_SAMPLE_SHUFFLE_TABLE1,
    REJECTION_SAMPLE_SHUFFLE_TABLE2,
    REJECTION_SAMPLE_SHUFFLE_TABLE3,
    REJECTION_SAMPLE_SHUFFLE_TABLE4,
    REJECTION_SAMPLE_SHUFFLE_TABLE5,
    REJECTION_SAMPLE_SHUFFLE_TABLE6,
    REJECTION_SAMPLE_SHUFFLE_TABLE7,
    REJECTION_SAMPLE_SHUFFLE_TABLE8,
    REJECTION_SAMPLE_SHUFFLE_TABLE9,
    REJECTION_SAMPLE_SHUFFLE_TABLE10,
    REJECTION_SAMPLE_SHUFFLE_TABLE11,
    REJECTION_SAMPLE_SHUFFLE_TABLE12,
    REJECTION_SAMPLE_SHUFFLE_TABLE13,
    REJECTION_SAMPLE_SHUFFLE_TABLE14,
    REJECTION_SAMPLE_SHUFFLE_TABLE15,
    REJECTION_SAMPLE_SHUFFLE_TABLE16,
    REJECTION_SAMPLE_SHUFFLE_TABLE17,
    REJECTION_SAMPLE_SHUFFLE_TABLE18,
    REJECTION_SAMPLE_SHUFFLE_TABLE19,
    REJECTION_SAMPLE_SHUFFLE_TABLE20,
    REJECTION_SAMPLE_SHUFFLE_TABLE21,
    REJECTION_SAMPLE_SHUFFLE_TABLE22,
    REJECTION_SAMPLE_SHUFFLE_TABLE23,
    REJECTION_SAMPLE_SHUFFLE_TABLE24,
    REJECTION_SAMPLE_SHUFFLE_TABLE25,
    REJECTION_SAMPLE_SHUFFLE_TABLE26,
    REJECTION_SAMPLE_SHUFFLE_TABLE27,
    REJECTION_SAMPLE_SHUFFLE_TABLE28,
    REJECTION_SAMPLE_SHUFFLE_TABLE29,
    REJECTION_SAMPLE_SHUFFLE_TABLE30,
    REJECTION_SAMPLE_SHUFFLE_TABLE31,
    REJECTION_SAMPLE_SHUFFLE_TABLE32,
    REJECTION_SAMPLE_SHUFFLE_TABLE33,
    REJECTION_SAMPLE_SHUFFLE_TABLE34,
    REJECTION_SAMPLE_SHUFFLE_TABLE35,
    REJECTION_SAMPLE_SHUFFLE_TABLE36,
    REJECTION_SAMPLE_SHUFFLE_TABLE37,
    REJECTION_SAMPLE_SHUFFLE_TABLE38,
    REJECTION_SAMPLE_SHUFFLE_TABLE39,
    REJECTION_SAMPLE_SHUFFLE_TABLE40,
    REJECTION_SAMPLE_SHUFFLE_TABLE41,
    REJECTION_SAMPLE_SHUFFLE_TABLE42,
    REJECTION_SAMPLE_SHUFFLE_TABLE43,
    REJECTION_SAMPLE_SHUFFLE_TABLE44,
    REJECTION_SAMPLE_SHUFFLE_TABLE45,
    REJECTION_SAMPLE_SHUFFLE_TABLE46,
    REJECTION_SAMPLE_SHUFFLE_TABLE47,
    REJECTION_SAMPLE_SHUFFLE_TABLE48,
    REJECTION_SAMPLE_SHUFFLE_TABLE49,
    REJECTION_SAMPLE_SHUFFLE_TABLE50,
    REJECTION_SAMPLE_SHUFFLE_TABLE51,
    REJECTION_SAMPLE_SHUFFLE_TABLE52,
    REJECTION_SAMPLE_SHUFFLE_TABLE53,
    REJECTION_SAMPLE_SHUFFLE_TABLE54,
    REJECTION_SAMPLE_SHUFFLE_TABLE55,
    REJECTION_SAMPLE_SHUFFLE_TABLE56,
    REJECTION_SAMPLE_SHUFFLE_TABLE57,
    REJECTION_SAMPLE_SHUFFLE_TABLE58,
    REJECTION_SAMPLE_SHUFFLE_TABLE59,
    REJECTION_SAMPLE_SHUFFLE_TABLE60,
    REJECTION_SAMPLE_SHUFFLE_TABLE61,
    REJECTION_SAMPLE_SHUFFLE_TABLE62,
    REJECTION_SAMPLE_SHUFFLE_TABLE63,
    REJECTION_SAMPLE_SHUFFLE_TABLE64,
    REJECTION_SAMPLE_SHUFFLE_TABLE65,
    REJECTION_SAMPLE_SHUFFLE_TABLE66,
    REJECTION_SAMPLE_SHUFFLE_TABLE67,
    REJECTION_SAMPLE_SHUFFLE_TABLE68,
    REJECTION_SAMPLE_SHUFFLE_TABLE69,
    REJECTION_SAMPLE_SHUFFLE_TABLE70,
    REJECTION_SAMPLE_SHUFFLE_TABLE71,
    REJECTION_SAMPLE_SHUFFLE_TABLE72,
    REJECTION_SAMPLE_SHUFFLE_TABLE73,
    REJECTION_SAMPLE_SHUFFLE_TABLE74,
    REJECTION_SAMPLE_SHUFFLE_TABLE75,
    REJECTION_SAMPLE_SHUFFLE_TABLE76,
    REJECTION_SAMPLE_SHUFFLE_TABLE77,
    REJECTION_SAMPLE_SHUFFLE_TABLE78,
    REJECTION_SAMPLE_SHUFFLE_TABLE79,
    REJECTION_SAMPLE_SHUFFLE_TABLE80,
    REJECTION_SAMPLE_SHUFFLE_TABLE81,
    REJECTION_SAMPLE_SHUFFLE_TABLE82,
    REJECTION_SAMPLE_SHUFFLE_TABLE83,
    REJECTION_SAMPLE_SHUFFLE_TABLE84,
    REJECTION_SAMPLE_SHUFFLE_TABLE85,
    REJECTION_SAMPLE_SHUFFLE_TABLE86,
    REJECTION_SAMPLE_SHUFFLE_TABLE87,
    REJECTION_SAMPLE_SHUFFLE_TABLE88,
    REJECTION_SAMPLE_SHUFFLE_TABLE89,
    REJECTION_SAMPLE_SHUFFLE_TABLE90,
    REJECTION_SAMPLE_SHUFFLE_TABLE91,
    REJECTION_SAMPLE_SHUFFLE_TABLE92,
    REJECTION_SAMPLE_SHUFFLE_TABLE93,
    REJECTION_SAMPLE_SHUFFLE_TABLE94,
    REJECTION_SAMPLE_SHUFFLE_TABLE95,
    REJECTION_SAMPLE_SHUFFLE_TABLE96,
    REJECTION_SAMPLE_SHUFFLE_TABLE97,
    REJECTION_SAMPLE_SHUFFLE_TABLE98,
    REJECTION_SAMPLE_SHUFFLE_TABLE99,
    REJECTION_SAMPLE_SHUFFLE_TABLE100,
    REJECTION_SAMPLE_SHUFFLE_TABLE101,
    REJECTION_SAMPLE_SHUFFLE_TABLE102,
    REJECTION_SAMPLE_SHUFFLE_TABLE103,
    REJECTION_SAMPLE_SHUFFLE_TABLE104,
    REJECTION_SAMPLE_SHUFFLE_TABLE105,
    REJECTION_SAMPLE_SHUFFLE_TABLE106,
    REJECTION_SAMPLE_SHUFFLE_TABLE107,
    REJECTION_SAMPLE_SHUFFLE_TABLE108,
    REJECTION_SAMPLE_SHUFFLE_TABLE109,
    REJECTION_SAMPLE_SHUFFLE_TABLE110,
    REJECTION_SAMPLE_SHUFFLE_TABLE111,
    REJECTION_SAMPLE_SHUFFLE_TABLE112,
    REJECTION_SAMPLE_SHUFFLE_TABLE113,
    REJECTION_SAMPLE_SHUFFLE_TABLE114,
    REJECTION_SAMPLE_SHUFFLE_TABLE115,
    REJECTION_SAMPLE_SHUFFLE_TABLE116,
    REJECTION_SAMPLE_SHUFFLE_TABLE117,
    REJECTION_SAMPLE_SHUFFLE_TABLE118,
    REJECTION_SAMPLE_SHUFFLE_TABLE119,
    REJECTION_SAMPLE_SHUFFLE_TABLE120,
    REJECTION_SAMPLE_SHUFFLE_TABLE121,
    REJECTION_SAMPLE_SHUFFLE_TABLE122,
    REJECTION_SAMPLE_SHUFFLE_TABLE123,
    REJECTION_SAMPLE_SHUFFLE_TABLE124,
    REJECTION_SAMPLE_SHUFFLE_TABLE125,
    REJECTION_SAMPLE_SHUFFLE_TABLE126,
    REJECTION_SAMPLE_SHUFFLE_TABLE127,
    REJECTION_SAMPLE_SHUFFLE_TABLE128,
    REJECTION_SAMPLE_SHUFFLE_TABLE129,
    REJECTION_SAMPLE_SHUFFLE_TABLE130,
    REJECTION_SAMPLE_SHUFFLE_TABLE131,
    REJECTION_SAMPLE_SHUFFLE_TABLE132,
    REJECTION_SAMPLE_SHUFFLE_TABLE133,
    REJECTION_SAMPLE_SHUFFLE_TABLE134,
    REJECTION_SAMPLE_SHUFFLE_TABLE135,
    REJECTION_SAMPLE_SHUFFLE_TABLE136,
    REJECTION_SAMPLE_SHUFFLE_TABLE137,
    REJECTION_SAMPLE_SHUFFLE_TABLE138,
    REJECTION_SAMPLE_SHUFFLE_TABLE139,
    REJECTION_SAMPLE_SHUFFLE_TABLE140,
    REJECTION_SAMPLE_SHUFFLE_TABLE141,
    REJECTION_SAMPLE_SHUFFLE_TABLE142,
    REJECTION_SAMPLE_SHUFFLE_TABLE143,
    REJECTION_SAMPLE_SHUFFLE_TABLE144,
    REJECTION_SAMPLE_SHUFFLE_TABLE145,
    REJECTION_SAMPLE_SHUFFLE_TABLE146,
    REJECTION_SAMPLE_SHUFFLE_TABLE147,
    REJECTION_SAMPLE_SHUFFLE_TABLE148,
    REJECTION_SAMPLE_SHUFFLE_TABLE149,
    REJECTION_SAMPLE_SHUFFLE_TABLE150,
    REJECTION_SAMPLE_SHUFFLE_TABLE151,
    REJECTION_SAMPLE_SHUFFLE_TABLE152,
    REJECTION_SAMPLE_SHUFFLE_TABLE153,
    REJECTION_SAMPLE_SHUFFLE_TABLE154,
    REJECTION_SAMPLE_SHUFFLE_TABLE155,
    REJECTION_SAMPLE_SHUFFLE_TABLE156,
    REJECTION_SAMPLE_SHUFFLE_TABLE157,
    REJECTION_SAMPLE_SHUFFLE_TABLE158,
    REJECTION_SAMPLE_SHUFFLE_TABLE159,
    REJECTION_SAMPLE_SHUFFLE_TABLE160,
    REJECTION_SAMPLE_SHUFFLE_TABLE161,
    REJECTION_SAMPLE_SHUFFLE_TABLE162,
    REJECTION_SAMPLE_SHUFFLE_TABLE163,
    REJECTION_SAMPLE_SHUFFLE_TABLE164,
    REJECTION_SAMPLE_SHUFFLE_TABLE165,
    REJECTION_SAMPLE_SHUFFLE_TABLE166,
    REJECTION_SAMPLE_SHUFFLE_TABLE167,
    REJECTION_SAMPLE_SHUFFLE_TABLE168,
    REJECTION_SAMPLE_SHUFFLE_TABLE169,
    REJECTION_SAMPLE_SHUFFLE_TABLE170,
    REJECTION_SAMPLE_SHUFFLE_TABLE171,
    REJECTION_SAMPLE_SHUFFLE_TABLE172,
    REJECTION_SAMPLE_SHUFFLE_TABLE173,
    REJECTION_SAMPLE_SHUFFLE_TABLE174,
    REJECTION_SAMPLE_SHUFFLE_TABLE175,
    REJECTION_SAMPLE_SHUFFLE_TABLE176,
    REJECTION_SAMPLE_SHUFFLE_TABLE177,
    REJECTION_SAMPLE_SHUFFLE_TABLE178,
    REJECTION_SAMPLE_SHUFFLE_TABLE179,
    REJECTION_SAMPLE_SHUFFLE_TABLE180,
    REJECTION_SAMPLE_SHUFFLE_TABLE181,
    REJECTION_SAMPLE_SHUFFLE_TABLE182,
    REJECTION_SAMPLE_SHUFFLE_TABLE183,
    REJECTION_SAMPLE_SHUFFLE_TABLE184,
    REJECTION_SAMPLE_SHUFFLE_TABLE185,
    REJECTION_SAMPLE_SHUFFLE_TABLE186,
    REJECTION_SAMPLE_SHUFFLE_TABLE187,
    REJECTION_SAMPLE_SHUFFLE_TABLE188,
    REJECTION_SAMPLE_SHUFFLE_TABLE189,
    REJECTION_SAMPLE_SHUFFLE_TABLE190,
    REJECTION_SAMPLE_SHUFFLE_TABLE191,
    REJECTION_SAMPLE_SHUFFLE_TABLE192,
    REJECTION_SAMPLE_SHUFFLE_TABLE193,
    REJECTION_SAMPLE_SHUFFLE_TABLE194,
    REJECTION_SAMPLE_SHUFFLE_TABLE195,
    REJECTION_SAMPLE_SHUFFLE_TABLE196,
    REJECTION_SAMPLE_SHUFFLE_TABLE197,
    REJECTION_SAMPLE_SHUFFLE_TABLE198,
    REJECTION_SAMPLE_SHUFFLE_TABLE199,
    REJECTION_SAMPLE_SHUFFLE_TABLE200,
    REJECTION_SAMPLE_SHUFFLE_TABLE201,
    REJECTION_SAMPLE_SHUFFLE_TABLE202,
    REJECTION_SAMPLE_SHUFFLE_TABLE203,
    REJECTION_SAMPLE_SHUFFLE_TABLE204,
    REJECTION_SAMPLE_SHUFFLE_TABLE205,
    REJECTION_SAMPLE_SHUFFLE_TABLE206,
    REJECTION_SAMPLE_SHUFFLE_TABLE207,
    REJECTION_SAMPLE_SHUFFLE_TABLE208,
    REJECTION_SAMPLE_SHUFFLE_TABLE209,
    REJECTION_SAMPLE_SHUFFLE_TABLE210,
    REJECTION_SAMPLE_SHUFFLE_TABLE211,
    REJECTION_SAMPLE_SHUFFLE_TABLE212,
    REJECTION_SAMPLE_SHUFFLE_TABLE213,
    REJECTION_SAMPLE_SHUFFLE_TABLE214,
    REJECTION_SAMPLE_SHUFFLE_TABLE215,
    REJECTION_SAMPLE_SHUFFLE_TABLE216,
    REJECTION_SAMPLE_SHUFFLE_TABLE217,
    REJECTION_SAMPLE_SHUFFLE_TABLE218,
    REJECTION_SAMPLE_SHUFFLE_TABLE219,
    REJECTION_SAMPLE_SHUFFLE_TABLE220,
    REJECTION_SAMPLE_SHUFFLE_TABLE221,
    REJECTION_SAMPLE_SHUFFLE_TABLE222,
    REJECTION_SAMPLE_SHUFFLE_TABLE223,
    REJECTION_SAMPLE_SHUFFLE_TABLE224,
    REJECTION_SAMPLE_SHUFFLE_TABLE225,
    REJECTION_SAMPLE_SHUFFLE_TABLE226,
    REJECTION_SAMPLE_SHUFFLE_TABLE227,
    REJECTION_SAMPLE_SHUFFLE_TABLE228,
    REJECTION_SAMPLE_SHUFFLE_TABLE229,
    REJECTION_SAMPLE_SHUFFLE_TABLE230,
    REJECTION_SAMPLE_SHUFFLE_TABLE231,
    REJECTION_SAMPLE_SHUFFLE_TABLE232,
    REJECTION_SAMPLE_SHUFFLE_TABLE233,
    REJECTION_SAMPLE_SHUFFLE_TABLE234,
    REJECTION_SAMPLE_SHUFFLE_TABLE235,
    REJECTION_SAMPLE_SHUFFLE_TABLE236,
    REJECTION_SAMPLE_SHUFFLE_TABLE237,
    REJECTION_SAMPLE_SHUFFLE_TABLE238,
    REJECTION_SAMPLE_SHUFFLE_TABLE239,
    REJECTION_SAMPLE_SHUFFLE_TABLE240,
    REJECTION_SAMPLE_SHUFFLE_TABLE241,
    REJECTION_SAMPLE_SHUFFLE_TABLE242,
    REJECTION_SAMPLE_SHUFFLE_TABLE243,
    REJECTION_SAMPLE_SHUFFLE_TABLE244,
    REJECTION_SAMPLE_SHUFFLE_TABLE245,
    REJECTION_SAMPLE_SHUFFLE_TABLE246,
    REJECTION_SAMPLE_SHUFFLE_TABLE247,
    REJECTION_SAMPLE_SHUFFLE_TABLE248,
    REJECTION_SAMPLE_SHUFFLE_TABLE249,
    REJECTION_SAMPLE_SHUFFLE_TABLE250,
    REJECTION_SAMPLE_SHUFFLE_TABLE251,
    REJECTION_SAMPLE_SHUFFLE_TABLE252,
    REJECTION_SAMPLE_SHUFFLE_TABLE253,
    REJECTION_SAMPLE_SHUFFLE_TABLE254,
    REJECTION_SAMPLE_SHUFFLE_TABLE255,
];

#[inline(always)]
pub(crate) fn rejection_sample(input: &[u8], output: &mut [i16]) -> usize {
    let field_modulus = mm256_set1_epi16(FIELD_MODULUS);

    // The input bytes can be interpreted as a sequence of serialized
    // 12-bit (i.e. uncompressed) coefficients. Not all coefficients may be
    // less than FIELD_MODULUS though.
    let potential_coefficients = deserialize_12(input);

    // Suppose we view |potential_coefficients| as follows (grouping 64-bit elements):
    //
    // A B C D | E F G H | ....
    //
    // and A < 3329, D < 3329 and H < 3329, |compare_with_field_modulus| will look like:
    //
    // 0xFF 0 0 0xFF | 0 0 0 0xFF | ...
    let compare_with_field_modulus = mm256_cmpgt_epi16(field_modulus, potential_coefficients);

    // Since every bit in each lane is either 0 or 1, we only need one bit from
    // each lane in the register to tell us what coefficients to keep and what
    // to throw-away. Combine all the bits (there are 16) into two bytes.
    let good = serialize_1(compare_with_field_modulus);

    // Each bit (and its corresponding position) represents an element we
    // want to sample. We'd like all such elements to be next to each other starting
    // at index 0, so that they can be read from the vector easily.
    // |REJECTION_SAMPLE_SHUFFLE_TABLE| encodes the byte-level shuffling indices
    // needed to make this happen.
    //
    // For e.g. if good[0] = 0b0_0_0_0_0_0_1_0, we need to move the element in
    // the 2-nd 16-bit lane to the first. To do this, we need the byte-level
    // shuffle indices to be 2 3 X X X X ...
    let lower_shuffles = REJECTION_SAMPLE_SHUFFLE_TABLE[good[0] as usize];

    // Shuffle the lower 8 16-bits accordingly ...
    let lower_shuffles = mm_loadu_si128(&lower_shuffles);
    let lower_coefficients = mm256_castsi256_si128(potential_coefficients);
    let lower_coefficients = mm_shuffle_epi8(lower_coefficients, lower_shuffles);

    // ... then write them out ...
    mm_storeu_si128(output, lower_coefficients);

    // ... and finally count the number of bits of |good[0]| so we know how many
    // were actually sampled
    let sampled_count = good[0].count_ones() as usize;

    // Do the same for |goood[1]|
    let upper_shuffles = REJECTION_SAMPLE_SHUFFLE_TABLE[good[1] as usize];
    let upper_shuffles = mm_loadu_si128(&upper_shuffles);
    let upper_coefficients = mm256_extracti128_si256::<1>(potential_coefficients);
    let upper_coefficients = mm_shuffle_epi8(upper_coefficients, upper_shuffles);

    mm_storeu_si128(
        &mut output[sampled_count..sampled_count + 8],
        upper_coefficients,
    );

    sampled_count + (good[1].count_ones() as usize)
}
