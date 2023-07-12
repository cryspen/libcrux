pub(crate) const NUMBER_OF_COEFFICIENTS : usize = 256;
pub(crate) const Q : u16 = 3329;
pub(crate) const REJECTION_SAMPLING_BYTES : usize = NUMBER_OF_COEFFICIENTS * 3 * 3;
pub(crate) const BITS_PER_COEFFICIENT : usize = 12; // ceil(log_2(Q))
pub(crate) const ETA : usize = 2;
pub(crate) const K : usize = 3;
pub(crate) const CPA_PKE_PUBLIC_KEY_BYTES : usize = (12 * K * NUMBER_OF_COEFFICIENTS)/8 + 32; //1184
pub(crate) const CPA_PKE_SECRET_KEY_BYTES : usize = (12 * K * NUMBER_OF_COEFFICIENTS)/8; //1152

pub(crate) const BITS_PER_RING_ELEMENT : usize = NUMBER_OF_COEFFICIENTS * BITS_PER_COEFFICIENT;
