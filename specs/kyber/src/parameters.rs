pub(crate) const Q : u16 = 3329;
pub(crate) const N : usize = 256;
pub(crate) const REJECTION_SAMPLING_BYTES : usize = N * 3 * 3;
pub(crate) const L : usize = 12;
pub(crate) const ETA : usize = 2;
pub(crate) const K : usize = 3;
pub(crate) const CPA_PKE_PUBLIC_KEY_BYTES : usize = (12 * K * N)/8 + 32; //1184
pub(crate) const CPA_PKE_SECRET_KEY_BYTES : usize = (12 * K * N)/8; //1152
