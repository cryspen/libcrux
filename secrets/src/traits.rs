/// A trait for public types that can be classified into secret types
pub trait Classify {
    type Classified;
    fn classify(self) -> Self::Classified;
}

/// A trait for classifying immutable references to public types
pub trait ClassifyRef {
    type ClassifiedRef;
    fn classify_ref(self) -> Self::ClassifiedRef;
}

/// A trait for declassifying secret types into public types
pub trait Declassify {
    type Declassified;
    fn declassify(self) -> Self::Declassified;
}

/// A trait for declassifying references to secret types
pub trait DeclassifyRef {
    type DeclassifiedRef;
    fn declassify_ref(self) -> Self::DeclassifiedRef;
}

/// A trait for classifying mutable references to public types
pub trait ClassifyRefMut {
    type ClassifiedRefMut;
    fn classify_ref_mut(self) -> Self::ClassifiedRefMut;
}

/// A trait for declassifying mutable references to secret types
pub trait DeclassifyRefMut {
    type DeclassifiedRefMut;
    fn declassify_ref_mut(self) -> Self::DeclassifiedRefMut;
}

/// Marker trait for scalar types (machine integers)
pub trait Scalar: Copy {}

impl Scalar for u8 {}
impl Scalar for u16 {}
impl Scalar for u32 {}
impl Scalar for u64 {}
#[cfg(not(eurydice))]
impl Scalar for u128 {}

impl Scalar for i8 {}
impl Scalar for i16 {}
impl Scalar for i32 {}
impl Scalar for i64 {}
#[cfg(not(eurydice))]
impl Scalar for i128 {}

/// A trait for integer operations provided by Rust for machine integers
pub trait IntOps
where
    Self: Sized,
{
    fn wrapping_add<T: Into<Self>>(self, rhs: T) -> Self;
    fn wrapping_sub<T: Into<Self>>(self, rhs: T) -> Self;
    fn wrapping_mul<T: Into<Self>>(self, rhs: T) -> Self;
    fn rotate_left(self, rhs: u32) -> Self;
    fn rotate_right(self, rhs: u32) -> Self;
}

/// A trait for byte conversion operations provided by Rust for machine integers
pub trait EncodeOps<T, const N: usize> {
    fn to_le_bytes(&self) -> [T; N];
    fn to_be_bytes(&self) -> [T; N];

    fn from_le_bytes(x: [T; N]) -> Self;
    fn from_be_bytes(x: [T; N]) -> Self;
}

// SIMD values are also scalars
#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m128i {}

#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m256i {}

#[cfg(target_arch = "x86")]
impl Scalar for core::arch::x86::__m256 {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m128i {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m256i {}

#[cfg(target_arch = "x86_64")]
impl Scalar for core::arch::x86_64::__m256 {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int8x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int8x16_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int16x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int16x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int32x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int32x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int64x1_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::int64x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint8x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint8x16_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint16x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint16x8_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint32x2_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint32x4_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint64x1_t {}

#[cfg(target_arch = "aarch64")]
impl Scalar for core::arch::aarch64::uint64x2_t {}

/// Best effort constant time swapping of values.
pub trait Swap {
    /// Depending on `selector`, keep everything as is, or swap `self` and `other`.
    ///
    /// If `selector == 0`, the values are unchanged, otherwise swap.
    fn cswap(&mut self, other: &mut Self, selector: u8);
}

/// Best effort constant time selection of values.
pub trait Select {
    /// Select `self` or `other`, depending on `selector`.
    /// The selected value will be in `self`.
    ///
    /// If `selector != 0`, select `other`, otherwise
    /// `self` is unchanged.
    fn select(&mut self, other: &Self, selector: u8);
}
