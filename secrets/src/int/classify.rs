use crate::traits::*;

// A type for secret scalars
#[repr(transparent)]
pub struct Secret<T>(pub(crate) T);

impl<T: Clone> Clone for Secret<T> {
    fn clone(&self) -> Self {
        Secret(self.0.clone())
    }
}

impl<T: Clone + Copy> Copy for Secret<T> {}

impl<T: Scalar, const N: usize> Classify for [T; N] {
    type Classified = [Secret<T>; N];
    fn classify(self) -> [Secret<T>; N] {
        self.map(|x| x.into())
    }
}

impl<T: Scalar, const N: usize> Declassify for [Secret<T>; N] {
    type Declassified = [T; N];
    fn declassify(self) -> [T; N] {
        self.map(|x| x.0)
    }
}

impl<T: Scalar, const M: usize, const N: usize> Classify for [[T; N]; M] {
    type Classified = [[Secret<T>; N]; M];
    fn classify(self) -> [[Secret<T>; N]; M] {
        self.map(|x| x.map(|y| y.into()))
    }
}

impl<T: Scalar, const N: usize, const M: usize> Declassify for [[Secret<T>; N]; M] {
    type Declassified = [[T; N]; M];
    fn declassify(self) -> [[T; N]; M] {
        self.map(|x| x.map(|y| y.0))
    }
}

impl<'a, T: Scalar> ClassifyRefMut for &'a mut T {
    type Classified = &'a mut Secret<T>;
    fn classify_ref_mut(self) -> &'a mut Secret<T> {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> DeclassifyRefMut for &'a mut Secret<T> {
    type Declassified = &'a mut T;
    fn declassify_ref_mut(self) -> &'a mut T {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> ClassifyRef for &'a [T] {
    type Classified = &'a [Secret<T>];
    fn classify_ref(self) -> &'a [Secret<T>] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> DeclassifyRef for &'a [Secret<T>] {
    type Declassified = &'a [T];
    fn declassify_ref(self) -> &'a [T] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> ClassifyRefMut for &'a mut [T] {
    type Classified = &'a mut [Secret<T>];
    fn classify_ref_mut(self) -> &'a mut [Secret<T>] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar> DeclassifyRefMut for &'a mut [Secret<T>] {
    type Declassified = &'a mut [T];
    fn declassify_ref_mut(self) -> &'a mut [T] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> ClassifyRef for &'a [T; N] {
    type Classified = &'a [Secret<T>; N];
    fn classify_ref(self) -> &'a [Secret<T>; N] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> DeclassifyRef for &'a [Secret<T>; N] {
    type Declassified = &'a [T; N];
    fn declassify_ref(self) -> &'a [T; N] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> ClassifyRefMut for &'a mut [T; N] {
    type Classified = &'a mut [Secret<T>; N];
    fn classify_ref_mut(self) -> &'a mut [Secret<T>; N] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<'a, T: Scalar, const N: usize> DeclassifyRefMut for &'a mut [Secret<T>; N] {
    type Declassified = &'a mut [T; N];
    fn declassify_ref_mut(self) -> &'a mut [T; N] {
        unsafe { core::mem::transmute(self) }
    }
}

impl<T> From<T> for Secret<T> {
    fn from(x: T) -> Secret<T> {
        Secret(x)
    }
}
