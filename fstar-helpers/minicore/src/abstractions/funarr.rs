#[hax_lib::fstar::replace(
    r"
open FStar.FunctionalExtensionality
type t_FunArray (n: usize) (t: Type0) = i:usize {v i < v n} ^-> t

let ${FunArray::<0, ()>::get} (v_N: usize) (#v_T: Type0) (self: t_FunArray v_N v_T) (i: usize {v i < v v_N}) : v_T = 
    self i

let ${FunArray::<0, ()>::from_fn::<fn(usize)->()>}
    (v_N: usize)
    (#v_T: Type0)
    (f: (i: usize {v i < v v_N}) -> v_T)
    : t_FunArray v_N v_T = on (i: usize {v i < v v_N}) f

let ${FunArray::<0, ()>::as_slice} n #t (self: t_FunArray n t) = FStar.Seq.init (v n) (fun i -> self (mk_usize i))

let rec ${FunArray::<0, ()>::fold::<()>} n #t #a (arr: t_FunArray n t) (init: a) (f: a -> t -> a): Tot a (decreases (v n)) = 
    match n with
    | MkInt 0 -> init
    | MkInt n -> 
        let acc: a = f init (arr (mk_usize 0)) in 
        let n = MkInt (n - 1) in
        ${FunArray::<0, ()>::fold::<()>}  n #t #a
                      (impl_6__from_fn n (fun i -> arr (i +. mk_usize 1)))
                      acc f
"
)]
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct FunArray<const N: usize, T>([T; N]);

#[hax_lib::exclude]
impl<const N: usize, T> FunArray<N, T> {
    pub fn get(&self, i: usize) -> &T {
        &self.0[i]
    }
    /// Constructor for BitVec. `BitVec::<N>::from_fn` constructs a bitvector out of a function that takes usizes smaller than `N` and produces bits.
    pub fn from_fn<F: Fn(usize) -> T>(f: F) -> Self {
        Self(core::array::from_fn(f))
    }
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    pub fn fold<A>(&self, mut init: A, f: fn(A, T) -> A) -> A
    where
        T: Clone,
    {
        for i in 0..N {
            init = f(init, self[i].clone());
        }
        init
    }
}

#[hax_lib::attributes]
impl<const N: usize, T> core::ops::Index<usize> for FunArray<N, T> {
    type Output = T;
    #[requires(index < N)]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index)
    }
}

impl<const N: usize, T> AsRef<[T]> for FunArray<N, T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}
