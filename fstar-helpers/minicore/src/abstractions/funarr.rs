#[hax_lib::fstar::replace(
    r#"
open FStar.Tactics

let ${_pointwise_apply_mk_term} #t
  (max: nat)
  (f: (n:nat {n < max}) -> t)
  : Tac unit
  = let rec brs (n:int): Tac _ =
      if n < 0 then []
      else
        let c = C_Int n in
        let p = Pat_Constant c in
        (p, mk_e_app (quote f) [pack (Tv_Const c)])::brs (n - 1)
    in
    let bd = fresh_binder_named "i" (quote (m: nat {m < max})) in
    let t = mk_abs [bd] (Tv_Match bd None (brs (max - 1))) in
    exact t"#
)]
pub fn _pointwise_apply_mk_term() {}

#[hax_lib::fstar::replace(
    r#"
open FStar.FunctionalExtensionality    
type t_FunArray (n: u64) (t: Type0) = i:u64 {v i < v n} ^-> t

let pointwise_apply 
    (v_N: u64) (#v_T: Type0) (f: t_FunArray v_N v_T)
    (#[${_pointwise_apply_mk_term} (v v_N) (fun (i:nat{i < v v_N}) -> f (mk_u64 i))] def: (n: nat {n < v v_N}) -> v_T)
    : t_FunArray v_N v_T
    = on (i: u64 {v i < v v_N}) (fun i -> def (v i))

let ${FunArray::<0, ()>::get} (v_N: u64) (#v_T: Type0) (self: t_FunArray v_N v_T) (i: u64 {v i < v v_N}) : v_T = 
    self i

let ${FunArray::<0, ()>::from_fn::<fn(u64)->()>}
    (v_N: u64)
    (#v_T: Type0)
    (f: (i: u64 {v i < v v_N}) -> v_T)
    : t_FunArray v_N v_T = on (i: u64 {v i < v v_N}) f

let ${FunArray::<0, ()>::as_vec} n #t (self: t_FunArray n t) = FStar.Seq.init (v n) (fun i -> self (mk_u64 i))

let rec ${FunArray::<0, ()>::fold::<()>} n #t #a (arr: t_FunArray n t) (init: a) (f: a -> t -> a): Tot a (decreases (v n)) = 
    match n with
    | MkInt 0 -> init
    | MkInt n -> 
        let acc: a = f init (arr (mk_u64 0)) in 
        let n = MkInt (n - 1) in
        ${FunArray::<0, ()>::fold::<()>}  n #t #a
                      (${FunArray::<0, ()>::from_fn::<fn(u64)->()>} n (fun i -> arr (i +. mk_u64 1)))
                      acc f
"#
)]
#[derive(Copy, Clone, Eq, PartialEq)]
// pub struct FunArray<const N: usize, T>([T; N]);
pub struct FunArray<const N: u64, T>([Option<T>; 512]);

#[hax_lib::exclude]
impl<const N: u64, T> FunArray<N, T> {
    pub fn pointwise_apply(self) -> FunArray<N, T> {
        self
    }

    pub fn get(&self, i: u64) -> &T {
        &self.0[i as usize].as_ref().unwrap()
    }
    /// Constructor for BitVec. `BitVec::<N>::from_fn` constructs a bitvector out of a function that takes usizes smaller than `N` and produces bits.
    pub fn from_fn<F: Fn(u64) -> T>(f: F) -> Self {
        // let vec = (0..N).map(f).collect();
        let arr = core::array::from_fn(|i| {
            if (i as u64) < N {
                Some(f(i as u64))
            } else {
                None
            }
        });
        Self(arr)
    }
    pub fn as_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.0[0..(N as usize)]
            .iter()
            .cloned()
            .map(|x| x.unwrap())
            .collect()
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

#[hax_lib::exclude]
impl<const N: u64, T: Clone> TryFrom<Vec<T>> for FunArray<N, T> {
    type Error = ();
    fn try_from(v: Vec<T>) -> Result<Self, ()> {
        if (v.len() as u64) < N {
            Err(())
        } else {
            Ok(Self::from_fn(|i| v[i as usize].clone()))
        }
    }
}

#[hax_lib::exclude]
impl<const N: u64, T: core::fmt::Debug + Clone> core::fmt::Debug for FunArray<N, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.as_vec())
    }
}

#[hax_lib::attributes]
impl<const N: u64, T> core::ops::Index<u64> for FunArray<N, T> {
    type Output = T;
    #[requires(index < N)]
    fn index(&self, index: u64) -> &Self::Output {
        self.get(index)
    }
}

// impl<const N: u64, T> AsRef<[T]> for FunArray<N, T> {
//     fn as_ref(&self) -> &[T] {
//         self.as_slice()
//     }
// }
