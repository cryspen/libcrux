macro_rules! clone {
    ($new:ident = $old:ident) => {
        #[cfg(hax)]
        let $new = $old.clone();
    };
}
pub(crate) use clone;
