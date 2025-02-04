extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Symmetric {
    #[logic]
    fn op(self, _: Self) -> Self;

    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn reflexive(a: Self, b: Self);
}

#[logic]
#[ensures(result == true)]
pub fn uses_op<T: Symmetric>(x: T, y: T) -> bool {
    pearlite! { x.op(y) == y.op(x) }
}

impl Symmetric for () {
    #[logic]
    fn op(self, _: Self) -> Self {
        ()
    }

    #[law]
    fn reflexive(_: Self, _: Self) {}
}

#[logic]
#[ensures(result == true)]
pub fn impl_laws() -> bool {
    pearlite! { ().op(()) == ().op(()) }
}
