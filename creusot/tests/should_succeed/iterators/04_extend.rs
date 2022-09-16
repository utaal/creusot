#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{iter::*, std::*, *};

#[ensures(exists<f : I, p : _> i.produces(p, f) && f.completed() && (@^v) == (@v).concat(p))]
fn extend<T, I: Iterator<Item = T>>(v: &mut Vec<T>, i: I)
where
    I: iter::IteratorSpec,
{
    let old_v = ghost! { v };
    #[invariant(proph_const, ^*old_v == ^v)]
    #[invariant(x, (@v).ext_eq((@old_v).concat(*produced)))]
    for x in i {
        v.push(x);
    }
}

#[ensures((@^v).ext_eq((@v).concat(@w)))]
fn concat<T>(v: &mut Vec<T>, w: Vec<T>) {
    extend(v, w.into_iter());
}

// Short-circuiting
#[ensures(result == true ==> (^iter).completed())]
// If true, then post condition holds w result true for every element
// If false, there exists an element where it returned false
#[ensures(
    exists<p : _ > iter.produces(p, ^iter) &&
      result == true ==> (forall<i : _> 0 <= i && i < p.len() ==> exists<f2 : F> f.invariant(f2) && f2.postcondition_mut(p[i], true)) &&
      result == false ==> (exists<i : _> 0 <= i && i < p.len() ==> exists<f2 : F> f.invariant(f2) && f2.postcondition_mut(p[i], false) )
)]
fn all<I: IteratorSpec, F: FnMut(I::Item) -> bool>(iter: &mut I, f: F) -> bool {
    let mut all = true;

    #[invariant(dummy, true)]
    for x in i {
        all = all && (f)(x)
    }

    all
}

// struct Extend<I, J> { first: I, second: J }

// fn extend<I : Iterator, J : Iterator<Item = I::Item>>(self_ : I, other: J) -> Extend<I, J> {
//   Extend { first: self_, second: other }
// }
