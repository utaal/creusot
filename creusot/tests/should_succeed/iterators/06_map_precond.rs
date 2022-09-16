#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{std::*, *};

mod common;
use common::*;

pub struct Map<I, A, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,

    produced: Ghost<Seq<A>>,

    init_iter: Ghost<I>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator for Map<I, I::Item, F> {
    type Item = B;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<iter : &mut _> *iter == self.iter && ^iter == (^self).iter && iter.completed()
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            (self.produced.len() + visited.len() == succ.produced.len()
            && succ.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced)
            && self.init_iter == succ.init_iter)
            && self.iter.produces(succ.produced.subsequence(self.produced.len(), succ.produced.len()), succ.iter )
            && exists<fs : Seq<&mut F>>
                fs.len() == visited.len()
                && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                && (visited.len() > 0 ==>
                        * fs[0] == self.func
                    &&  ^ fs[visited.len() - 1] == succ.func)
                && (visited.len() == 0 ==> self.func == succ.func)
                && forall<i : Int> 0 <= i && i < visited.len() ==>
                    fs[i].postcondition_mut((succ.produced[self.produced.len() + i], Ghost(succ.produced.subsequence(0, self.produced.len() + i))), visited[i])
        }
    }

    #[predicate]
    fn invariant(self) -> bool {
        // invariant implies precondition
        pearlite! {
            (forall<initial: Self>
                self.init_iter == initial.init_iter ==>
                initial.produced.len() >= self.produced.len() ==>
                initial.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced) ==>
                self.iter.produces(initial.produced.subsequence(self.produced.len(), initial.produced.len()), initial.iter) ==>
                initial.init_iter.produces(*initial.produced, initial.iter) ==>
                // post condition implies invariant
                forall<i: I, e: I::Item, b: B>
                    initial.iter.produces(Seq::singleton(e), i) ==>
                        forall<f : &mut F> * f == initial.func ==>
                            f.postcondition_mut((e, initial.produced), b) ==>
                                forall<i2: _, e2: _>
                                    i.produces(Seq::singleton(e2), i2) ==>
                                    (^f).precondition((e2, Ghost(initial.produced.push(e))))
            ) &&
            self.init_iter.produces(*self.produced, self.iter) &&
            (forall<e : I::Item, i2 : I>
                self.iter.produces(Seq::singleton(e), i2) ==> self.func.precondition((e, self.produced))
            )
        }
    }

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => self.completed() && self.produces(Seq::EMPTY, ^self),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        let _ = ghost! { {Seq::<I::Item>::left_neutral;} };
        proof_assert!(Self::inv_trans; true);
        let produced = ghost! { *self.produced };
        match self.iter.next() {
            Some(v) => {
                self.produced = ghost! { produced.push(v) };
                Some((self.func)(v, produced))
            }
            None => None,
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Map<I, I::Item, F> {
    #[logic]
    #[requires(a.invariant())]
    #[requires(a.produces(seq, b))]
    #[requires(b.init_iter.produces(*b.produced, b.iter))]
    #[ensures(
        forall<initial: Self>
            b.init_iter == initial.init_iter ==>
            initial.produced.len() >= b.produced.len() ==>
            initial.produced.subsequence(0, b.produced.len()).ext_eq(*b.produced) ==>
            b.iter.produces(initial.produced.subsequence(b.produced.len(), initial.produced.len()), initial.iter) ==>
            initial.init_iter.produces(*initial.produced, initial.iter) ==>
            // post condition implies invariant
            forall<i: I, e: I::Item, b: B>
                initial.iter.produces(Seq::singleton(e), i) ==>
                    forall<f : &mut F> * f == initial.func ==>
                        f.postcondition_mut((e, initial.produced), b) ==>
                            forall<i2: _, e2: _>
                                i.produces(Seq::singleton(e2), i2) ==>
                                (^f).precondition((e2, Ghost(initial.produced.push(e))))

    )]
    fn inv_trans(a: Self, seq: Seq<B>, b: Self) {}
}

#[requires(forall<e : I::Item, i2 : I> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost(Seq::EMPTY))))]
#[requires(forall<initial: Map<I,_,_>>
    *initial.init_iter == iter ==>
    initial.init_iter.produces(*initial.produced, initial.iter) ==>
    // post condition implies invariant
    forall<i : I, e: I::Item, b: B>
        initial.iter.produces(Seq::singleton(e), i) ==>
            forall<f : &mut F> * f == initial.func ==>
                f.postcondition_mut((e, initial.produced), b) ==>
                    forall<i2: _, e2: _>
                        i.produces(Seq::singleton(e2), i2) ==>
                        (^f).precondition((e2, Ghost(initial.produced.push(e))))
)]
#[ensures(result.invariant())]
#[ensures(result == Map { init_iter: Ghost(iter), iter, func, produced: Ghost(Seq::EMPTY) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, I::Item, F> {
    Map { init_iter: ghost! {iter}, iter, func, produced: ghost! {Seq::EMPTY} }
}

fn identity<I: Iterator>(iter: I) {
    map(iter, |x, _| x);
}

#[requires(iter.invariant())]
#[requires(forall<prod : _, fin: _> iter.produces(prod, fin) ==> forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 10u32)]
fn increment<I: Iterator<Item = u32>>(iter: I) {
    map(
        iter,
        #[requires(@x <= 15)]
        |x: u32, _| x + 1,
    );
}
