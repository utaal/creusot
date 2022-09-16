#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{iter::*, std::*, *};

fn mapped_range() {
    assert!((0..10).map(|x| x * 10).nth(10) == 100);
}

fn counter() {
    let mut c = 0;
    let count = (0..10)
        .map(|x| {
            c += 1;
            x
        })
        .count();
    assert!(c == count);
}

fn enumerate<I: Iterator>(i: I) -> impl Iterator {
    let mut i = 0;

    i.map(|x| {
        let r = (i, x);
        i += 1;
        r
    })
}

// Done
fn concat() {}

fn sum() {
    assert!((0..10).sum() == 45)
}

fn sum_times() {
    assert!((0..10).map(|x| x * 2).sum() == 45)
}

// all_zero

// collect
//
fn collect() {}
// let v = (0..n).collect();
// forall i v[i] == i

// let v = (0..n).map(|x| x * x).collect();
// forall i, v[i] == i * i
