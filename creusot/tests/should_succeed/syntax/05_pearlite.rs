extern crate creusot_contracts;
use creusot_contracts::*;

// Tests that we can use field access syntax in pearlite.

pub struct A {
    a: bool,
}

#[trusted]
#[ensures(x.a == x.a)]
pub fn solver(x: A) {}

#[ensures(x == A { a : false })]
pub fn struct_in_pearlite(x: A) {}

pub struct B {
    pub field1: bool,
    pub field2: u32,
}

#[ensures(x == B { field2: 0u32, field1: false })]
pub fn struct_order(x: B) {}

#[predicate]
#[allow(unreachable_patterns)]
pub fn field1_is_true(x: B) -> bool {
    pearlite! {
        use crate::B; // verify that imports work properly
        match x {
            B { field1: true, .. } => true,
            B { field2, field1: _f } => @field2 == 0,
            _ => false
        }
    }
}

pub fn ghost_closure() {
    let x = ghost! { pearlite! { |a : u32| a  } };
}

pub fn pearlite_closure(x: Ghost<Mapping<u32, bool>>) {}

pub fn caller() {
    pearlite_closure(ghost! { pearlite! { |a| true }});
}

// Implicit logical reborrows

pub struct S {}

impl S {
    #[logic]
    pub fn x(&mut self) -> bool {
        true
    }
}

#[logic]
pub fn proj(x: &mut (S, S)) -> bool {
    x.0.x()
}
