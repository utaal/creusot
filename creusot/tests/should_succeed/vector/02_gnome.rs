extern crate creusot_contracts;

use creusot_contracts::*;

#[predicate]
fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[ensures(sorted((^v).deep_model()))]
#[ensures((@^v).permutation_of(@v))]
pub fn gnome_sort<T: Ord + DeepModel>(v: &mut Vec<T>)
where
    T::DeepModelTy: OrdLogic,
{
    let old_v = ghost! { v };
    let mut i = 0;
    #[invariant(sorted, sorted_range(v.deep_model(), 0, @i))]
    #[invariant(proph_const, ^v == ^old_v.inner())]
    #[invariant(permutation, (@v).permutation_of(@old_v.inner()))]
    while i < v.len() {
        if i == 0 || v[i - 1].le(&v[i]) {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}
