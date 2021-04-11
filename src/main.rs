extern crate prusti_contracts;
use prusti_contracts::*;

#[predicate]
fn sorted(a: &[u32]) -> bool {
    forall((|i: usize, j:usize| (0 <= i && i <= j && j <= a.len()) ==> (a[i] <= a[j])))
}

// #[pure]
// fn binary_search(haystack: &[u32], needle: u32) -> 

fn main() {
}
