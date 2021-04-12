extern crate prusti_contracts;
use prusti_contracts::*;

// from prust-dev
#[requires(forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b))]
fn test5() {}

// from prust-dev prusti-tests/tests/parse/ui/predicates.rs
#[predicate]
fn pred(a: bool) -> bool {
    forall(|b: bool| a == b)
}

#[predicate]
fn pred_implies(a: bool) -> bool {
    forall(|b: bool| true ==> true)
}

// #[requires(forall(|i: usize, j:usize| (0 <= i && i <= j && j <= a.len()) ==> (a[i] <= a[j])))]
// fn sorted1(a: &[u32]) -> bool {
//     true
// }

// #[predicate]
// fn sorted2(a: &[u32]) -> bool {
//     forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b)
// }

// #[predicate]
// fn sorted(a: &[u32]) -> bool {
//     forall(|i: usize, j:usize| (0 <= i && i <= j && j <= a.len()) ==> (a[i] <= a[j]))
// }

// #[pure]
// fn binary_search(haystack: &[u32], needle: u32) ->

fn main() {
}
