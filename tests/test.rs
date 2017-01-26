extern crate pdqsort;
extern crate rand;

use std::cmp::Ordering::{Greater, Less};
use rand::{Rng, thread_rng};

#[test]
fn stress_correctness() {
    let mut rng = thread_rng();
    for n in 0..16 {
        for l in 0..16 {
            let mut a = rng.gen_iter::<u64>()
                .map(|x| x % (1 << l))
                .take((1 << n))
                .collect::<Vec<_>>();

            let mut b = a.clone();

            a.sort();
            pdqsort::sort(&mut b);

            assert_eq!(a, b);
        }
    }
}

#[test]
fn crazy_compare() {
    let mut rng = thread_rng();

    let mut v = rng.gen_iter::<u64>()
        .map(|x| x % 1000)
        .take(100_000)
        .collect::<Vec<_>>();

    // Even though comparison is non-sensical, sorting must not panic.
    pdqsort::sort_by(&mut v, |_, _| {
        if rng.gen::<bool>() {
            Less
        } else {
            Greater
        }
    });
}
