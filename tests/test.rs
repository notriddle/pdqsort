extern crate pdqsort;
extern crate rand;

use rand::{Rng, thread_rng};

// TODO: Set up Travis
// TODO: Ensure #![no_std] compatibility
// TODO: Optimize insertion sort
// TODO: more correctness tests
// TODO: a test with totally random comparison function

#[test]
fn test_correctness() {
    let mut rng = thread_rng();
    for _ in 0..1000 {
        let len = rng.gen::<usize>() % 1000 + 1;
        let limit = rng.gen::<u64>() % 1000 + 1;

        let mut a = rng.gen_iter::<u64>()
            .map(|x| x % limit)
            .take(len)
            .collect::<Vec<_>>();

        let mut b = a.clone();

        a.sort();
        pdqsort::sort(&mut b);

        assert_eq!(a, b);
    }
}
