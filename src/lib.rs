#![feature(test)]
#![feature(untagged_unions)]

extern crate test;
extern crate rand;

use std::cmp;
use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::mem::size_of;
use std::mem;
use std::ptr;

// Holds a value, but never drops it.
#[allow(unions_with_drop_fields)]
union NoDrop<T> {
    value: T
}

/// TODO: Fix comments in this function.
/// Inserts `v[0]` into pre-sorted sequence `v[1..]` so that whole `v[..]` becomes sorted.
///
/// This is the integral subroutine of insertion sort.
fn insert_tail<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    let len = v.len();
    unsafe {
        if len >= 2 && compare(&v[len-2], &v[len-1]) == Greater {
            // There are three ways to implement insertion here:
            //
            // 1. Swap adjacent elements until the first one gets to its final destination.
            //    However, this way we copy data around more than is necessary. If elements are big
            //    structures (costly to copy), this method will be slow.
            //
            // 2. Iterate until the right place for the first element is found. Then shift the
            //    elements succeeding it to make room for it and finally place it into the
            //    remaining hole. This is a good method.
            //
            // 3. Copy the first element into a temporary variable. Iterate until the right place
            //    for it is found. As we go along, copy every traversed element into the slot
            //    preceding it. Finally, copy data from the temporary variable into the remaining
            //    hole. This method is very good. Benchmarks demonstrated slightly better
            //    performance than with the 2nd method.
            //
            // All methods were benchmarked, and the 3rd showed best results. So we chose that one.
            let mut tmp = NoDrop { value: ptr::read(&v[len-1]) };

            // Intermediate state of the insertion process is always tracked by `hole`, which
            // serves two purposes:
            // 1. Protects integrity of `v` from panics in `compare`.
            // 2. Fills the remaining hole in `v` in the end.
            //
            // Panic safety:
            //
            // If `compare` panics at any point during the process, `hole` will get dropped and
            // fill the hole in `v` with `tmp`, thus ensuring that `v` still holds every object it
            // initially held exactly once.
            let mut hole = InsertionHole {
                src: &mut tmp.value,
                dest: v.get_unchecked_mut(len - 2),
            };
            ptr::copy_nonoverlapping(&v[len-2], &mut v[len-1], 1);

            for i in (0..len-2).rev() {
                if compare(v.get_unchecked(i), &tmp.value) != Greater {
                    break;
                }
                ptr::copy_nonoverlapping(v.get_unchecked(i), v.get_unchecked_mut(i+1), 1);
                hole.dest = v.get_unchecked_mut(i);
            }
            // `hole` gets dropped and thus copies `tmp` into the remaining hole in `v`.
            return true;
        } else {
            return false;
        }
    }

    // When dropped, copies from `src` into `dest`.
    struct InsertionHole<T> {
        src: *mut T,
        dest: *mut T,
    }

    impl<T> Drop for InsertionHole<T> {
        fn drop(&mut self) {
            unsafe { ptr::copy_nonoverlapping(self.src, self.dest, 1); }
        }
    }
}

fn check<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    if v.len() >= 2 {
        if compare(&v[0], &v[1]) == Greater {
            for i in 2..v.len() {
                if compare(&v[i - 1], &v[i]) != Greater {
                    return false;
                }
            }
            v.reverse();
        } else {
            for i in 2..v.len() {
                if compare(&v[i - 1], &v[i]) == Greater {
                    return false;
                }
            }
        }
    }
    true
}

unsafe fn partition<T, F>(v: &mut [T], compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
    , T: std::fmt::Debug
{
    let len = v.len();
    let pivot = v.get_unchecked(0) as *const _;

    let mut a = 1;
    let mut b = len;

    const WIDTH: usize = 64;

    let mut elems_a = [0u8; WIDTH];
    let mut len_a = 0;
    let mut pos_a = 0;

    let mut elems_b = [0u8; WIDTH];
    let mut len_b = 0;
    let mut pos_b = 0;

    while b - a > 2 * WIDTH {
        if pos_a == len_a {
            pos_a = 0;
            len_a = 0;
            for i in 0..WIDTH {
                let c0 = (compare(v.get_unchecked_mut(a + i), &*pivot) != Less) as usize;
                *elems_a.get_unchecked_mut(len_a) = i as u8;
                len_a += c0;
            }
        }

        if pos_b == len_b {
            pos_b = 0;
            len_b = 0;
            for i in 0..WIDTH {
                let c0 = (compare(v.get_unchecked_mut(b - i - 1), &*pivot) == Less) as usize;
                *elems_b.get_unchecked_mut(len_b) = i as u8;
                len_b += c0;
            }
        }

        let cnt = cmp::min(len_a - pos_a, len_b - pos_b);
        for _ in 0..cnt {
            ptr::swap(v.get_unchecked_mut(a + *elems_a.get_unchecked_mut(pos_a) as usize),
                      v.get_unchecked_mut(b - *elems_b.get_unchecked_mut(pos_b) as usize - 1));
            pos_a += 1;
            pos_b += 1;
        }

        if pos_a == len_a {
            a += WIDTH;
        }

        if pos_b == len_b {
            b -= WIDTH;
        }
    }

    let rem = b - a - (pos_a < len_a || pos_b < len_b) as usize * WIDTH;
    let width_a;
    let width_b;
    if pos_a < len_a {
        width_a = WIDTH;
        width_b = rem;
    } else if pos_b < len_b {
        width_a = rem;
        width_b = WIDTH;
    } else {
        width_a = rem / 2;
        width_b = rem - width_a;
    }

    if pos_a == len_a {
        pos_a = 0;
        len_a = 0;
        for i in 0..width_a {
            let c0 = (compare(v.get_unchecked_mut(a + i), &*pivot) != Less) as usize;
            *elems_a.get_unchecked_mut(len_a) = i as u8;
            len_a += c0;
        }
    }

    if pos_b == len_b {
        pos_b = 0;
        len_b = 0;
        for i in 0..width_b {
            let c0 = (compare(v.get_unchecked_mut(b - i - 1), &*pivot) == Less) as usize;
            *elems_b.get_unchecked_mut(len_b) = i as u8;
            len_b += c0;
        }
    }

    let cnt = cmp::min(len_a - pos_a, len_b - pos_b);
    for _ in 0..cnt {
        ptr::swap(v.get_unchecked_mut(a + *elems_a.get_unchecked_mut(pos_a) as usize),
                  v.get_unchecked_mut(b - *elems_b.get_unchecked_mut(pos_b) as usize - 1));
        pos_a += 1;
        pos_b += 1;
    }

    if pos_a == len_a {
        a += width_a;
    }

    if pos_b == len_b {
        b -= width_b;
    }

    if pos_a < len_a {
        while pos_a < len_a {
            ptr::swap(v.get_unchecked_mut(a + *elems_a.get_unchecked_mut(len_a - 1) as usize),
                      v.get_unchecked_mut(b - 1));
            len_a -= 1; 
            b -= 1;
        }
        b
    } else {
        while pos_b < len_b {
            ptr::swap(v.get_unchecked_mut(a),
                      v.get_unchecked_mut(b - *elems_b.get_unchecked_mut(len_b - 1) as usize - 1));
            a += 1;
            len_b -= 1;
        }
        a
    }
}

fn rec<'a, T, F>(mut v: &'a mut [T], compare: &mut F)
    where F: FnMut(&T, &T) -> Ordering
    , T: std::fmt::Debug
{
    let max_insertion = if size_of::<T>() <= 16 { 64 } else { 32 };

    loop {
        let len = v.len();

        if len <= max_insertion {
            for i in 2..len+1 {
                insert_tail(&mut v[..i], compare);
            }
            return;
        }

        let mid = len / 2;
        {
            let mut sort2 = |a,  b| {
                if compare(&v[a], &v[b]) == Greater {
                    v.swap(a, b);
                }
            };

            let mut sort3 = |a, b, c| {
                sort2(a, b);
                sort2(b, c);
                sort2(a, b);
            };

            if len >= 200 {
                sort3(0, mid - 1, len - 3);
                sort3(1, mid + 0, len - 2);
                sort3(2, mid + 1, len - 1);
                sort3(mid - 1, mid, mid + 1);
            } else {
                sort3(0, mid, len - 1);
            }
            // TODO: partition left if median occurs twice
            // TODO: partition left if very unbalanced for a small array
            // TODO: scan every fourth pivot (see paper)
            // TODO: median of sqrt for large arrays?
            // TODO: some randomization?
        }

        v.swap(0, mid);
        let new_mid = unsafe { partition(v, compare) };
        v.swap(0, new_mid - 1);

        let (left, right) = {v}.split_at_mut(new_mid);

        if new_mid - 1 == mid && check(left, compare) {
            // nothing
        } else {
            rec(left, compare);
        }

        if new_mid - 1 == mid && check(right, compare) {
            return;
        }
        v = right;
    }
}

pub fn sort<T, F>(v: &mut [T], mut compare: F)
    where F: FnMut(&T, &T) -> Ordering
    , T: std::fmt::Debug
{
    // Sorting has no meaningful behavior on zero-sized types.
    if size_of::<T>() == 0 {
        return;
    }

    if check(v, &mut compare) {
        return;
    }

    rec(v, &mut compare);
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use test;
    use rand::{thread_rng, Rng};
    use std::mem;

    // TODO: more correctness tests

    #[test]
    fn test() {
        let mut rng = thread_rng();
        for i in 0..1000 {
            let len = rng.gen::<usize>() % 1000 + 1;
            let limit = rng.gen::<u64>() % 1000 + 1;

            let mut a = rng.gen_iter::<u64>()
                .map(|x| x % limit)
                .take(len)
                .collect::<Vec<_>>();

            let mut b = a.clone();

            a.sort();
            sort(&mut b, |x, y| x.cmp(y));

            assert_eq!(a, b);
        }
    }

    fn gen_ascending(len: usize) -> Vec<u64> {
        (0..len as u64).collect()
    }

    fn gen_descending(len: usize) -> Vec<u64> {
        (0..len as u64).rev().collect()
    }

    fn gen_random(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        rng.gen_iter::<u64>().take(len).collect()
    }

    fn gen_mostly_ascending(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        let mut v = gen_ascending(len);
        for _ in (0usize..).take_while(|x| x * x <= len) {
            let x = rng.gen::<usize>() % len;
            let y = rng.gen::<usize>() % len;
            v.swap(x, y);
        }
        v
    }

    fn gen_mostly_descending(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        let mut v = gen_descending(len);
        for _ in (0usize..).take_while(|x| x * x <= len) {
            let x = rng.gen::<usize>() % len;
            let y = rng.gen::<usize>() % len;
            v.swap(x, y);
        }
        v
    }

    fn gen_big_random(len: usize) -> Vec<[u64; 16]> {
        let mut rng = thread_rng();
        rng.gen_iter().map(|x| [x; 16]).take(len).collect()
    }

    fn gen_big_ascending(len: usize) -> Vec<[u64; 16]> {
        (0..len as u64).map(|x| [x; 16]).take(len).collect()
    }

    fn gen_big_descending(len: usize) -> Vec<[u64; 16]> {
        (0..len as u64).rev().map(|x| [x; 16]).take(len).collect()
    }

    macro_rules! sort_bench {
        ($name:ident, $gen:expr, $len:expr) => {
            #[bench]
            fn $name(b: &mut Bencher) {
                b.iter(|| $gen($len).sort());
                b.bytes = $len * mem::size_of_val(&$gen(1)[0]) as u64;
            }
        }
    }

    sort_bench!(sort_small_random, gen_random, 10);
    sort_bench!(sort_small_ascending, gen_ascending, 10);
    sort_bench!(sort_small_descending, gen_descending, 10);

    sort_bench!(sort_small_big_random, gen_big_random, 10);
    sort_bench!(sort_small_big_ascending, gen_big_ascending, 10);
    sort_bench!(sort_small_big_descending, gen_big_descending, 10);

    sort_bench!(sort_medium_random, gen_random, 100);
    sort_bench!(sort_medium_ascending, gen_ascending, 100);
    sort_bench!(sort_medium_descending, gen_descending, 100);

    sort_bench!(sort_large_random, gen_random, 10000);
    sort_bench!(sort_large_ascending, gen_ascending, 10000);
    sort_bench!(sort_large_descending, gen_descending, 10000);
    sort_bench!(sort_large_mostly_ascending, gen_mostly_ascending, 10000);
    sort_bench!(sort_large_mostly_descending, gen_mostly_descending, 10000);

    sort_bench!(sort_large_big_random, gen_big_random, 10000);
    sort_bench!(sort_large_big_ascending, gen_big_ascending, 10000);
    sort_bench!(sort_large_big_descending, gen_big_descending, 10000);

    #[bench]
    fn sort_large_random_expensive(b: &mut Bencher) {
        let len = 10000;
        b.iter(|| {
            let mut count = 0;
            let cmp = move |a: &u64, b: &u64| {
                count += 1;
                if count % 1_000_000_000 == 0 {
                    panic!("should not happen");
                }
                (*a as f64).cos().partial_cmp(&(*b as f64).cos()).unwrap()
            };

            let mut v = gen_random(len);
            v.sort_by(cmp);
            test::black_box(count);
        });
        b.bytes = len as u64 * mem::size_of::<u64>() as u64;
    }

    macro_rules! new_sort_bench {
        ($name:ident, $gen:expr, $len:expr) => {
            #[bench]
            fn $name(b: &mut Bencher) {
                b.iter(|| sort(&mut $gen($len), |a, b| a.cmp(b)));
                b.bytes = $len * mem::size_of_val(&$gen(1)[0]) as u64;
            }
        }
    }

    new_sort_bench!(new_sort_small_random, gen_random, 10);
    new_sort_bench!(new_sort_small_ascending, gen_ascending, 10);
    new_sort_bench!(new_sort_small_descending, gen_descending, 10);

    new_sort_bench!(new_sort_small_big_random, gen_big_random, 10);
    new_sort_bench!(new_sort_small_big_ascending, gen_big_ascending, 10);
    new_sort_bench!(new_sort_small_big_descending, gen_big_descending, 10);

    new_sort_bench!(new_sort_medium_random, gen_random, 100);
    new_sort_bench!(new_sort_medium_ascending, gen_ascending, 100);
    new_sort_bench!(new_sort_medium_descending, gen_descending, 100);

    new_sort_bench!(new_sort_large_random, gen_random, 10000);
    new_sort_bench!(new_sort_large_ascending, gen_ascending, 10000);
    new_sort_bench!(new_sort_large_descending, gen_descending, 10000);
    new_sort_bench!(new_sort_large_mostly_ascending, gen_mostly_ascending, 10000);
    new_sort_bench!(new_sort_large_mostly_descending, gen_mostly_descending, 10000);

    new_sort_bench!(new_sort_large_big_random, gen_big_random, 10000);
    new_sort_bench!(new_sort_large_big_ascending, gen_big_ascending, 10000);
    new_sort_bench!(new_sort_large_big_descending, gen_big_descending, 10000);

    #[bench]
    fn new_sort_large_random_expensive(b: &mut Bencher) {
        let len = 10000;
        b.iter(|| {
            let mut count = 0;
            let mut cmp = move |a: &u64, b: &u64| {
                count += 1;
                if count % 1_000_000_000 == 0 {
                    panic!("should not happen");
                }
                (*a as f64).cos().partial_cmp(&(*b as f64).cos()).unwrap()
            };

            let mut v = gen_random(len);
            sort(&mut v, &mut cmp);
            test::black_box(count);
        });
        b.bytes = len as u64 * mem::size_of::<u64>() as u64;
    }
}
