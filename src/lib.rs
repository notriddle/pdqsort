#![feature(test)]
#![feature(untagged_unions)]

extern crate test;
extern crate rand;

use std::cmp;
use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::mem::size_of;
use std::mem;
use std::ptr;

/// Inserts `v[0]` into pre-sorted sequence `v[1..]` so that whole `v[..]` becomes sorted.
///
/// This is the integral subroutine of insertion sort.
fn insert_head<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    if v.len() >= 2 && compare(&v[0], &v[1]) == Greater {
        unsafe {
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
            let mut tmp = NoDrop { value: ptr::read(&v[0]) };

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
                dest: &mut v[1],
            };
            ptr::copy_nonoverlapping(&v[1], &mut v[0], 1);

            for i in 2..v.len() {
                if compare(&tmp.value, &v[i]) != Greater {
                    break;
                }
                ptr::copy_nonoverlapping(&v[i], &mut v[i - 1], 1);
                hole.dest = &mut v[i];
            }
            // `hole` gets dropped and thus copies `tmp` into the remaining hole in `v`.
        }
        return true;
    }
    return false;

    // Holds a value, but never drops it.
    #[allow(unions_with_drop_fields)]
    union NoDrop<T> {
        value: T
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

fn initial<T, F>(v: &mut [T], compare: &mut F) -> bool
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

fn check<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    let mut cnt = 0;
    let len = v.len();
    if len >= 2 {
        for i in (0..len-1).rev() {
            if insert_head(&mut v[i..], compare) {
                cnt += 1;
                if cnt > 4 {
                    return false;
                }
            }
        }
    }
    true
}

fn partition_in_blocks<T, F>(v: &mut [T], pivot: &T, compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
{
    const WIDTH: usize = 64;

    let mut a = 0;
    let mut b = v.len();

    let mut elems_a = [0u8; WIDTH];
    let mut len_a = 0;
    let mut pos_a = 0;

    let mut elems_b = [0u8; WIDTH];
    let mut len_b = 0;
    let mut pos_b = 0;

    let mut width_a = WIDTH;
    let mut width_b = WIDTH;
    let mut done = false;

    while !done {
        done = b - a <= 2 * WIDTH;
        if done {
            let rem = b - a - (pos_a < len_a || pos_b < len_b) as usize * WIDTH;
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
        }

        if pos_a == len_a {
            pos_a = 0;
            len_a = 0;
            for i in 0..width_a {
                unsafe {
                    let c0 = (compare(v.get_unchecked(a + i), pivot) != Less) as usize;
                    *elems_a.get_unchecked_mut(len_a) = i as u8;
                    len_a += c0;
                }
            }
        }

        if pos_b == len_b {
            pos_b = 0;
            len_b = 0;
            for i in 0..width_b {
                unsafe {
                    let c0 = (compare(v.get_unchecked(b - i - 1), pivot) == Less) as usize;
                    *elems_b.get_unchecked_mut(len_b) = i as u8;
                    len_b += c0;
                }
            }
        }

        for _ in 0..cmp::min(len_a - pos_a, len_b - pos_b) {
            unsafe {
                ptr::swap(v.get_unchecked_mut(a + *elems_a.get_unchecked(pos_a) as usize),
                v.get_unchecked_mut(b - *elems_b.get_unchecked(pos_b) as usize - 1));
            }
            pos_a += 1;
            pos_b += 1;
        }

        if pos_a == len_a {
            a += width_a;
        }

        if pos_b == len_b {
            b -= width_b;
        }
    }

    if pos_a < len_a {
        while pos_a < len_a {
            unsafe {
                ptr::swap(v.get_unchecked_mut(a + *elems_a.get_unchecked(len_a - 1) as usize),
                v.get_unchecked_mut(b - 1));
            }
            len_a -= 1; 
            b -= 1;
        }
        b
    } else {
        while pos_b < len_b {
            unsafe {
                ptr::swap(v.get_unchecked_mut(a),
                v.get_unchecked_mut(b - *elems_b.get_unchecked(len_b - 1) as usize - 1));
            }
            a += 1;
            len_b -= 1;
        }
        a
    }
}

fn partition<T, F>(v: &mut [T], mid: usize, compare: &mut F) -> (usize, bool)
    where F: FnMut(&T, &T) -> Ordering
{
    v.swap(0, mid);
    let (mid, already) = {
        let (pivot, v) = v.split_at_mut(1);
        let pivot = &pivot[0];
        let len = v.len();

        let mut a = 0;
        let mut b = len;
        while a < b && compare(&v[a], &*pivot) == Less {
            a += 1;
        }
        while a < b && compare(&v[b - 1], &*pivot) != Less {
            b -= 1;
        }
        let already = a >= b;

        if a >= b {
            (a, true)
        } else {
            (a + partition_in_blocks(&mut v[a..b], pivot, compare), false)
        }
    };
    v.swap(0, mid);
    (mid, already)
}

fn partition_equal<T, F>(v: &mut [T], mid: usize, compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
{
    v.swap(0, mid);
    let (pivot, v) = v.split_at_mut(1);
    let pivot = &pivot[0];
    let len = v.len();

    let mut a = 0;
    let mut b = len;

    while a < b {
        while a < b && compare(&v[a], &*pivot) == Equal {
            a += 1;
        }
        while a < b && compare(&v[b - 1], &*pivot) == Greater {
            b -= 1;
        }
        if a < b {
            b -= 1;
            v.swap(a, b);
            a += 1;
        }
    }
    a + 1
}

fn quicksort<T, F>(v: &mut [T], compare: &mut F, pred: Option<&T>, depth: usize)
    where F: FnMut(&T, &T) -> Ordering
{
    let max_insertion = if size_of::<T>() <= 2 * size_of::<usize>() { 32 } else { 16 };

    // TODO: switch to heapsort
    let len = v.len();

    if len <= max_insertion {
        if len >= 2 {
            for i in (0..len-1).rev() {
                insert_head(&mut v[i..], compare);
            }
        }
        return;
    }

    // TODO: factor out
    let mid = {
        let mut sort3 = |a, b, c| {
            let mut sort2 = |a, b| {
                unsafe {
                    if compare(v.get_unchecked(a), v.get_unchecked(b)) == Greater {
                        ptr::swap(v.get_unchecked_mut(a), v.get_unchecked_mut(b));
                    }
                }
            };
            sort2(a, b);
            sort2(b, c);
            sort2(a, b);
        };

        let a = len / 4;
        let b = len / 2;
        let c = a + b;
        if len >= 200 {
            sort3(a - 1, a, c + 1);
            sort3(b - 1, b, b + 1);
            sort3(c - 1, c, c + 1);
        }
        sort3(a, b, c);
        b
    };

    if let Some(p) = pred {
        if compare(p, &v[mid]) == Equal {
            let new_mid = partition_equal(v, mid, compare);
            let (left, right) = v.split_at_mut(new_mid - 1);

            quicksort(right, compare, Some(&left[left.len() - 1]), depth + 1);
            return;
        }
    }

    let (mid, already) = partition(v, mid, compare);
    let (left, right) = v.split_at_mut(mid);
    let (pivot, right) = right.split_at_mut(1);
    let pivot = &pivot[0];

    if already && check(left, compare) && check(right, compare) {
        return;
    }

    quicksort(left, compare, pred, depth + 1);
    quicksort(right, compare, Some(pivot), depth + 1);
}

pub fn sort<T, F>(v: &mut [T], mut compare: F)
    where F: FnMut(&T, &T) -> Ordering
{
    // Sorting has no meaningful behavior on zero-sized types.
    if size_of::<T>() == 0 {
        return;
    }

    if initial(v, &mut compare) {
        return;
    }

    quicksort(v, &mut compare, None, 0);
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
