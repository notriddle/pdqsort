//! Pattern-defeating quicksort.
//!
//! This sort is significantly faster than the standard sort in Rust. On random arrays it's around
//! 40% faster. The key drawback is that it is an unstable sort (i.e. may reorder equal elements).
//!
//! The algorithm was designed by Orson Peters and first published at:
//! https://github.com/orlp/pdqsort
//!
//! Quoting it's designer: "Pattern-defeating quicksort (pdqsort) is a novel sorting algorithm
//! that combines the fast average case of randomized quicksort with the fast worst case of
//! heapsort, while achieving linear time on inputs with certain patterns. pdqsort is an extension
//! and improvement of David Musser's introsort."
//!
//! Characteristics:
//!
//! - Best-case running time is `O(n)`.
//! - Worst-case running time is `O(n log n)`.
//! - Unstable (i.e. may reorder equal elements).
//! - Does not allocate additional memory.
//! - Compatible with `#![no_std]`.
//!
//! # Example
//!
//! ```
//! extern crate pdqsort;
//!
//! let mut v = [-5, 4, 1, -3, 2];
//! pdqsort::sort(&mut v);
//! assert!(v == [-5, -3, 1, 2, 4]);
//! ```

#![feature(test)]
#![feature(untagged_unions)]

extern crate test;
extern crate rand;

use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::cmp;
use std::mem::size_of;
use std::ptr;

/// Inserts `v[0]` into pre-sorted sequence `v[1..]` so that whole `v[..]` becomes sorted, and
/// returns `true` if the sequence was modified.
///
/// This is the integral subroutine of insertion sort.
fn insert_head<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
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
        true
    } else {
        false
    }
}

/// Sorts `v` using insertion sort, which is `O(n^2)` worst-case.
fn insertion_sort<T, F>(v: &mut [T], compare: &mut F)
    where F: FnMut(&T, &T) -> Ordering
{
    let len = v.len();

    if len >= 2 {
        for i in (0..len-1).rev() {
            insert_head(&mut v[i..], compare);
        }
    }
}

/// Attempts to sort `v` using insertion sort in just a handful of steps. Returns `true` if the
/// slice was successfully sorted.
fn partial_insertion_sort<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    const MAX_INSERTIONS: usize = 4;

    let len = v.len();
    if len >= 2 {
        let mut insertions = 0;

        for i in (0..len-1).rev() {
            if insert_head(&mut v[i..], compare) {
                insertions += 1;
                if insertions > MAX_INSERTIONS {
                    return false;
                }
            }
        }
    }
    true
}

/// Sorts `v` using heapsort, which guarantees `O(n log n)` worst-case.
fn heapsort<T, F>(v: &mut [T], compare: &mut F)
    where F: FnMut(&T, &T) -> Ordering
{
    // The heap is a max-heap. In other words, children are never greater than their parents.
    let mut sift_down = |v: &mut [T], mut x| {
        loop {
            let l = 2 * x + 1;
            let r = 2 * x + 2;

            // Find the greater child.
            let child = if r < v.len() && compare(&v[l], &v[r]) == Less {
                r
            } else {
                l
            };

            if child >= v.len() || compare(&v[x], &v[child]) != Less {
                break;
            }
            v.swap(x, child);
            x = child;
        }
    };

    // Build the heap in linear time.
    for i in (0 .. v.len() / 2).rev() {
        sift_down(v, i);
    }

    // Pop elements from the heap.
    for i in (1 .. v.len()).rev() {
        v.swap(0, i);
        sift_down(&mut v[..i], 0);
    }
}

/// Checks whether `v` is already sorted (either in ascending or descending order) and attempts to
/// make it ascending in very few steps. Finally, returns `true` if `v` is sorted in ascending
/// order.
fn is_presorted<T, F>(v: &mut [T], compare: &mut F) -> bool
    where F: FnMut(&T, &T) -> Ordering
{
    if v.len() >= 2 {
        if compare(&v[0], &v[1]) == Greater {
            // Check whether the slice is descending.
            for i in 2..v.len() {
                if compare(&v[i - 1], &v[i]) == Less {
                    return false;
                }
            }
            // Reverse to make it ascending.
            v.reverse();
        } else {
            // Check whether the slice is ascending.
            for i in 2..v.len() {
                if compare(&v[i - 1], &v[i]) == Greater {
                    return false;
                }
            }
        }
    }
    true
}

/// Partitions `v` into elements smaller than `pivot`, followed by elements greater than or equal
/// to `pivot`. Returns the number of elements smaller than `pivot`.
///
/// Partitioning is performed block-by-block in order to minimize the cost of branching operations.
/// This idea is presented in the [BlockQuicksort][pdf] paper.
///
/// [pdf]: http://drops.dagstuhl.de/opus/volltexte/2016/6389/pdf/LIPIcs-ESA-2016-38.pdf
fn partition_in_blocks<T, F>(v: &mut [T], pivot: &T, compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
{
    const BLOCK: usize = 64;

    // State on the left side.
    let mut l = 0;
    let mut len_l = 0;
    let mut start_l = 0;
    let mut block_l = BLOCK;
    let mut offsets_l = [0u8; BLOCK];

    // State on the right side.
    let mut r = v.len();
    let mut len_r = 0;
    let mut start_r = 0;
    let mut block_r = BLOCK;
    let mut offsets_r = [0u8; BLOCK];

    // The general idea is to repeat the following steps until completion:
    //
    // 1. Identify a few elements on the left side that are greater than or equal to the pivot.
    // 2. Identify a few elements on the right side that are less than the pivot.
    // 3. Swap the corresponding displaced elements on the left and right side.

    let mut is_done = false;

    while !is_done {
        // We are done with partitioning block-by-block when `l` and `r` get very close. Then we do
        // some patch-up work in order to partition the remaining elements.
        is_done = r - l <= 2 * BLOCK;

        if is_done {
            // Number of remaining elements (still not compared to the pivot).
            let rem = r - l - (start_l < len_l || start_r < len_r) as usize * BLOCK;

            if start_l < len_l {
                block_r = rem;
            } else if start_r < len_r {
                block_l = rem;
            } else {
                block_l = rem / 2;
                block_r = rem - block_l;
            }
            debug_assert!(block_l <= BLOCK);
            debug_assert!(block_r <= BLOCK);
        }

        if start_l == len_l {
            // Trace `block_l` elements from the left side.
            start_l = 0;
            len_l = 0;
            for i in 0..block_l {
                unsafe {
                    let c0 = (compare(v.get_unchecked(l + i), pivot) != Less) as usize;
                    *offsets_l.get_unchecked_mut(len_l) = i as u8;
                    len_l += c0;
                }
            }
        }

        if start_r == len_r {
            // Trace `block_r` elements from the right side.
            start_r = 0;
            len_r = 0;
            for i in 0..block_r {
                unsafe {
                    let c0 = (compare(v.get_unchecked(r - i - 1), pivot) == Less) as usize;
                    *offsets_r.get_unchecked_mut(len_r) = i as u8;
                    len_r += c0;
                }
            }
        }

        // Perform swaps between the left and right side.
        for _ in 0..cmp::min(len_l - start_l, len_r - start_r) {
            unsafe {
                ptr::swap(v.get_unchecked_mut(l + *offsets_l.get_unchecked(start_l) as usize),
                          v.get_unchecked_mut(r - *offsets_r.get_unchecked(start_r) as usize - 1));
            }
            start_l += 1;
            start_r += 1;
        }

        if start_l == len_l {
            // The left block is fully exhausted. Move the left bound.
            l += block_l;
        }

        if start_r == len_r {
            // The right block is fully exhausted. Move the right bound.
            r -= block_r;
        }
    }

    if start_l < len_l {
        // Move the remaining to-be-swapped elements to the far right.
        while start_l < len_l {
            len_l -= 1;
            unsafe {
                ptr::swap(v.get_unchecked_mut(l + *offsets_l.get_unchecked(len_l) as usize),
                          v.get_unchecked_mut(r - 1));
            }
            r -= 1;
        }
        r
    } else {
        // Move the remaining to-be-swapped elements to the far left.
        while start_r < len_r {
            len_r -= 1;
            unsafe {
                ptr::swap(v.get_unchecked_mut(l),
                          v.get_unchecked_mut(r - *offsets_r.get_unchecked(len_r) as usize - 1));
            }
            l += 1;
        }
        l
    }
}

/// Partitions `v` into elements smaller than `v[pivot]`, followed by elements greater than or
/// equal to `v[pivot]`.
///
/// Returns two things:
///
/// 1. the number of elements smaller than `v[pivot]`
/// 2. `true` if `v` was already partitioned
fn partition<T, F>(v: &mut [T], pivot: usize, compare: &mut F) -> (usize, bool)
    where F: FnMut(&T, &T) -> Ordering
{
    v.swap(0, pivot);

    let (mid, was_partitioned) = {
        let (pivot, v) = v.split_at_mut(1);
        let pivot = &pivot[0];
        let len = v.len();

        let mut l = 0;
        let mut r = len;
        while l < r && compare(&v[l], &*pivot) == Less {
            l += 1;
        }
        while l < r && compare(&v[r - 1], &*pivot) != Less {
            r -= 1;
        }

        (l + partition_in_blocks(&mut v[l..r], pivot, compare), l >= r)
    };

    v.swap(0, mid);
    (mid, was_partitioned)
}

/// Partitions `v` into elements equal than `v[pivot]`, followed by elements greater than
/// `v[pivot]`. It is assumed that `v` does not contain elements smaller than `v[pivot]`.
fn partition_equal<T, F>(v: &mut [T], mid: usize, compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
{
    v.swap(0, mid);

    let (pivot, v) = v.split_at_mut(1);
    let pivot = &pivot[0];
    let len = v.len();

    let mut l = 0;
    let mut r = len;

    while l < r {
        while l < r && compare(&v[l], &*pivot) == Equal {
            l += 1;
        }
        while l < r && compare(&v[r - 1], &*pivot) == Greater {
            r -= 1;
        }
        if l < r {
            r -= 1;
            v.swap(l, r);
            l += 1;
        }
    }

    // Add 1 to also account for the pivot at index 0.
    l + 1
}

/// Scatters some elements in `v` around in attempt to break patterns that might cause imbalanced
/// partitions in quicksort.
fn break_patterns<T>(v: &mut [T]) {
    let len = v.len();

    if len >= 4 {
        v.swap(0, len / 2);
        v.swap(len - 1, len - len / 2);

        if len >= 8 {
            v.swap(1, len / 2 + 1);
            v.swap(2, len / 2 + 2);
            v.swap(len - 2, len - len / 2 - 1);
            v.swap(len - 3, len - len / 2 - 2);
        }
    }
}

/// Chooses a pivot in `v` and returns it's index.
fn choose_pivot<T, F>(v: &mut [T], compare: &mut F) -> usize
    where F: FnMut(&T, &T) -> Ordering
{
    const MIN_MEDIAN_OF_MEDIANS: usize = 256;

    let len = v.len();
    let a = len / 4 * 1;
    let b = len / 4 * 2;
    let c = len / 4 * 3;

    let mut sort2 = |a, b| unsafe {
        if compare(v.get_unchecked(a), v.get_unchecked(b)) == Greater {
            ptr::swap(v.get_unchecked_mut(a), v.get_unchecked_mut(b));
        }
    };

    let mut sort3 = |a, b, c| {
        sort2(a, b);
        sort2(b, c);
        sort2(a, b);
    };

    if len >= 4 {
        if len >= MIN_MEDIAN_OF_MEDIANS {
            sort3(a - 1, a, c + 1);
            sort3(b - 1, b, b + 1);
            sort3(c - 1, c, c + 1);
        }
        sort3(a, b, c);
    }
    b
}

/// Sorts `v` recursively using quicksort.
///
/// If the slice had a predecessor in the original array, it is specified as `pred`.
///
/// `limit` is the number of allowed imbalanced partitions before switching to `heapsort`. If zero,
/// this function will immediately switch to heapsort.
fn quicksort<T, F>(v: &mut [T], compare: &mut F, pred: Option<&T>, mut limit: usize)
    where F: FnMut(&T, &T) -> Ordering
{
    // If `v` has length up to `insertion_len`, simply switch to insertion sort because it is going
    // to perform better than quicksort. For bigger types `T`, the threshold is smaller.
    let max_insertion = if size_of::<T>() <= 2 * size_of::<usize>() { 32 } else { 16 };

    let len = v.len();

    if len <= max_insertion {
        insertion_sort(v, compare);
        return;
    }

    if limit == 0 {
        heapsort(v, compare);
        return;
    }

    let mid = choose_pivot(v, compare);

    // If the chosen pivot is equal to the predecessor, then it's the smallest element in the
    // slice. In that case, partition the slice into elements equal to and elements greater
    // than the pivot.
    if let Some(p) = pred {
        if compare(p, &v[mid]) == Equal {
            let mid = partition_equal(v, mid, compare);
            quicksort(&mut v[mid..], compare, pred, limit);
            return;
        }
    }

    let (mid, was_partitioned) = partition(v, mid, compare);
    let (left, right) = v.split_at_mut(mid);
    let (pivot, right) = right.split_at_mut(1);
    let pivot = &pivot[0];

    if left.len() < len / 8 || right.len() < len / 8 {
        // The partitioning is imbalanced. Try breaking patterns in the slice to prevent that in
        // the future.
        limit -= 1;
        break_patterns(left);
        break_patterns(right);
    } else {
        // If decently balanced and was already partitioned, there are good chances the slice is
        // sorted or almost sorted. Try taking advantage of that for quick exit.
        if was_partitioned && partial_insertion_sort(left, compare)
                           && partial_insertion_sort(right, compare) {
            return;
        }
    }

    quicksort(left, compare, pred, limit);
    quicksort(right, compare, Some(pivot), limit);
}

/// Sorts a slice.
///
/// This sort is in-place, unstable, and `O(n log n)` worst-case.
///
/// The implementation is based on Orson Peters' pattern-defeating quicksort.
///
/// # Examples
///
/// ```
/// extern crate pdqsort;
///
/// let mut v = [-5, 4, 1, -3, 2];
/// pdqsort::sort(&mut v);
/// assert!(v == [-5, -3, 1, 2, 4]);
/// ```
#[inline]
pub fn sort<T>(v: &mut [T])
    where T: Ord
{
    sort_by(v, |a, b| a.cmp(b));
}

/// Sorts a slice using `f` to extract a key to compare elements by.
///
/// This sort is in-place, unstable, and `O(n log n)` worst-case.
///
/// The implementation is based on Orson Peters' pattern-defeating quicksort.
///
/// # Examples
///
/// ```
/// extern crate pdqsort;
///
/// let mut v = [-5i32, 4, 1, -3, 2];
/// pdqsort::sort_by_key(&mut v, |k| k.abs());
/// assert!(v == [1, 2, -3, 4, -5]);
/// ```
#[inline]
pub fn sort_by_key<T, B, F>(v: &mut [T], mut f: F)
    where F: FnMut(&T) -> B,
          B: Ord
{
    sort_by(v, |a, b| f(a).cmp(&f(b)))
}

/// Sorts a slice using `compare` to compare elements.
///
/// This sort is in-place, unstable, and `O(n log n)` worst-case.
///
/// The implementation is based on Orson Peters' pattern-defeating quicksort.
///
/// # Examples
///
/// ```
/// extern crate pdqsort;
///
/// let mut v = [5, 4, 1, 3, 2];
/// pdqsort::sort_by(&mut v, |a, b| a.cmp(b));
/// assert!(v == [1, 2, 3, 4, 5]);
///
/// // reverse sorting
/// pdqsort::sort_by(&mut v, |a, b| b.cmp(a));
/// assert!(v == [5, 4, 3, 2, 1]);
/// ```
#[inline]
pub fn sort_by<T, F>(v: &mut [T], mut compare: F)
    where F: FnMut(&T, &T) -> Ordering
{
    // Sorting has no meaningful behavior on zero-sized types.
    if size_of::<T>() == 0 {
        return;
    }

    if is_presorted(v, &mut compare) {
        return;
    }

    let len = v.len() as u64;
    let limit = 64 - len.leading_zeros() as usize + 1;

    quicksort(v, &mut compare, None, limit);
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use test;
    use rand::{thread_rng, Rng};
    use std::mem;

    // TODO: Set up Travis
    // TODO: Ensure #![no_std] compatibility
    // TODO: clean up imports
    // TODO: factor out into more modules
    // TODO: more correctness tests
    // TODO: a test with totally random comparison function

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
            sort(&mut b);

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
                b.iter(|| sort(&mut $gen($len)));
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
            sort_by(&mut v, &mut cmp);
            test::black_box(count);
        });
        b.bytes = len as u64 * mem::size_of::<u64>() as u64;
    }
}
