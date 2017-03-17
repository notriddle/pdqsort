use super::sort_by;

/// Sorts floating point number.
/// The ordering used is
/// | -inf | < 0 | -0 | +0 | > 0 | +inf | NaN |
///
/// # Example
///
/// ```
/// let mut v = [-5.0, 4.0, 1.0, -3.0, 2.0];
///
/// pdqsort::float::sort(&mut v);
/// assert!(v == [-5.0, -3.0, 1.0, 2.0, 4.0]);
/// ```

pub fn sort<T: Float>(v: &mut [T]) {
    /*
     * We don't have hardware support for a total order on floats. NaN is not
     * smaller or greater than any number. We want NaNs to be last, so we could
     * just use is_nan() in the comparison function. It turns out that hurts
     * performance a lot, and in most cases we probably don't have any NaNs anyway.
     * 
     * The solution is to first move all NaNs to the end of the array, and the
     * sort the remainder with efficient comparisons. After sorting, the zeros
     * might be in the wrong order, since -0 and 0 compare equal, but we want
     * -0 to be sorted before 0. We binary search to find the zero interval fix
     * them up.
     */

    if v.len() <= 1 {
        return;
    }

    // First we move all NaNs to the end
    let mut rnan = v.len() - 1;
    // Skip NaNs already in place
    while rnan > 0 && v[rnan].is_nan() {
        rnan -= 1;
    }
    let mut p = rnan;
    while p > 0 {
        p -= 1;
        if v[p].is_nan() {
            v.swap(p, rnan);
            rnan -= 1;
        }
    }

    // Sort the non-NaN part with efficient comparisons
    sort_by(&mut v[..rnan + 1], &|x: &T, y: &T|
        match x.partial_cmp(y) {
            Some(ord) => ord,
            None      => unsafe { unreachable() }
        });


    let left = find_first_zero(&v[..rnan + 1]);

    // Count zeros of each type and then fill them in in the right order
    let mut zeros = 0;
    let mut neg_zeros = 0;
    for x in v[left..].iter() {
        if *x != T::zero() {
            break;
        }
        if x.is_sign_negative() {
            neg_zeros += 1;
        } else {
            zeros += 1;
        }
    }
    for x in v[left..].iter_mut() {
        if neg_zeros > 0 {
            *x = Float::neg_zero();
            neg_zeros -= 1;
        } else if zeros > 0 {
             *x = T::zero();
             zeros -= 1;
        } else {
            break;
        }
    }
}

/// Find the first zero in `v`.
/// If there is no zero, it return v.len() - 1
fn find_first_zero<T: Float>(v: &[T]) -> usize {
    if v.len() == 0 { return 0; }
    let mut hi = v.len() - 1;
    let mut left = 0;

    while left < hi {
        let mid = ((hi - left) / 2) + left;
        if v[mid] < T::zero() {
            left = mid + 1;
        } else {
            hi = mid;
        }
    }

    while left < v.len() && v[left] < T::zero() {
        left += 1;
    }
    return left;
}

/// A value that can be sorted as a floating-point number.
///
/// This cannot (safely) use the trait in `num_traits`,
/// because this sorting algorithm will invoke UB
/// if `Float::is_nan()` returns false and `PartialOrd::cmp` returns `None`.
pub unsafe trait Float: PartialOrd + Copy {
    fn is_nan(self) -> bool;
    fn zero() -> Self;
    fn neg_zero() -> Self;
    fn is_sign_negative(self) -> bool;
}

unsafe impl Float for f32 {
    fn is_nan(self) -> bool { self != self }
    fn zero() -> Self { 0.0 }
    fn neg_zero() -> Self { -0.0 }
    fn is_sign_negative(self) -> bool { ::core::num::Float::is_sign_negative(self) }
}

unsafe impl Float for f64 {
    fn is_nan(self) -> bool { self != self }
    fn zero() -> Self { 0.0 }
    fn neg_zero() -> Self { -0.0 }
    fn is_sign_negative(self) -> bool { ::core::num::Float::is_sign_negative(self) }
}

/// An `unreachable()` intrinsic.
#[inline(always)]
unsafe fn unreachable() -> ! {
    enum Void {}
    let void: Void = ::core::mem::transmute(());
    match void {}
}

#[cfg(test)]
mod tests {
    extern crate std;
    extern crate rand;

    use self::rand::{Rng, thread_rng};
    use self::std::prelude::v1::*;

    #[test]
    fn test_numbers() {
        let mut rng = thread_rng();
        for n in 0..16 {
            for l in 0..16 {
                let mut v = rng.gen_iter::<f64>()
                    .map(|x| x % (1 << l) as i64 as f64)
                    .take((1 << n))
                    .collect::<Vec<_>>();
                let mut v1 = v.clone();

                super::sort(&mut v);
                assert!(v.windows(2).all(|w| w[0] <= w[1]));

                v1.sort_by(|a, b| a.partial_cmp(b).unwrap());
                assert!(v1.windows(2).all(|w| w[0] <= w[1]));

                v1.sort_by(|a, b| b.partial_cmp(a).unwrap());
                assert!(v1.windows(2).all(|w| w[0] >= w[1]));
            }
        }

        let mut v = [5.0];
        super::sort(&mut v);
        assert!(v == [5.0]);
    }

    #[test]
    fn test_nan() {
        let nan = ::core::f64::NAN;
        let mut v = [-1.0, 5.0, 0.0, -0.0, nan, 1.5, nan, 3.7];
        super::sort(&mut v);
        assert!(v[0] == -1.0);
        assert!(v[1] == 0.0 && v[1].is_sign_negative());
        assert!(v[2] == 0.0 && !v[2].is_sign_negative());
        assert!(v[3] == 1.5);
        assert!(v[4] == 3.7);
        assert!(v[5] == 5.0);
        assert!(v[6].is_nan());
        assert!(v[7].is_nan());
    }
}