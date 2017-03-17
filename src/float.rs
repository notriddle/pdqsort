use super::sort_by;

pub use core::cmp::{Ordering, PartialEq, PartialOrd};

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
    sort_by(&mut v[..rnan + 1], |x: &T, y: &T|
        match x.partial_cmp(y) {
            Some(ord) => ord,
            None      => unsafe { unreachable() }
        });


    let left = find_first_zero(&v[..rnan + 1]);

    // Count zeros of each type and then fill them in in the right order
    let mut zeros = false;
    let mut neg_zeros = false;
    let mut right = left;
    for x in v[left..].iter() {
        if !x.is_zero() {
            break;
        }
        if x.is_sign_negative() {
            neg_zeros = true;
        } else {
            zeros = true;
        }
        right += 1;
    }
    if zeros && neg_zeros {
        sort_by(&mut v[left..right], |x: &T, y: &T|
            match (x.is_sign_negative(), y.is_sign_negative()) {
                (true, false) => Ordering::Less,
                (false, true) => Ordering::Greater,
                _ => Ordering::Equal,
            });
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
        if v[mid].is_lt_zero() {
            left = mid + 1;
        } else {
            hi = mid;
        }
    }

    while left < v.len() && v[left].is_lt_zero() {
        left += 1;
    }
    return left;
}

/// A value that can be sorted as a floating-point number.
///
/// This cannot (safely) use the trait in `num_traits`,
/// because this sorting algorithm will invoke UB
/// if `Float::is_nan()` returns false and `PartialOrd::cmp` returns `None`.
pub unsafe trait Float: PartialOrd {
    fn is_nan(&self) -> bool;
    fn is_zero(&self) -> bool;
    fn is_lt_zero(&self) -> bool;
    fn is_sign_negative(&self) -> bool;
}

unsafe impl Float for f32 {
    fn is_nan(&self) -> bool { self != self }
    fn is_zero(&self) -> bool { *self == 0.0 }
    fn is_lt_zero(&self) -> bool { *self < 0.0 }
    fn is_sign_negative(&self) -> bool { ::core::num::Float::is_sign_negative(*self) }
}

unsafe impl Float for f64 {
    fn is_nan(&self) -> bool { self != self }
    fn is_zero(&self) -> bool { *self == 0.0 }
    fn is_lt_zero(&self) -> bool { *self < 0.0 }
    fn is_sign_negative(&self) -> bool { ::core::num::Float::is_sign_negative(*self) }
}

/// Define a float member to sort by.
///
/// # Example
///
/// ```
/// #[macro_use] extern crate pdqsort;
/// struct Item {
///     key: f64,
/// }
/// pdqsort_float_member!(Item, key);
/// # fn main() {
/// let mut v = [ Item{ key: 2.0 }, Item{ key: 1.0 } ];
/// pdqsort::float::sort(&mut v);
/// assert!(1.0 == v[0].key);
/// assert!(2.0 == v[1].key);
/// # }
/// ```
#[macro_export]
macro_rules! pdqsort_float_member {
    ($ty:ident, $member:ident) => {
        impl $crate::float::PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                $crate::float::PartialEq::eq(&self.$member, &other.$member)
            }
        }
        impl $crate::float::PartialOrd for $ty {
            fn partial_cmp(&self, other: &Self) -> Option<$crate::float::Ordering> {
                $crate::float::PartialOrd::partial_cmp(&self.$member, &other.$member)
            }
        }
        unsafe impl $crate::float::Float for $ty {
            fn is_nan(&self) -> bool {
                $crate::float::Float::is_nan(&self.$member)
            }
            fn is_zero(&self) -> bool {
                $crate::float::Float::is_zero(&self.$member)
            }
            fn is_lt_zero(&self) -> bool {
                $crate::float::Float::is_lt_zero(&self.$member)
            }
            fn is_sign_negative(&self) -> bool {
                $crate::float::Float::is_sign_negative(&self.$member)
            }
        }
    }
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