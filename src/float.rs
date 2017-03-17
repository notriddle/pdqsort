use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::mem::transmute;

/// Order floating point numbers, into this ordering:
///
/// NaN -inf <0 -0 +0 >0 +inf NaN
#[derive(Clone, Copy)]
pub struct FloatOrd<T>(T);

macro_rules! float_ord_impl {
    ($f:ident, $i:ident, $n:expr) => {
        impl FloatOrd<$f> {
            fn convert(self) -> $i {
                let u = unsafe { transmute::<$f, $i>(self.0) };
                let bit = 1 << ($n - 1);
                if u & bit == 0 {
                    u | bit
                } else {
                    !u
                }
            }
        }
        impl PartialEq for FloatOrd<$f> {
            fn eq(&self, other: &Self) -> bool {
                self.convert() == other.convert()
            }
        }
        impl Eq for FloatOrd<$f> {}
        impl PartialOrd for FloatOrd<$f> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.convert().partial_cmp(&other.convert())
            }
        }
        impl Ord for FloatOrd<$f> {
            fn cmp(&self, other: &Self) -> Ordering {
                self.convert().cmp(&other.convert())
            }
        }
    }
}

float_ord_impl!(f32, u32, 32);
float_ord_impl!(f64, u64, 64);

/// Sorts floating point number.
///
/// # Example
///
/// ```
/// let mut v = [-5.0, 4.0, 1.0, -3.0, 2.0];
///
/// pdqsort::float::sort(&mut v);
/// assert!(v == [-5.0, -3.0, 1.0, 2.0, 4.0]);
/// ```
pub fn sort<T>(v: &mut [T]) where FloatOrd<T>: Ord {
    let v_: &mut [FloatOrd<T>] = unsafe { transmute(v) };
    super::sort(v_);
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