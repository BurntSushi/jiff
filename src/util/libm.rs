/*!
A no-std module for some floating point operations.

These were vendored from the [`libm`] crate. For no-std specifically, I
wouldn't necessarily mind depending on `libm`, but I don't think there's a
way to express "only depend on a crate if some on-by-default feature is not
enabled."

We also very intentionally have very minimal floating point requirements. It's
used for `Span::total` where it's part of the API and thus necessary. It's also
used when rounding in some cases, although I would like to remove that use of
floating point. And now it's also used in parts of `SignedDuration`.

[`libm`]: https://github.com/rust-lang/libm
*/

pub(crate) trait Float {
    fn abs(self) -> Self;
    fn ceil(self) -> Self;
    fn floor(self) -> Self;
    fn round(self) -> Self;
    fn signum(self) -> Self;
    fn trunc(self) -> Self;
    fn fract(self) -> Self;
}

macro_rules! force_eval {
    ($e:expr) => {
        core::ptr::read_volatile(&$e)
    };
}

const TOINT64: f64 = 1. / f64::EPSILON;

impl Float for f64 {
    fn abs(self) -> f64 {
        if self.is_sign_negative() {
            -self
        } else {
            self
        }
    }

    fn ceil(self) -> f64 {
        let x = self;
        let u: u64 = x.to_bits();
        let e: i64 = (u >> 52 & 0x7ff) as i64;
        let y: f64;

        if e >= 0x3ff + 52 || x == 0. {
            return x;
        }
        // y = int(x) - x, where int(x) is an integer neighbor of x
        y = if (u >> 63) != 0 {
            x - TOINT64 + TOINT64 - x
        } else {
            x + TOINT64 - TOINT64 - x
        };
        // special case because of non-nearest rounding modes
        if e < 0x3ff {
            unsafe {
                force_eval!(y);
            }
            return if (u >> 63) != 0 { -0. } else { 1. };
        }
        if y < 0. {
            x + y + 1.
        } else {
            x + y
        }
    }

    fn floor(self) -> f64 {
        let x = self;
        let ui = x.to_bits();
        let e = ((ui >> 52) & 0x7ff) as i32;

        if (e >= 0x3ff + 52) || (x == 0.) {
            return x;
        }
        /* y = int(x) - x, where int(x) is an integer neighbor of x */
        let y = if (ui >> 63) != 0 {
            x - TOINT64 + TOINT64 - x
        } else {
            x + TOINT64 - TOINT64 - x
        };
        /* special case because of non-nearest rounding modes */
        if e < 0x3ff {
            unsafe {
                force_eval!(y);
            }
            return if (ui >> 63) != 0 { -1. } else { 0. };
        }
        if y > 0. {
            x + y - 1.
        } else {
            x + y
        }
    }

    fn round(self) -> f64 {
        (self + copysign64(0.5 - 0.25 * f64::EPSILON, self)).trunc()
    }

    fn signum(self) -> f64 {
        if self.is_nan() {
            Self::NAN
        } else {
            copysign64(1.0, self)
        }
    }

    fn trunc(self) -> f64 {
        let x = self;
        let x1p120 = f64::from_bits(0x4770000000000000); // 0x1p120f === 2 ^ 120

        let mut i: u64 = x.to_bits();
        let mut e: i64 = (i >> 52 & 0x7ff) as i64 - 0x3ff + 12;
        let m: u64;

        if e >= 52 + 12 {
            return x;
        }
        if e < 12 {
            e = 1;
        }
        m = -1i64 as u64 >> e;
        if (i & m) == 0 {
            return x;
        }
        unsafe {
            force_eval!(x + x1p120);
        }
        i &= !m;
        f64::from_bits(i)
    }

    fn fract(self) -> f64 {
        self - self.trunc()
    }
}

fn copysign64(x: f64, y: f64) -> f64 {
    let mut ux = x.to_bits();
    let uy = y.to_bits();
    ux &= (!0) >> 1;
    ux |= uy & (1 << 63);
    f64::from_bits(ux)
}
