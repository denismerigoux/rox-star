// Natural integers type

use std::ops::*;

use num_bigint::{BigInt};
use num_traits::{Pow, One, identities::Zero};

#[derive(Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct Int(BigInt);

impl Add for Int {
    type Output = Int;

    fn add(self, rhs:Int) -> Int {
        Int(self.0 + rhs.0)
    }
}

impl Sub for Int {
    type Output = Int;

    fn sub(self, rhs:Int) -> Int {
        Int(self.0 - rhs.0)
    }
}

impl Mul for Int {
    type Output = Int;

    fn mul(self, rhs:Int) -> Int {
        Int(self.0 * rhs.0)
    }
}

impl Div for Int {
    type Output = Int;

    //#[requires(| self, rhs | => rhs != 0.into())]
    fn div(self, rhs:Int) -> Int {
        verif_pre!(rhs != 0.into());
        Int(self.0 / rhs.0)
    }
}

impl Rem for Int {
    type Output = Int;

    //#[requires(| self, rhs | => rhs != 0.into())]
    fn rem(self, rhs:Int) -> Int {
        verif_pre!(rhs != 0.into());
        Int(self.0 % rhs.0)
    }
}


impl Pow<Int> for Int {
    type Output = Int;
    //#[requires (|self, exp| => exp >= 0)]
    fn pow(self, exp: Int) -> Int {
        verif_pre!(exp >= 0.into());
        let mut exp = exp.0;
        if exp == BigInt::zero() {
                   return Int(BigInt::one());
               }
               let mut base = self.0.clone();

               while exp.clone() & BigInt::one() == BigInt::zero() {
                   base = &base * &base;
                   exp >>= 1;
               }

               if exp == BigInt::one() {
                   return Int(base);
               }

               let mut acc = base.clone();
               while exp.clone() > BigInt::one() {
                   exp >>= 1;
                   base = &base * &base;
                   if exp.clone() & BigInt::one() == BigInt::one() {
                       acc = &acc * &base;
                   }
               }
               Int(acc)
    }
}

impl From<u128> for Int {
    fn from(x:u128) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<u64> for Int {
    fn from(x:u64) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<u32> for Int {
    fn from(x:u32) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<u8> for Int {
    fn from(x:u8) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<usize> for Int {
    fn from(x:usize) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<i128> for Int {
    fn from(x:i128) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<i64> for Int {
    fn from(x:i64) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<i32> for Int {
    fn from(x:i32) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<i8> for Int {
    fn from(x:i8) -> Int {
        Int(BigInt::from(x))
    }
}

impl From<isize> for Int {
    fn from(x:isize) -> Int {
        Int(BigInt::from(x))
    }
}
