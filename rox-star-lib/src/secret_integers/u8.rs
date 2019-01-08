use std::num::Wrapping;
use std::ops::*;
use std::fmt::{Display, Formatter, Error};

use crate::nat_int::Int;

#[derive(Clone, Copy, Debug, Default)]
pub struct U8(pub(crate) u8);
type Representation = u8;

impl U8 {
    fn nb_bits () -> Int {
        (std::mem::size_of::<Representation>()*8).into()
    }

    pub fn to_nat(self) -> Int {
        self.0.into()
    }

    pub fn classify<T: Into<Representation>>(x: T) -> Self {
        U8(x.into())
    }

    pub fn declassify<T: From<Representation>>(self) -> T {
        self.0.into()
    }
}

impl Add for U8 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8((Wrapping(i1) + Wrapping(i2)).0)
    }
}

impl Sub for U8 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8((Wrapping(i1) - Wrapping(i2)).0)
    }
}

impl Mul for U8 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8((Wrapping(i1) * Wrapping(i2)).0)
    }
}

impl Shl for U8 {
    type Output = Self;
    #[inline]
    fn shl(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8(i1 << i2)
    }
}

impl Shr for U8 {
    type Output = Self;
    #[inline]
    fn shr(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8(i1 >> i2)
    }
}

impl U8 {
    pub fn rotate_left(self, rotval:u32) -> Self {
        verif_pre!(Int::from(rotval) < Self::nb_bits());
        let U8(i) = self;
        U8(i.rotate_left(rotval))
    }

    pub fn rotate_right(self, rotval:u32) -> Self {
        verif_pre!(Int::from(rotval) < Self::nb_bits());
        let U8(i) = self;
        U8(i.rotate_right(rotval))
    }
}

impl BitAnd for U8 {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8(i1 & i2)
    }
}

impl BitOr for U8 {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8(i1 | i2)
    }
}

impl BitXor for U8 {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let U8(i1) = self;
        let U8(i2) = rhs;
        U8(i1 ^ i2)
    }
}

impl BitXorAssign for U8 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs
    }
}

impl Display for U8 {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{:02x}", self.0)
    }
}
