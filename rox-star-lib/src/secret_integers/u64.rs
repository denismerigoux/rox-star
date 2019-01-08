use std::num::Wrapping;
use std::ops::*;
use std::fmt::{Display, Formatter, Error};


use crate::nat_int::Int;

#[derive(Clone, Copy, Debug, Default)]
pub struct U64(pub(crate) u64);
type Representation = u64;

impl U64 {
    fn nb_bits () -> Int {
        (std::mem::size_of::<Representation>()*8).into()
    }

    pub fn to_nat(self) -> Int {
        self.0.into()
    }

    pub fn classify<T: Into<Representation>>(x: T) -> Self {
        U64(x.into())
    }

    pub fn declassify<T: From<Representation>>(self) -> T {
        self.0.into()
    }
}

impl Add for U64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64((Wrapping(i1) + Wrapping(i2)).0)
    }
}
impl Sub for U64 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64((Wrapping(i1) - Wrapping(i2)).0)
    }
}

impl Mul for U64 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64((Wrapping(i1) * Wrapping(i2)).0)
    }
}

impl Shl for U64 {
    type Output = Self;
    #[inline]
    fn shl(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64(i1 << i2)
    }
}

impl Shr for U64 {
    type Output = Self;
    #[inline]
    fn shr(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64(i1 >> i2)
    }
}

impl U64 {
    pub fn rotate_left(self, rotval:u32) -> Self {
        verif_pre!(Int::from(rotval) < Self::nb_bits());
        let U64(i) = self;
        U64(i.rotate_left(rotval))
    }

    pub fn rotate_right(self, rotval:u32) -> Self {
        verif_pre!(Int::from(rotval) < Self::nb_bits());
        let U64(i) = self;
        U64(i.rotate_right(rotval))
    }
}

impl BitAnd for U64 {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64(i1 & i2)
    }
}

impl BitOr for U64 {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64(i1 | i2)
    }
}

impl BitXor for U64 {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let U64(i1) = self;
        let U64(i2) = rhs;
        U64(i1 ^ i2)
    }
}

impl Display for U64 {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{:016x}", self.0)
    }
}
