use std::ops::*;

use crate::nat_int::Int;

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub struct U32(pub(crate) u32);
type Representation = u32;

impl U32 {
    pub const MAX: Self = U32(std::u32::MAX);
    fn nb_bits() -> Int { (core::mem::size_of::<u32>() * 8).into() }

    #[inline]
    pub fn into_repr(self) -> Representation {
        self.0
    }

    #[inline]
    pub fn from_repr(x: Representation) -> Self {
        U32(x)
    }

    pub fn to_nat(self) -> Int {
        self.0.into()
    }
}

impl U32 {
    #[inline]
    fn add_mod(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 + i2)
    }
}

impl Add for U32 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() + rhs.to_nat() <= Self::MAX.to_nat());
        self.add_mod(rhs)
    }
}

impl U32 {
    #[inline]
    fn sub_mod(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() - rhs.to_nat() >= 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 - i2)
    }
}

impl Sub for U32 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() - rhs.to_nat() >= 0.into());
        self.sub_mod(rhs)
    }
}

impl U32 {
    fn mul_mod(self, rhs: Self) -> Self {
        #[inline]
        verif_pre!(self.to_nat() * rhs.to_nat() <= Self::MAX.to_nat());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 - i2)
    }
}

impl Mul for U32 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        #[inline]
        verif_pre!(self.to_nat() * rhs.to_nat() <= Self::MAX.to_nat());
        self.mul_mod(rhs)
    }
}

impl Div for U32 {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() != 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 / i2)
    }
}

impl Rem for U32 {
    type Output = Self;
    #[inline]
    fn rem(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() != 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 % i2)
    }
}

impl Shl for U32 {
    type Output = Self;
    #[inline]
    fn shl(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 << i2)
    }
}

impl Shr for U32 {
    type Output = Self;
    #[inline]
    fn shr(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 >> i2)
    }
}

impl BitAnd for U32 {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 & i2)
    }
}

impl BitOr for U32 {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 | i2)
    }
}

impl BitXor for U32 {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 ^ i2)
    }
}

impl Into<U32> for u32 {
    #[inline]
    fn into(self) -> U32 {
        U32::from_repr(self)
    }
}
