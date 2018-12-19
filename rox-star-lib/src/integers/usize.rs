use std::ops::*;

use crate::nat_int::Int;

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub struct Usize(pub(crate) usize);
type Representation = usize;

impl Usize {
    pub const MAX: Self = Usize(std::usize::MAX);
    fn nb_bits() -> Int { (core::mem::size_of::<usize>() * 8).into() }

    #[inline]
    pub fn into_repr(self) -> Representation {
        self.0
    }

    #[inline]
    pub fn from_repr(x: Representation) -> Self {
        Usize(x)
    }

    #[inline]
    pub fn to_nat(self) -> Int {
        self.0.into()
    }
}

impl Usize {
    #[inline]
    fn add_mod(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 + i2)
    }
}

impl Add for Usize {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() + rhs.to_nat() <= Self::MAX.to_nat());
        self.add_mod(rhs)
    }
}

impl Usize {
    #[inline]
    fn sub_mod(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() - rhs.to_nat() >= 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 - i2)
    }
}

impl Sub for Usize {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() - rhs.to_nat() >= 0.into());
        self.sub_mod(rhs)
    }
}

impl Usize {
    #[inline]
    fn mul_mod(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() * rhs.to_nat() <= Self::MAX.to_nat());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 - i2)
    }
}

impl Mul for Usize {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        verif_pre!(self.to_nat() * rhs.to_nat() <= Self::MAX.to_nat());
        self.mul_mod(rhs)
    }
}

impl Div for Usize {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() != 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 / i2)
    }
}

impl Rem for Usize {
    type Output = Self;
    #[inline]
    fn rem(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() != 0.into());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 % i2)
    }
}

impl Shl for Usize {
    type Output = Self;
    #[inline]
    fn shl(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 << i2)
    }
}

impl Shr for Usize {
    type Output = Self;
    #[inline]
    fn shr(self, rhs: Self) -> Self {
        verif_pre!(rhs.to_nat() < Self::nb_bits());
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 >> i2)
    }
}

impl BitAnd for Usize {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 & i2)
    }
}

impl BitOr for Usize {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 | i2)
    }
}

impl BitXor for Usize {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let i1: Representation = self.into_repr();
        let i2: Representation = rhs.into_repr();
        Self::from_repr(i1 ^ i2)
    }
}

impl Into<Usize> for usize {
    #[inline]
    fn into(self) -> Usize {
        Usize::from_repr(self)
    }
}
