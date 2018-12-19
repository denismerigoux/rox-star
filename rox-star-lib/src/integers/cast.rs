use crate::integers::*;

impl From<U32> for Usize {
    #[inline]
    fn from(x: U32) -> Usize {
        Usize(x.0 as usize)
    }
}

impl From<Usize> for U32 {
    #[inline]
    fn from(x: Usize) -> U32 {
        verif_pre!(x.to_nat() <= U32::MAX.to_nat());
        U32(x.0 as u32)
    }
}

impl From<U8> for Usize {
    #[inline]
    fn from(x: U8) -> Usize {
        Usize(x.0 as usize)
    }
}
