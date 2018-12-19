extern crate num_bigint;
extern crate num_traits;


#[macro_use]
mod macros {
    #[macro_export]
    macro_rules! verif_assert {
        ($e:expr) => { assert!($e) }
    }
    #[macro_export]
    macro_rules! verif_pre {
        ($e:expr) => { assert!($e) }
    }
    #[macro_export]
    macro_rules! verif_post {
        ($e:expr) => { assert!($e) }
    }
}

mod vec;
mod array;
mod nat_int;
mod integers;


pub use self::array::*;
pub use self::vec::*;
pub use self::nat_int::*;
pub use self::integers::*;
