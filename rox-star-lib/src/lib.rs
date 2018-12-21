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

mod nat_int;
mod secret_integers;
mod bytes;


pub use self::nat_int::*;
pub use self::secret_integers::*;
pub use self::bytes::*;
