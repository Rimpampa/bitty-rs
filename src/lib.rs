use std::fmt::{Debug, Display};

#[macro_use]
mod alias;
#[macro_use]
mod max;
#[macro_use]
mod iimpl;
#[macro_use]
mod uimpl;

struct Assert<const COND: bool>;
trait True {}
impl True for Assert<true> {}

/// A constant number of bits
pub struct Bits<const BITS: usize>;

/// Trait for integer wrappers that use another integer types as their base
pub trait BaseType {
    /// Unsigned variant of the base type
    type U;
    /// Signed variant of the base type
    type I;
}

macro_rules! __derive {
    (BaseType for Bits<[$($bits:expr),* $(,)?]> where
        U = $unsigned:ty,
        I = $signed:ty;
    ) => {
        $(impl BaseType for Bits<{$bits}> {
            type U = $unsigned;
            type I = $signed;
        })*
    };

    (Deref for UBits<[$($bits:expr),* $(,)?]>) => {
        __derive!{@deref UBits, $([$bits, bits_base!(@u $bits)]),*}
    };

    (Deref for IBits<[$($bits:expr),* $(,)?]>) => {
        __derive!{@deref IBits, $([$bits, bits_base!(@i $bits)]),*}
    };

    (@deref $type:ident, $([$bits:expr, $base:ty]),*) => {
        $(impl ::core::ops::Deref for $type<$bits> {
            type Target = $base;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        })*

        $(impl ::core::ops::DerefMut for $type<$bits> {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        })*
    }
}

__derive! {
    BaseType for Bits<[1, 2, 3, 4, 5, 6, 7, 8]>
    where U = u8,I = i8;
}

__derive! {
    BaseType for Bits<[9, 10, 11, 12, 13, 14, 15, 16]>
    where U = u16, I = i16;
}

__derive! {
    BaseType for Bits<[
        17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32,
    ]> where U = u32, I = i32;
}

__derive! {
    BaseType for Bits<[
        33, 34, 35, 36, 37, 38, 39, 40,
        41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56,
        57, 58, 59, 60, 61, 62, 63, 64,
    ]> where U = u64, I = i64;
}

macro_rules! bits_base {
    (@u $bits:expr) => { <$crate::Bits<{ $bits }> as $crate::BaseType>::U };
    (@i $bits:expr) => { <$crate::Bits<{ $bits }> as $crate::BaseType>::I };
}

macro_rules! build_macros {
    (UBits<[$($bits:tt),* $(,)?]>) => { $(bits_alias!{@u-macro $bits})* };
    (IBits<[$($bits:tt),* $(,)?]>) => { $(bits_alias!{@i-macro $bits})* };
}

build_macros!{UBits<[
    1,  2,  3,  4,  5,  6,  7, /* 8 , */
    9, 10, 11, 12, 13, 14, 15, /* 16, */
   17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 29, 30, 31, /* 32, */
   33, 34, 35, 36, 37, 38, 39, 40,
   41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55, 56,
   57, 58, 59, 60, 61, 62, 63, /* 64, */
]>}

build_macros!{IBits<[
    1,  2,  3,  4,  5,  6,  7, /* 8 , */
    9, 10, 11, 12, 13, 14, 15, /* 16, */
   17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 29, 30, 31, /* 32, */
   33, 34, 35, 36, 37, 38, 39, 40,
   41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55, 56,
   57, 58, 59, 60, 61, 62, 63, /* 64, */
]>}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct UBits<const BITS: usize>(bits_base!(@u BITS))
where
    Bits<BITS>: BaseType,
    bits_base!(@u BITS): Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Debug + Display;

uimpl! {UBits<[
     1,  2,  3,  4,  5,  6,  7, /* 8 , */
     9, 10, 11, 12, 13, 14, 15, /* 16, */
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, /* 32, */
    33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56,
    57, 58, 59, 60, 61, 62, 63, /* 64, */
]>}

__derive!(Deref for UBits<[8, 16, 32, 64]>);

pub struct IBits<const BITS: usize>(bits_base!(@i BITS))
where
    Bits<BITS>: BaseType,
    bits_base!(@u BITS): Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Debug + Display;

// iimpl!(
//      1,  2,  3,  4,  5,  6,  7, /*  8, */
//      9, 10, 11, 12, 13, 14, 15, /* 16, */
//     17, 18, 19, 20, 21, 22, 23, 24,
//     25, 26, 27, 28, 29, 30, 31, /* 32, */
//     33, 34, 35, 36, 37, 38, 39, 40,
//     41, 42, 43, 44, 45, 46, 47, 48,
//     49, 50, 51, 52, 53, 54, 55, 56,
//     57, 58, 59, 60, 61, 62, 63, /* 64, */
// );

__derive!(Deref for IBits<[8, 16, 32, 64]>);
