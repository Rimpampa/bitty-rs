macro_rules! uimpl_bitty {
    ($self_type:ty, $bits:tt) => {
        /// The smallest value that can be represented by this integer type,
        /// stored with the base type instead of
        #[doc = concat!("[`", stringify!($self_type), "`]")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MIN, 0);")]
        /// ```
        const BASE_MIN: bits_base!(@u $bits) = 0;

        /// The largest value that can be represented by this integer type,
        #[doc = concat!("2<sup>", $bits, "</sup> &minus; 1,")]
        /// stored with the base type instead of
        #[doc = concat!("[`", stringify!($self_type), "`]")]
        ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX, ", stringify!($max_value), ");")]
        // /// ```
        const BASE_MAX: bits_base!(@u $bits) = bits_max!($bits) as bits_base!(@u $bits);

        /// Number of bits of padding
        const PADDING_BITS: u32 = <bits_base!(@u $bits)>::BITS - $bits;

        /// Bitmask that covers the padding bits.
        const PADDING_MASK: bits_base!(@u $bits) = <bits_base!(@u $bits)>::MAX - Self::BASE_MAX;

        /// Bitmask that covers [`PADDING_BITS`](Self::PADDING_BITS) bits
        const PADDING_BITS_MASK: bits_base!(@u $bits) = Self::PADDING_MASK >> Self::PADDING_MASK.trailing_zeros();

        /// Converts a
        #[doc = concat!("[`", stringify!($underlying_type), "`]")]
        /// into a
        #[doc = concat!("[`", stringify!($self_type), "`]")]
        /// while checking that the value fits
        ///
        // TODO: add example
        pub const fn cast_bits_checked(value: bits_base!(@u $bits)) -> Option<Self> {
            if value > Self::BASE_MAX {
                None
            } else {
                Some(Self(value))
            }
        }

        /// Converts a
        #[doc = concat!("[`", stringify!($underlying_type), "`]")]
        /// into a
        #[doc = concat!("[`", stringify!($self_type), "`]")]
        /// 
        /// # Panics
        /// 
        /// This functions panics if the value doesn't fit
        ///
        // TODO: add example
        pub const fn cast_bits(value: bits_base!(@u $bits)) -> Self {
            if value > Self::BASE_MAX {
                panic!("the value is too big")
            }
            Self(value)
        }
    };
}

macro_rules! uimpl_consts {
    ($self_type:ty, $bits:tt) => {
        /// The smallest value that can be represented by this integer type.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MIN, 0);")]
        /// ```
        pub const MIN: Self = Self::cast_bits(Self::BASE_MIN);

        /// The largest value that can be represented by this integer type,
        #[doc = concat!("2<sup>", $bits, "</sup> &minus; 1.")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX, ", bits_max!(@str $bits), ");")]
        /// ```
        pub const MAX: Self = Self::cast_bits(Self::BASE_MAX);

        /// The size of this integer type in bits.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::BITS, ", stringify!($bits), ");")]
        /// ```
        pub const BITS: u32 = $bits;
    }
}

macro_rules! uimpl_bits {
    ($self_type:ty, $bits:expr) => {
        /// Returns the number of ones in the binary representation of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0b01001100", stringify!($self_type), ";")]
        ///
        /// assert_eq!(n.count_ones(), 3);
        /// ```
        #[doc(alias = "popcount")]
        #[doc(alias = "popcnt")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn count_ones(self) -> u32 {
            self.0.count_ones()
        }

        /// Returns the number of zeros in the binary representation of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.count_zeros(), 0);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn count_zeros(self) -> u32 {
            Self::BITS - self.count_ones()
        }

        /// Returns the number of leading zeros in the binary representation of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = ", stringify!($self_type), "::MAX >> 2;")]
        ///
        /// assert_eq!(n.leading_zeros(), 2);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn leading_zeros(self) -> u32 {
            self.0.leading_zeros() - Self::PADDING_BITS
        }

        /// Returns the number of trailing zeros in the binary representation
        /// of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0b0101000", stringify!($self_type), ";")]
        ///
        /// assert_eq!(n.trailing_zeros(), 3);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn trailing_zeros(self) -> u32 {
            self.0.trailing_zeros()
        }

        /// Returns the number of leading ones in the binary representation of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = !(", stringify!($self_type), "::MAX >> 2);")]
        ///
        /// assert_eq!(n.leading_ones(), 2);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn leading_ones(self) -> u32 {
            (!self.0 & Self::BASE_MAX).leading_zeros()
        }

        /// Returns the number of trailing ones in the binary representation
        /// of `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0b1010111", stringify!($self_type), ";")]
        ///
        /// assert_eq!(n.trailing_ones(), 3);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn trailing_ones(self) -> u32 {
            (!self.0 & Self::BASE_MAX).trailing_zeros()
        }

        // /// Shifts the bits to the left by a specified amount, `n`,
        // /// wrapping the truncated bits to the end of the resulting integer.
        // ///
        // /// Please note this isn't the same operation as the `<<` shifting operator!
        // ///
        // // /// # Examples
        // // ///
        // // /// Basic usage:
        // // ///
        // // /// ```
        // // #[doc = concat!("let n = ", $rot_op, stringify!($self_type), ";")]
        // // #[doc = concat!("let m = ", $rot_result, ";")]
        // // ///
        // // #[doc = concat!("assert_eq!(n.rotate_left(", $rot, "), m);")]
        // // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const fn rotate_left(self, n: u32) -> Self {
        //     ::core::intrinsics::rotate_left(self.0, n)
        // }

        // /// Shifts the bits to the right by a specified amount, `n`,
        // /// wrapping the truncated bits to the beginning of the resulting
        // /// integer.
        // ///
        // /// Please note this isn't the same operation as the `>>` shifting operator!
        // ///
        // // /// # Examples
        // // ///
        // // /// Basic usage:
        // // ///
        // // /// ```
        // // #[doc = concat!("let n = ", $rot_result, stringify!($self_type), ";")]
        // // #[doc = concat!("let m = ", $rot_op, ";")]
        // // ///
        // // #[doc = concat!("assert_eq!(n.rotate_right(", $rot, "), m);")]
        // // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const fn rotate_right(self, n: u32) -> Self {
        //     ::core::intrinsics::rotate_right(self, n as $SelfT)
        // }

        /// Reverses the order of bits in the integer. The least significant bit becomes the most significant bit,
        ///                 second least-significant bit becomes second most-significant bit, etc.
        ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // #[doc = concat!("let n = ", $swap_op, stringify!($self_type), ";")]
        // /// let m = n.reverse_bits();
        // ///
        // #[doc = concat!("assert_eq!(m, ", $reversed, ");")]
        // #[doc = concat!("assert_eq!(0, 0", stringify!($self_type), ".reverse_bits());")]
        // /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn reverse_bits(self) -> Self {
            Self(self.0.reverse_bits() >> Self::PADDING_BITS)
        }

        /// Returns `true` if and only if `self == 2^k` for some `k`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert!(", stringify!($self_type), "::cast_bits(16).is_power_of_two());")]
        #[doc = concat!("assert!(!", stringify!($self_type), "::cast_bits(10).is_power_of_two());")]
        /// ```
        #[must_use]
        #[inline(always)]
        pub const fn is_power_of_two(self) -> bool {
            self.count_ones() == 1
        }

        /// Checked shift left. Computes `self << rhs`, returning `None`
        /// if `rhs` is larger than or equal to the number of bits in `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x1).checked_shl(4), Some(0x10));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x10).checked_shl(129), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
            // TODO: use the real one
            use std::convert::identity as unlikely;
            let (a, b) = self.overflowing_shl(rhs);
            if unlikely(b) {None} else {Some(a)}
        }

        // /// Unchecked shift left. Computes `self << rhs`, assuming that
        // /// `rhs` is less than the number of bits in `self`.
        // ///
        // /// # Safety
        // ///
        // /// This results in undefined behavior if `rhs` is larger than
        // /// or equal to the number of bits in `self`,
        // /// i.e. when [`checked_shl`] would return `None`.
        // ///
        // #[doc = concat!("[`checked_shl`]: ", stringify!($self_type), "::checked_shl")]
        // // #[unstable(
        // //     feature = "unchecked_math",
        // //     reason = "niche optimization path",
        // //     issue = "85122",
        // // )]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const unsafe fn unchecked_shl(self, rhs: Self) -> Self {
        //     // SAFETY: the caller must uphold the safety contract for
        //     // `unchecked_shl`.
        //     unsafe { ::core::intrinsics::unchecked_shl(self, rhs) }
        // }

        /// Checked shift right. Computes `self >> rhs`, returning `None`
        /// if `rhs` is larger than or equal to the number of bits in `self`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x10).checked_shr(4), Some(0x1));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x10).checked_shr(129), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
            // TODO: use the real one
            use std::convert::identity as unlikely;
            let (a, b) = self.overflowing_shr(rhs);
            if unlikely(b) {None} else {Some(a)}
        }

        // /// Unchecked shift right. Computes `self >> rhs`, assuming that
        // /// `rhs` is less than the number of bits in `self`.
        // ///
        // /// # Safety
        // ///
        // /// This results in undefined behavior if `rhs` is larger than
        // /// or equal to the number of bits in `self`,
        // /// i.e. when [`checked_shr`] would return `None`.
        // ///
        // #[doc = concat!("[`checked_shr`]: ", stringify!($self_type), "::checked_shr")]
        // // #[unstable(
        // //     feature = "unchecked_math",
        // //     reason = "niche optimization path",
        // //     issue = "85122",
        // // )]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const unsafe fn unchecked_shr(self, rhs: Self) -> Self {
        //     // SAFETY: the caller must uphold the safety contract for
        //     // `unchecked_shr`.
        //     unsafe { ::core::intrinsics::unchecked_shr(self, rhs) }
        // }

        /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
        /// where `mask` removes any high-order bits of `rhs` that
        /// would cause the shift to exceed the bitwidth of the type.
        ///
        /// Note that this is *not* the same as a rotate-left; the
        /// RHS of a wrapping shift-left is restricted to the range
        /// of the type, rather than the bits shifted out of the LHS
        /// being returned to the other end. The primitive integer
        /// types all implement a [`rotate_left`](Self::rotate_left) function,
        /// which may be what you want instead.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(1).wrapping_shl(7), 128);")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(1).wrapping_shl(128), 1);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_shl(self, rhs: u32) -> Self {
            Self(self.0 << (rhs % $bits))
        }

        /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
        /// where `mask` removes any high-order bits of `rhs` that
        /// would cause the shift to exceed the bitwidth of the type.
        ///
        /// Note that this is *not* the same as a rotate-right; the
        /// RHS of a wrapping shift-right is restricted to the range
        /// of the type, rather than the bits shifted out of the LHS
        /// being returned to the other end. The primitive integer
        /// types all implement a [`rotate_right`](Self::rotate_right) function,
        /// which may be what you want instead.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(128).wrapping_shr(7), 1);")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(128).wrapping_shr(128), 128);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_shr(self, rhs: u32) -> Self {
            Self(self.0 >> (rhs % $bits))
        }

        /// Shifts self left by `rhs` bits.
        ///
        /// Returns a tuple of the shifted version of self along with a boolean
        /// indicating whether the shift value was larger than or equal to the
        /// number of bits. If the shift value is too large, then value is
        /// masked (N-1) where N is the number of bits, and this value is then
        /// used to perform the shift.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x1).overflowing_shl(4), (0x10, false));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x1).overflowing_shl(132), (0x10, true));")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shl(rhs), (rhs >= $bits))
        }

        /// Shifts self right by `rhs` bits.
        ///
        /// Returns a tuple of the shifted version of self along with a boolean
        /// indicating whether the shift value was larger than or equal to the
        /// number of bits. If the shift value is too large, then value is
        /// masked (N-1) where N is the number of bits, and this value is then
        /// used to perform the shift.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x10).overflowing_shr(4), (0x1, false));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(0x10).overflowing_shr(132), (0x1, true));")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shr(rhs), (rhs >= $bits))
        }
    }
}

#[allow(unused)]
macro_rules! uimpl_bytes {
    () => {
        /// Reverses the byte order of the integer.
        ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // #[doc = concat!("let n = ", $swap_op, stringify!($SelfT), ";")]
        // /// let m = n.swap_bytes();
        // ///
        // #[doc = concat!("assert_eq!(m, ", $swapped, ");")]
        // /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn swap_bytes(self) -> Self {
            ::core::intrinsics::bswap(self as $ActualT) as Self
        }

        /// Converts an integer from big endian to the target's endianness.
        ///
        /// On big endian this is a no-op. On little endian the bytes are
        /// swapped.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0x1A", stringify!($SelfT), ";")]
        ///
        /// if cfg!(target_endian = "big") {
        #[doc = concat!("    assert_eq!(", stringify!($SelfT), "::from_be(n), n)")]
        /// } else {
        #[doc = concat!("    assert_eq!(", stringify!($SelfT), "::from_be(n), n.swap_bytes())")]
        /// }
        /// ```
        #[must_use]
        #[inline(always)]
        pub const fn from_be(x: Self) -> Self {
            #[cfg(target_endian = "big")]
            {
                x
            }
            #[cfg(not(target_endian = "big"))]
            {
                x.swap_bytes()
            }
        }

        /// Converts an integer from little endian to the target's endianness.
        ///
        /// On little endian this is a no-op. On big endian the bytes are
        /// swapped.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0x1A", stringify!($SelfT), ";")]
        ///
        /// if cfg!(target_endian = "little") {
        #[doc = concat!("    assert_eq!(", stringify!($SelfT), "::from_le(n), n)")]
        /// } else {
        #[doc = concat!("    assert_eq!(", stringify!($SelfT), "::from_le(n), n.swap_bytes())")]
        /// }
        /// ```
        #[must_use]
        #[inline(always)]
        pub const fn from_le(x: Self) -> Self {
            #[cfg(target_endian = "little")]
            {
                x
            }
            #[cfg(not(target_endian = "little"))]
            {
                x.swap_bytes()
            }
        }

        /// Converts `self` to big endian from the target's endianness.
        ///
        /// On big endian this is a no-op. On little endian the bytes are
        /// swapped.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0x1A", stringify!($SelfT), ";")]
        ///
        /// if cfg!(target_endian = "big") {
        ///     assert_eq!(n.to_be(), n)
        /// } else {
        ///     assert_eq!(n.to_be(), n.swap_bytes())
        /// }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn to_be(self) -> Self { // or not to be?
            #[cfg(target_endian = "big")]
            {
                self
            }
            #[cfg(not(target_endian = "big"))]
            {
                self.swap_bytes()
            }
        }

        /// Converts `self` to little endian from the target's endianness.
        ///
        /// On little endian this is a no-op. On big endian the bytes are
        /// swapped.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("let n = 0x1A", stringify!($SelfT), ";")]
        ///
        /// if cfg!(target_endian = "little") {
        ///     assert_eq!(n.to_le(), n)
        /// } else {
        ///     assert_eq!(n.to_le(), n.swap_bytes())
        /// }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn to_le(self) -> Self {
            #[cfg(target_endian = "little")]
            {
                self
            }
            #[cfg(not(target_endian = "little"))]
            {
                self.swap_bytes()
            }
        }

        /// Return the memory representation of this integer as a byte array in
        /// big-endian (network) byte order.
        ///
        // #[doc = $to_xe_bytes_doc]
        ///
        // /// # Examples
        // ///
        // /// ```
        // #[doc = concat!("let bytes = ", $swap_op, stringify!($SelfT), ".to_be_bytes();")]
        // #[doc = concat!("assert_eq!(bytes, ", $be_bytes, ");")]
        // /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn to_be_bytes(self) -> [u8; ::core::mem::size_of::<Self>()] {
            self.to_be().to_ne_bytes()
        }

        /// Return the memory representation of this integer as a byte array in
        /// little-endian byte order.
        ///
        // #[doc = $to_xe_bytes_doc]
        ///
        // /// # Examples
        // ///
        // /// ```
        // #[doc = concat!("let bytes = ", $swap_op, stringify!($SelfT), ".to_le_bytes();")]
        // #[doc = concat!("assert_eq!(bytes, ", $le_bytes, ");")]
        // /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn to_le_bytes(self) -> [u8; ::core::mem::size_of::<Self>()] {
            self.to_le().to_ne_bytes()
        }

        /// Return the memory representation of this integer as a byte array in
        /// native byte order.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
        /// instead.
        ///
        // #[doc = $to_xe_bytes_doc]
        ///
        /// [`to_be_bytes`]: Self::to_be_bytes
        /// [`to_le_bytes`]: Self::to_le_bytes
        ///
        // /// # Examples
        // ///
        // /// ```
        // #[doc = concat!("let bytes = ", $swap_op, stringify!($SelfT), ".to_ne_bytes();")]
        // /// assert_eq!(
        // ///     bytes,
        // ///     if cfg!(target_endian = "big") {
        // #[doc = concat!("        ", $be_bytes)]
        // ///     } else {
        // #[doc = concat!("        ", $le_bytes)]
        // ///     }
        // /// );
        // /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        // SAFETY: const sound because integers are plain old datatypes so we can always
        // transmute them to arrays of bytes
        #[inline]
        pub const fn to_ne_bytes(self) -> [u8; ::core::mem::size_of::<Self>()] {
            // SAFETY: integers are plain old datatypes so we can always transmute them to
            // arrays of bytes
            unsafe { ::core::mem::transmute(self) }
        }

        /// Create a native endian integer value from its representation
        /// as a byte array in big endian.
        ///
        // #[doc = $from_xe_bytes_doc]
        ///
        /// # Examples
        ///
        // /// ```
        // #[doc = concat!("let value = ", stringify!($SelfT), "::from_be_bytes(", $be_bytes, ");")]
        // #[doc = concat!("assert_eq!(value, ", $swap_op, ");")]
        // /// ```
        ///
        /// When starting from a slice rather than an array, fallible conversion APIs can be used:
        ///
        /// ```
        #[doc = concat!("fn read_be_", stringify!($SelfT), "(input: &mut &[u8]) -> ", stringify!($SelfT), " {")]
        #[doc = concat!("    let (int_bytes, rest) = input.split_at(std::mem::size_of::<", stringify!($SelfT), ">());")]
        ///     *input = rest;
        #[doc = concat!("    ", stringify!($SelfT), "::from_be_bytes(int_bytes.try_into().unwrap())")]
        /// }
        /// ```
        #[must_use]
        #[inline]
        pub const fn from_be_bytes(bytes: [u8; ::core::mem::size_of::<Self>()]) -> Self {
            Self::from_be(Self::from_ne_bytes(bytes))
        }

        /// Create a native endian integer value from its representation
        /// as a byte array in little endian.
        ///
        // #[doc = $from_xe_bytes_doc]
        ///
        /// # Examples
        ///
        // /// ```
        // #[doc = concat!("let value = ", stringify!($SelfT), "::from_le_bytes(", $le_bytes, ");")]
        // #[doc = concat!("assert_eq!(value, ", $swap_op, ");")]
        // /// ```
        ///
        /// When starting from a slice rather than an array, fallible conversion APIs can be used:
        ///
        /// ```
        #[doc = concat!("fn read_le_", stringify!($SelfT), "(input: &mut &[u8]) -> ", stringify!($SelfT), " {")]
        #[doc = concat!("    let (int_bytes, rest) = input.split_at(std::mem::size_of::<", stringify!($SelfT), ">());")]
        ///     *input = rest;
        #[doc = concat!("    ", stringify!($SelfT), "::from_le_bytes(int_bytes.try_into().unwrap())")]
        /// }
        /// ```
        #[must_use]
        #[inline]
        pub const fn from_le_bytes(bytes: [u8; ::core::mem::size_of::<Self>()]) -> Self {
            Self::from_le(Self::from_ne_bytes(bytes))
        }

        /// Create a native endian integer value from its memory representation
        /// as a byte array in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
        /// appropriate instead.
        ///
        /// [`from_be_bytes`]: Self::from_be_bytes
        /// [`from_le_bytes`]: Self::from_le_bytes
        ///
        // #[doc = $from_xe_bytes_doc]
        ///
        /// # Examples
        ///
        // /// ```
        // #[doc = concat!("let value = ", stringify!($SelfT), "::from_ne_bytes(if cfg!(target_endian = \"big\") {")]
        // #[doc = concat!("    ", $be_bytes, "")]
        // /// } else {
        // #[doc = concat!("    ", $le_bytes, "")]
        // /// });
        // #[doc = concat!("assert_eq!(value, ", $swap_op, ");")]
        // /// ```
        ///
        /// When starting from a slice rather than an array, fallible conversion APIs can be used:
        ///
        /// ```
        #[doc = concat!("fn read_ne_", stringify!($SelfT), "(input: &mut &[u8]) -> ", stringify!($SelfT), " {")]
        #[doc = concat!("    let (int_bytes, rest) = input.split_at(std::mem::size_of::<", stringify!($SelfT), ">());")]
        ///     *input = rest;
        #[doc = concat!("    ", stringify!($SelfT), "::from_ne_bytes(int_bytes.try_into().unwrap())")]
        /// }
        /// ```
        #[must_use]
        // SAFETY: const sound because integers are plain old datatypes so we can always
        // transmute to them
        #[inline]
        pub const fn from_ne_bytes(bytes: [u8; ::core::mem::size_of::<Self>()]) -> Self {
            // SAFETY: integers are plain old datatypes so we can always transmute to them
            unsafe { ::core::mem::transmute(bytes) }
        }
    }
}

macro_rules! uimpl_add {
    ($self_type:ty, $bits:tt) => {
        // /// Wrapping (modular) addition with a signed integer. Computes
        // /// `self + rhs`, wrapping around at the boundary of the type.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// # #![feature(mixed_integer_ops)]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".wrapping_add_signed(2), 3);")]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".wrapping_add_signed(-2), ", stringify!($SelfT), "::MAX);")]
        // #[doc = concat!("assert_eq!((", stringify!($SelfT), "::MAX - 2).wrapping_add_signed(4), 1);")]
        // /// ```
        // // #[unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[rustc_const_unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn wrapping_add_signed(self, rhs: $SignedT) -> Self {
        //     self.wrapping_add(rhs as Self)
        // }

        // /// Calculates `self` + `rhs` with a signed `rhs`
        // ///
        // /// Returns a tuple of the addition along with a boolean indicating
        // /// whether an arithmetic overflow would occur. If an overflow would
        // /// have occurred then the wrapped value is returned.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// # #![feature(mixed_integer_ops)]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".overflowing_add_signed(2), (3, false));")]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".overflowing_add_signed(-2), (", stringify!($SelfT), "::MAX, true));")]
        // #[doc = concat!("assert_eq!((", stringify!($SelfT), "::MAX - 2).overflowing_add_signed(4), (1, true));")]
        // /// ```
        // // #[unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[rustc_const_unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn overflowing_add_signed(self, rhs: $SignedT) -> (Self, bool) {
        //     let (res, overflowed) = self.overflowing_add(rhs as Self);
        //     (res, overflowed ^ (rhs < 0))
        // }

        // /// Saturating addition with a signed integer. Computes `self + rhs`,
        // /// saturating at the numeric bounds instead of overflowing.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// # #![feature(mixed_integer_ops)]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".saturating_add_signed(2), 3);")]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".saturating_add_signed(-2), 0);")]
        // #[doc = concat!("assert_eq!((", stringify!($SelfT), "::MAX - 2).saturating_add_signed(4), ", stringify!($SelfT), "::MAX);")]
        // /// ```
        // // #[unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[rustc_const_unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn saturating_add_signed(self, rhs: $SignedT) -> Self {
        //     let (res, overflow) = self.overflowing_add(rhs as Self);
        //     if overflow == (rhs < 0) {
        //         res
        //     } else if overflow {
        //         Self::MAX
        //     } else {
        //         0
        //     }
        // }

        // /// Checked addition with a signed integer. Computes `self + rhs`,
        // /// returning `None` if overflow occurred.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// # #![feature(mixed_integer_ops)]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".checked_add_signed(2), Some(3));")]
        // #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".checked_add_signed(-2), None);")]
        // #[doc = concat!("assert_eq!((", stringify!($SelfT), "::MAX - 2).checked_add_signed(3), None);")]
        // /// ```
        // // #[unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[rustc_const_unstable(feature = "mixed_integer_ops", issue = "87840")]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn checked_add_signed(self, rhs: $SignedT) -> Option<Self> {
        //     let (a, b) = self.overflowing_add_signed(rhs);
        //     if unlikely!(b) {None} else {Some(a)}
        // }
        
        /// Checked integer addition. Computes `self + rhs`, returning `None`
        /// if overflow occurred.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!(
            "assert_eq!((", stringify!($self_type), "::MAX - 2).checked_add(1), ",
            "Some(", stringify!($self_type), "::MAX - 1));"
        )]
        #[doc = concat!("assert_eq!((", stringify!($self_type), "::MAX - 2).checked_add(3), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_add(self, rhs: Self) -> Option<Self> {
            // TODO: use the real one
            use std::convert::identity as unlikely;
            let (a, b) = self.overflowing_add(rhs);
            if unlikely(b) {None} else {Some(a)}
        }

        // /// Unchecked integer addition. Computes `self + rhs`, assuming overflow
        // /// cannot occur.
        // ///
        // /// # Safety
        // ///
        // /// This results in undefined behavior when
        // #[doc = concat!("`self + rhs > ", stringify!($self_type), "::MAX` or `self + rhs < ", stringify!($self_type), "::MIN`,")]
        // /// i.e. when [`checked_add`] would return `None`.
        // ///
        // #[doc = concat!("[`checked_add`]: ", stringify!($self_type), "::checked_add")]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const unsafe fn unchecked_add(self, rhs: Self) -> Self {
        //     // SAFETY: the caller must uphold the safety contract for
        //     // `unchecked_add`.
        //     Self(unsafe { self.0.unchecked_add(rhs.0) })
        // }

        /// Saturating integer addition. Computes `self + rhs`, saturating at
        /// the numeric bounds instead of overflowing.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(100", stringify!($self_type), ".saturating_add(1), 101);")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.saturating_add(127), ", stringify!($self_type), "::MAX);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn saturating_add(self, rhs: Self) -> Self {
            Self(match self.0.saturating_add(rhs.0) {
                n @ 0..=Self::BASE_MAX => n,
                _ => Self::BASE_MAX,
            })
        }

        /// Wrapping (modular) addition. Computes `self + rhs`,
        /// wrapping around at the boundary of the type.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(200", stringify!($self_type), ".wrapping_add(55), 255);")]
        #[doc = concat!("assert_eq!(200", stringify!($self_type), ".wrapping_add(", stringify!($self_type), "::MAX), 199);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_add(self, rhs: Self) -> Self {
            match rhs.0.checked_sub(Self::BASE_MAX - self.0) {
                Some(v) => Self(v),
                None => Self(self.0 + rhs.0),
            }
        }

        /// Calculates `self` + `rhs`
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        ///
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".overflowing_add(2), (7, false));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.overflowing_add(1), (0, true));")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
            match rhs.0.checked_sub(Self::BASE_MAX - self.0) {
                Some(v) => (Self(v), true),
                None => (Self(self.0 + rhs.0), false),
            }
        }

        /// Calculates `self + rhs + carry` without the ability to overflow.
        ///
        /// Performs "ternary addition" which takes in an extra bit to add, and may return an
        /// additional bit of overflow. This allows for chaining together multiple additions
        /// to create "big integers" which represent larger values.
        ///
        #[doc = concat!("This can be thought of as a ", stringify!($bits), "-bit \"full adder\", in the electronics sense.")]
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        /// #![feature(bigint_helper_methods)]
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".carrying_add(2, false), (7, false));")]
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".carrying_add(2, true), (8, false));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.carrying_add(1, false), (0, true));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.carrying_add(0, true), (0, true));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.carrying_add(1, true), (1, true));")]
        #[doc = concat!("assert_eq!(",
            stringify!($self_type), "::MAX.carrying_add(", stringify!($self_type), "::MAX, true), ",
            "(", stringify!($self_type), "::MAX, true));"
        )]
        /// ```
        ///
        /// If `carry` is false, this method is equivalent to [`overflowing_add`](Self::overflowing_add):
        ///
        /// ```
        /// #![feature(bigint_helper_methods)]
        #[doc = concat!("assert_eq!(5_", stringify!($self_type), ".carrying_add(2, false), 5_", stringify!($self_type), ".overflowing_add(2));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.carrying_add(1, false), ", stringify!($self_type), "::MAX.overflowing_add(1));")]
        /// ```
        // #[unstable(feature = "bigint_helper_methods", issue = "85532")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            // note: longer-term this should be done via an intrinsic, but this has been shown
            //   to generate optimal code for now, and LLVM doesn't have an equivalent intrinsic
            let (a, b) = self.overflowing_add(rhs);
            let (c, d) = a.overflowing_add(Self::cast_bits(carry as _));
            (c, b || d)
        }
    }
}

macro_rules! uimpl_sub {
    ($self_type:ty, $bits:tt) => {
        /// Checked integer subtraction. Computes `self - rhs`, returning
        /// `None` if overflow occurred.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(1", stringify!($self_type), ".checked_sub(1), Some(0));")]
        #[doc = concat!("assert_eq!(0", stringify!($self_type), ".checked_sub(1), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
            // TODO: use the real one
            use std::convert::identity as unlikely;
            let (a, b) = self.overflowing_sub(rhs);
            if unlikely(b) {None} else {Some(a)}
        }

        // /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow
        // /// cannot occur.
        // ///
        // /// # Safety
        // ///
        // /// This results in undefined behavior when
        // #[doc = concat!("`self - rhs > ", stringify!($self_type), "::MAX` or `self - rhs < ", stringify!($self_type), "::MIN`,")]
        // /// i.e. when [`checked_sub`] would return `None`.
        // ///
        // #[doc = concat!("[`checked_sub`]: ", stringify!($self_type), "::checked_sub")]
        // // #[unstable(
        // //     feature = "unchecked_math",
        // //     reason = "niche optimization path",
        // //     issue = "85122",
        // // )]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const unsafe fn unchecked_sub(self, rhs: Self) -> Self {
        //     // SAFETY: the caller must uphold the safety contract for
        //     // `unchecked_sub`.
        //     Self(unsafe { self.0.unchecked_sub(rhs.0) })
        // }

        /// Saturating integer subtraction. Computes `self - rhs`, saturating
        /// at the numeric bounds instead of overflowing.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(100", stringify!($self_type), ".saturating_sub(27), 73);")]
        #[doc = concat!("assert_eq!(13", stringify!($self_type), ".saturating_sub(127), 0);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn saturating_sub(self, rhs: Self) -> Self {
            Self(self.0.saturating_sub(rhs.0))
        }

        /// Wrapping (modular) subtraction. Computes `self - rhs`,
        /// wrapping around at the boundary of the type.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(100", stringify!($self_type), ".wrapping_sub(100), 0);")]
        #[doc = concat!("assert_eq!(100", stringify!($self_type), ".wrapping_sub(", stringify!($self_type), "::MAX), 101);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_sub(self, rhs: Self) -> Self {
            Self(self.0.wrapping_sub(rhs.0) & Self::BASE_MAX)
        }

        /// Calculates `self` - `rhs`
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        ///
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".overflowing_sub(2), (3, false));")]
        #[doc = concat!("assert_eq!(0", stringify!($self_type), ".overflowing_sub(1), (", stringify!($self_type), "::MAX, true));")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
            let (a, b) = self.0.overflowing_sub(rhs.0);
            (Self(a), b)
        }

        /// Calculates `self - rhs - borrow` without the ability to overflow.
        ///
        /// Performs "ternary subtraction" which takes in an extra bit to subtract, and may return
        /// an additional bit of overflow. This allows for chaining together multiple subtractions
        /// to create "big integers" which represent larger values.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        /// #![feature(bigint_helper_methods)]
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".borrowing_sub(2, false), (3, false));")]
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".borrowing_sub(2, true), (2, false));")]
        #[doc = concat!("assert_eq!(0", stringify!($self_type), ".borrowing_sub(1, false), (", stringify!($self_type), "::MAX, true));")]
        #[doc = concat!("assert_eq!(0", stringify!($self_type), ".borrowing_sub(1, true), (", stringify!($self_type), "::MAX - 1, true));")]
        /// ```
        // #[unstable(feature = "bigint_helper_methods", issue = "85532")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            // note: longer-term this should be done via an intrinsic, but this has been shown
            //   to generate optimal code for now, and LLVM doesn't have an equivalent intrinsic
            let (a, b) = self.overflowing_sub(rhs);
            let (c, d) = a.overflowing_sub(Self::cast_bits(borrow as _));
            (c, b || d)
        }

        /// Computes the absolute difference between `self` and `other`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).abs_diff(80), ", stringify!($self_type), "::cast_bits(20));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).abs_diff(110), ", stringify!($self_type), "::cast_bits(10));")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn abs_diff(self, other: Self) -> Self {
            Self(self.0.abs_diff(other.0))
        }
    }
}

macro_rules! uimpl_div {
    ($self_type:ty) => {
        /// Checked integer division. Computes `self / rhs`, returning `None`
        /// if `rhs == 0`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(128).checked_div(2), Some(64));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(1).checked_div(0), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_div(self, rhs: Self) -> Option<Self> {
            match self.0.checked_div(rhs.0) {
                Some(v) => Some(Self(v)),
                None => None,
            }
        }

        /// Checked Euclidean division. Computes `self.div_euclid(rhs)`, returning `None`
        /// if `rhs == 0`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(128).checked_div_euclid(2), Some(64));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(1).checked_div_euclid(0), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
            match self.0.checked_div_euclid(rhs.0) {
                Some(v) => Some(Self(v)),
                None => None,
            }
        }

        /// Saturating integer division. Computes `self / rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).saturating_div(2), 2);")]
        ///
        /// ```
        ///
        /// ```should_panic
        #[doc = concat!("let _ = ", stringify!($self_type), "::cast_bits(1).saturating_div(0);")]
        ///
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_div(self, rhs: Self) -> Self {
            // on unsigned types, there is no overflow in integer division
            self.wrapping_div(rhs)
        }

        /// Wrapping (modular) division. Computes `self / rhs`.
        /// Wrapped division on unsigned types is just normal division.
        /// There's no way wrapping could ever happen.
        /// This function exists, so that all operations
        /// are accounted for in the wrapping operations.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).wrapping_div(10), 10);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_div(self, rhs: Self) -> Self {
            Self(self.0.wrapping_div(rhs.0))
        }

        /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`.
        /// Wrapped division on unsigned types is just normal division.
        /// There's no way wrapping could ever happen.
        /// This function exists, so that all operations
        /// are accounted for in the wrapping operations.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self.wrapping_div(rhs)`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).wrapping_div_euclid(10), 10);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_div_euclid(self, rhs: Self) -> Self {
            Self(self.0.wrapping_div_euclid(rhs.0))
        }

        /// Checked integer remainder. Computes `self % rhs`, returning `None`
        /// if `rhs == 0`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).checked_rem(2), Some(1));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).checked_rem(0), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
            match self.0.checked_rem(rhs.0) {
                Some(v) => Some(Self(v)),
                None => None,
            }
        }

        /// Checked Euclidean modulo. Computes `self.rem_euclid(rhs)`, returning `None`
        /// if `rhs == 0`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).checked_rem_euclid(2), Some(1));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).checked_rem_euclid(0), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
            match self.0.checked_rem_euclid(rhs.0) {
                Some(v) => Some(Self(v)),
                None => None,
            }
        }

        /// Wrapping (modular) remainder. Computes `self % rhs`.
        /// Wrapped remainder calculation on unsigned types is
        /// just the regular remainder calculation.
        /// There's no way wrapping could ever happen.
        /// This function exists, so that all operations
        /// are accounted for in the wrapping operations.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).wrapping_rem(10), 0);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_rem(self, rhs: Self) -> Self {
            Self(self.0.wrapping_rem(rhs.0))
        }

        /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`.
        /// Wrapped modulo calculation on unsigned types is
        /// just the regular remainder calculation.
        /// There's no way wrapping could ever happen.
        /// This function exists, so that all operations
        /// are accounted for in the wrapping operations.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self.wrapping_rem(rhs)`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(100).wrapping_rem_euclid(10), 0);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_rem_euclid(self, rhs: Self) -> Self {
            Self(self.0.wrapping_rem_euclid(rhs.0))
        }

        /// Calculates the divisor when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating
        /// whether an arithmetic overflow would occur. Note that for unsigned
        /// integers overflow never occurs, so the second value is always
        /// `false`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).overflowing_div(2), (2, false));")]
        /// ```
        #[inline(always)]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
            let (a, b) = self.0.overflowing_div(rhs.0);
            (Self(a), b)
        }

        /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating
        /// whether an arithmetic overflow would occur. Note that for unsigned
        /// integers overflow never occurs, so the second value is always
        /// `false`.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self.overflowing_div(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).overflowing_div_euclid(2), (2, false));")]
        /// ```
        #[inline(always)]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
            let (a, b) = self.0.overflowing_div_euclid(rhs.0);
            (Self(a), b)
        }

        /// Calculates the remainder when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the remainder after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. Note that for
        /// unsigned integers overflow never occurs, so the second value is
        /// always `false`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).overflowing_rem(2), (1, false));")]
        /// ```
        #[inline(always)]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
            let (a, b) = self.0.overflowing_rem(rhs.0);
            (Self(a), b)
        }

        /// Calculates the remainder `self.rem_euclid(rhs)` as if by Euclidean division.
        ///
        /// Returns a tuple of the modulo after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. Note that for
        /// unsigned integers overflow never occurs, so the second value is
        /// always `false`.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this operation
        /// is exactly equal to `self.overflowing_rem(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).overflowing_rem_euclid(2), (1, false));")]
        /// ```
        #[inline(always)]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
            let (a, b) = self.0.overflowing_rem_euclid(rhs.0);
            (Self(a), b)
        }

        /// Performs Euclidean division.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self / rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(7).div_euclid(4), 1); // or any other integer type")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn div_euclid(self, rhs: Self) -> Self {
            Self(self.0.div_euclid(rhs.0))
        }

        /// Calculates the least remainder of `self (mod rhs)`.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self % rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is 0.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(7).rem_euclid(4), 3); // or any other integer type")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn rem_euclid(self, rhs: Self) -> Self {
            Self(self.0.rem_euclid(rhs.0))
        }

        // /// Calculates the quotient of `self` and `rhs`, rounding the result towards negative infinity.
        // ///
        // /// This is the same as performing `self / rhs` for all unsigned integers.
        // ///
        // /// # Panics
        // ///
        // /// This function will panic if `rhs` is zero.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// #![feature(int_roundings)]
        // #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(7).div_floor(4), 1);")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const fn div_floor(self, rhs: Self) -> Self {
        //     Self(self.0.div_floor(rhs.0))
        // }

        // /// Calculates the quotient of `self` and `rhs`, rounding the result towards positive infinity.
        // ///
        // /// # Panics
        // ///
        // /// This function will panic if `rhs` is zero.
        // ///
        // /// ## Overflow behavior
        // ///
        // /// On overflow, this function will panic if overflow checks are enabled (default in debug
        // /// mode) and wrap if overflow checks are disabled (default in release mode).
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// ```
        // /// #![feature(int_roundings)]
        // #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(7).div_ceil(4), 2);")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn div_ceil(self, rhs: Self) -> Self {
        //     Self(self.0.div_ceil(rhs.0))
        // }
    }
}

macro_rules! uimpl_mul {
    ($self_type:ty) => {
        /// Checked integer multiplication. Computes `self * rhs`, returning
        /// `None` if overflow occurred.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(5", stringify!($self_type), ".checked_mul(1), Some(5));")]
        #[doc = concat!("assert_eq!(", stringify!($self_type), "::MAX.checked_mul(2), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
            match self.0.checked_mul(rhs.0) {
                None => None,
                Some(v) if v > Self::BASE_MAX => None,
                Some(v) => Some(Self(v))
            }
        }

        // /// Unchecked integer multiplication. Computes `self * rhs`, assuming overflow
        // /// cannot occur.
        // ///
        // /// # Safety
        // ///
        // /// This results in undefined behavior when
        // #[doc = concat!("`self * rhs > ", stringify!($self_type), "::MAX` or `self * rhs < ", stringify!($self_type), "::MIN`,")]
        // /// i.e. when [`checked_mul`] would return `None`.
        // ///
        // #[doc = concat!("[`checked_mul`]: ", stringify!($self_type), "::checked_mul")]
        // // #[unstable(
        // //     feature = "unchecked_math",
        // //     reason = "niche optimization path",
        // //     issue = "85122",
        // // )]
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const unsafe fn unchecked_mul(self, rhs: Self) -> Self {
        //     // SAFETY: the caller must uphold the safety contract for
        //     // `unchecked_mul`.
        //     Self(unsafe { self.0.unchecked_mul(rhs.0) })
        // }

        /// Saturating integer multiplication. Computes `self * rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(2", stringify!($self_type), ".saturating_mul(10), 20);")]
        #[doc = concat!("assert_eq!((", stringify!($self_type), "::MAX).saturating_mul(10), ", stringify!($self_type),"::MAX);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(x) => x,
                None => Self::MAX,
            }
        }

        // TODO: how?
        // /// Wrapping (modular) multiplication. Computes `self *
        // /// rhs`, wrapping around at the boundary of the type.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// Please note that this example is shared between integer types.
        // /// Which explains why `u8` is used here.
        // ///
        // /// ```
        // /// assert_eq!(10u8.wrapping_mul(12), 120);
        // /// assert_eq!(25u8.wrapping_mul(12), 44);
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline(always)]
        // pub const fn wrapping_mul(self, rhs: Self) -> Self {
        //     ::core::intrinsics::wrapping_mul(self, rhs)
        // }

        // TODO: how?
        // /// Calculates the multiplication of `self` and `rhs`.
        // ///
        // /// Returns a tuple of the multiplication along with a boolean
        // /// indicating whether an arithmetic overflow would occur. If an
        // /// overflow would have occurred then the wrapped value is returned.
        // ///
        // /// # Examples
        // ///
        // /// Basic usage:
        // ///
        // /// Please note that this example is shared between integer types.
        // /// Which explains why `u32` is used here.
        // ///
        // /// ```
        // /// assert_eq!(5u32.overflowing_mul(2), (10, false));
        // /// assert_eq!(1_000_000_000u32.overflowing_mul(10), (1410065408, true));
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //                   without modifying the original"]
        // #[inline(always)]
        // pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        //     let (a, b) = ::core::intrinsics::mul_with_overflow(self as $ActualT, rhs as $ActualT);
        //     (a as Self, b)
        // }
    }
}

macro_rules! uimpl_log {
    ($self_type:ty, $bits:tt) => {
        // /// Returns the logarithm of the number with respect to an arbitrary base,
        // /// rounded down.
        // ///
        // /// This method might not be optimized owing to implementation details;
        // /// `log2` can produce results more efficiently for base 2, and `log10`
        // /// can produce results more efficiently for base 10.
        // ///
        // /// # Panics
        // ///
        // /// When the number is zero, or if the base is not at least 2;
        // /// it panics in debug mode and the return value is 0 in release mode.
        // ///
        // /// # Examples
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(", stringify!($self_type), "::cast_bits(5).log(5), 1);")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // #[track_caller]
        // #[allow(arithmetic_overflow)]
        // pub const fn log(self, base: Self) -> u32 {
        //     self.0.log(self.0)
        // }

        // /// Returns the base 2 logarithm of the number, rounded down.
        // ///
        // /// # Panics
        // ///
        // /// When the number is zero it panics in debug mode and
        // /// the return value is 0 in release mode.
        // ///
        // /// # Examples
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(2", stringify!($self_type), ".log2(), 1);")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // #[track_caller]
        // #[allow(arithmetic_overflow)]
        // pub const fn log2(self) -> u32 {
        //     self.0.log2()
        // }

        // /// Returns the base 10 logarithm of the number, rounded down.
        // ///
        // /// # Panics
        // ///
        // /// When the number is zero it panics in debug mode and the
        // /// return value is 0 in release mode.
        // ///
        // /// # Example
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(10", stringify!($self_type), ".log10(), 1);")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // #[track_caller]
        // #[allow(arithmetic_overflow)]
        // pub const fn log10(self) -> u32 {
        //     self.0.log10()
        // }

        // /// Returns the logarithm of the number with respect to an arbitrary base,
        // /// rounded down.
        // ///
        // /// Returns `None` if the number is zero, or if the base is not at least 2.
        // ///
        // /// This method might not be optimized owing to implementation details;
        // /// `checked_log2` can produce results more efficiently for base 2, and
        // /// `checked_log10` can produce results more efficiently for base 10.
        // ///
        // /// # Examples
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(5", stringify!($self_type), ".checked_log(5), Some(1));")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn checked_log(self, base: Self) -> Option<u32> {
        //     self.0.checked_log(base)
        // }

        // /// Returns the base 2 logarithm of the number, rounded down.
        // ///
        // /// Returns `None` if the number is zero.
        // ///
        // /// # Examples
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(2", stringify!($self_type), ".checked_log2(), Some(1));")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn checked_log2(self) -> Option<u32> {
        //     self.0.checked_log2()
        // }

        // /// Returns the base 10 logarithm of the number, rounded down.
        // ///
        // /// Returns `None` if the number is zero.
        // ///
        // /// # Examples
        // ///
        // /// ```
        // /// #![feature(int_log)]
        // #[doc = concat!("assert_eq!(10", stringify!($self_type), ".checked_log10(), Some(1));")]
        // /// ```
        // #[must_use = "this returns the result of the operation, \
        //               without modifying the original"]
        // #[inline]
        // pub const fn checked_log10(self) -> Option<u32> {
        //     self.0.checked_log10()
        // }
    }
}

macro_rules! uimpl_shift {
    ($self_type:ty, $bits:tt) => {

    }
}

macro_rules! uimpl {
    ($self_type:ident<[$($bits:tt),* $(,)?]>) => {
        $(uimpl!{@impl $self_type<[$bits]>})*
    };

    (@impl $self_type:ident<[$bits:tt]>) => {
        impl $self_type<$bits> {
            uimpl_bitty!{$self_type<$bits>, $bits}
            uimpl_consts!{$self_type<$bits>, $bits}
            uimpl_bits!{$self_type<$bits>, $bits}
            uimpl_add!{$self_type<$bits>, $bits}
            uimpl_sub!{$self_type<$bits>, $bits}
            uimpl_div!{$self_type<$bits>}
            uimpl_mul!{$self_type<$bits>}
            uimpl_log!{$self_type<$bits>, $bits}
            uimpl_shift!{$self_type<$bits>, $bits}

            // uimpl!{@impl-body
            //     $self_type<$bits>,
            //     $bits,
            // }
        }
    };

    (@impl-body
        $SelfT:ty,

        // TODO: signed type
        // $SignedT:ident,

        // TODO: non zero type
        // $NonZeroT:ident,

        $BITS:expr,

        // TODO: max value
        // $max_value:expr,

        // TODO: rotation examples
        // $rot:expr,
        // $rot_op:expr,
        // $rot_result:expr,

        // TODO: swap examples
        // $swap_op:expr,
        // $swapped:expr,
        // $reversed:expr,
        // $le_bytes:expr,
        // $be_bytes:expr,

        // TODO: extra docs
        // $to_xe_bytes_doc:expr,
        // $from_xe_bytes_doc:expr
    ) => {

        /// Converts a string slice in a given base to an integer.
        ///
        /// The string is expected to be an optional `+` sign
        /// followed by digits.
        /// Leading and trailing whitespace represent an error.
        /// Digits are a subset of these characters, depending on `radix`:
        ///
        /// * `0-9`
        /// * `a-z`
        /// * `A-Z`
        ///
        /// # Panics
        ///
        /// This function panics if `radix` is not in the range from 2 to 36.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::from_str_radix(\"A\", 16), Ok(10));")]
        /// ```
        pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
            from_str_radix(src, radix)
        }

        
        /// Checked negation. Computes `-self`, returning `None` unless `self ==
        /// 0`.
        ///
        /// Note that negating any positive integer will overflow.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".checked_neg(), Some(0));")]
        #[doc = concat!("assert_eq!(1", stringify!($SelfT), ".checked_neg(), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_neg(self) -> Option<Self> {
            let (a, b) = self.overflowing_neg();
            if unlikely!(b) {None} else {Some(a)}
        }

        /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if
        /// overflow occurred.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".checked_pow(5), Some(32));")]
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX.checked_pow(2), None);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_pow(self, mut exp: u32) -> Option<Self> {
            if exp == 0 {
                return Some(1);
            }
            let mut base = self;
            let mut acc: Self = 1;

            while exp > 1 {
                if (exp & 1) == 1 {
                    acc = try_opt!(acc.checked_mul(base));
                }
                exp /= 2;
                base = try_opt!(base.checked_mul(base));
            }

            // since exp!=0, finally the exp must be 1.
            // Deal with the final bit of the exponent separately, since
            // squaring the base afterwards is not necessary and may cause a
            // needless overflow.

            Some(try_opt!(acc.checked_mul(base)))
        }

        /// Saturating integer exponentiation. Computes `self.pow(exp)`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(4", stringify!($SelfT), ".saturating_pow(3), 64);")]
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX.saturating_pow(2), ", stringify!($SelfT), "::MAX);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_pow(self, exp: u32) -> Self {
            match self.checked_pow(exp) {
                Some(x) => x,
                None => Self::MAX,
            }
        }

        /// Wrapping (modular) negation. Computes `-self`,
        /// wrapping around at the boundary of the type.
        ///
        /// Since unsigned types do not have negative equivalents
        /// all applications of this function will wrap (except for `-0`).
        /// For values smaller than the corresponding signed type's maximum
        /// the result is the same as casting the corresponding signed value.
        /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
        /// `MAX` is the corresponding signed type's maximum.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// Please note that this example is shared between integer types.
        /// Which explains why `i8` is used here.
        ///
        /// ```
        /// assert_eq!(100i8.wrapping_neg(), -100);
        /// assert_eq!((-128i8).wrapping_neg(), -128);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline(always)]
        pub const fn wrapping_neg(self) -> Self {
            (0 as $SelfT).wrapping_sub(self)
        }

        /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
        /// wrapping around at the boundary of the type.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(3", stringify!($SelfT), ".wrapping_pow(5), 243);")]
        /// assert_eq!(3u8.wrapping_pow(6), 217);
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn wrapping_pow(self, mut exp: u32) -> Self {
            if exp == 0 {
                return 1;
            }
            let mut base = self;
            let mut acc: Self = 1;

            while exp > 1 {
                if (exp & 1) == 1 {
                    acc = acc.wrapping_mul(base);
                }
                exp /= 2;
                base = base.wrapping_mul(base);
            }

            // since exp!=0, finally the exp must be 1.
            // Deal with the final bit of the exponent separately, since
            // squaring the base afterwards is not necessary and may cause a
            // needless overflow.
            acc.wrapping_mul(base)
        }

        /// Negates self in an overflowing fashion.
        ///
        /// Returns `!self + 1` using wrapping operations to return the value
        /// that represents the negation of this unsigned value. Note that for
        /// positive unsigned values overflow always occurs, but negating 0 does
        /// not overflow.
        ///
        /// # Examples
        ///
        /// Basic usage
        ///
        /// ```
        #[doc = concat!("assert_eq!(0", stringify!($SelfT), ".overflowing_neg(), (0, false));")]
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".overflowing_neg(), (-2i32 as ", stringify!($SelfT), ", true));")]
        /// ```
        #[inline(always)]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn overflowing_neg(self) -> (Self, bool) {
            ((!self).wrapping_add(1), self != 0)
        }

        /// Raises self to the power of `exp`, using exponentiation by squaring.
        ///
        /// Returns a tuple of the exponentiation along with a bool indicating
        /// whether an overflow happened.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(3", stringify!($SelfT), ".overflowing_pow(5), (243, false));")]
        /// assert_eq!(3u8.overflowing_pow(6), (217, true));
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
            if exp == 0{
                return (1,false);
            }
            let mut base = self;
            let mut acc: Self = 1;
            let mut overflown = false;
            // Scratch space for storing results of overflowing_mul.
            let mut r;

            while exp > 1 {
                if (exp & 1) == 1 {
                    r = acc.overflowing_mul(base);
                    acc = r.0;
                    overflown |= r.1;
                }
                exp /= 2;
                r = base.overflowing_mul(base);
                base = r.0;
                overflown |= r.1;
            }

            // since exp!=0, finally the exp must be 1.
            // Deal with the final bit of the exponent separately, since
            // squaring the base afterwards is not necessary and may cause a
            // needless overflow.
            r = acc.overflowing_mul(base);
            r.1 |= overflown;

            r
        }

        /// Raises self to the power of `exp`, using exponentiation by squaring.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".pow(5), 32);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn pow(self, mut exp: u32) -> Self {
            if exp == 0 {
                return 1;
            }
            let mut base = self;
            let mut acc = 1;

            while exp > 1 {
                if (exp & 1) == 1 {
                    acc = acc * base;
                }
                exp /= 2;
                base = base * base;
            }

            // since exp!=0, finally the exp must be 1.
            // Deal with the final bit of the exponent separately, since
            // squaring the base afterwards is not necessary and may cause a
            // needless overflow.
            acc * base
        }

        /// Calculates the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// On overflow, this function will panic if overflow checks are enabled (default in debug
        /// mode) and wrap if overflow checks are disabled (default in release mode).
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// #![feature(int_roundings)]
        #[doc = concat!("assert_eq!(16_", stringify!($SelfT), ".next_multiple_of(8), 16);")]
        #[doc = concat!("assert_eq!(23_", stringify!($SelfT), ".next_multiple_of(8), 24);")]
        /// ```
        // #[unstable(feature = "int_roundings", issue = "88581")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn next_multiple_of(self, rhs: Self) -> Self {
            match self % rhs {
                0 => self,
                r => self + (rhs - r)
            }
        }

        /// Calculates the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`. Returns `None` if `rhs` is zero or the
        /// operation would result in overflow.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// #![feature(int_roundings)]
        #[doc = concat!("assert_eq!(16_", stringify!($SelfT), ".checked_next_multiple_of(8), Some(16));")]
        #[doc = concat!("assert_eq!(23_", stringify!($SelfT), ".checked_next_multiple_of(8), Some(24));")]
        #[doc = concat!("assert_eq!(1_", stringify!($SelfT), ".checked_next_multiple_of(0), None);")]
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX.checked_next_multiple_of(2), None);")]
        /// ```
        // #[unstable(feature = "int_roundings", issue = "88581")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
            match try_opt!(self.checked_rem(rhs)) {
                0 => Some(self),
                // rhs - r cannot overflow because r is smaller than rhs
                r => self.checked_add(rhs - r)
            }
        }

        // Returns one less than next power of two.
        // (For 8u8 next power of two is 8u8 and for 6u8 it is 8u8)
        //
        // 8u8.one_less_than_next_power_of_two() == 7
        // 6u8.one_less_than_next_power_of_two() == 7
        //
        // This method cannot overflow, as in the `next_power_of_two`
        // overflow cases it instead ends up returning the maximum value
        // of the type, and can return 0 for 0.
        #[inline]
        const fn one_less_than_next_power_of_two(self) -> Self {
            if self <= 1 { return 0; }

            let p = self - 1;
            // SAFETY: Because `p > 0`, it cannot consist entirely of leading zeros.
            // That means the shift is always in-bounds, and some processors
            // (such as intel pre-haswell) have more efficient ctlz
            // ::core::intrinsics when the argument is non-zero.
            let z = unsafe { ::core::intrinsics::ctlz_nonzero(p) };
            <$SelfT>::MAX >> z
        }

        /// Returns the smallest power of two greater than or equal to `self`.
        ///
        /// When return value overflows (i.e., `self > (1 << (N-1))` for type
        /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
        /// release mode (the only situation in which method can return 0).
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".next_power_of_two(), 2);")]
        #[doc = concat!("assert_eq!(3", stringify!($SelfT), ".next_power_of_two(), 4);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn next_power_of_two(self) -> Self {
            self.one_less_than_next_power_of_two() + 1
        }

        /// Returns the smallest power of two greater than or equal to `n`. If
        /// the next power of two is greater than the type's maximum value,
        /// `None` is returned, otherwise the power of two is wrapped in `Some`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".checked_next_power_of_two(), Some(2));")]
        #[doc = concat!("assert_eq!(3", stringify!($SelfT), ".checked_next_power_of_two(), Some(4));")]
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX.checked_next_power_of_two(), None);")]
        /// ```
        #[inline]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn checked_next_power_of_two(self) -> Option<Self> {
            self.one_less_than_next_power_of_two().checked_add(1)
        }

        /// Returns the smallest power of two greater than or equal to `n`. If
        /// the next power of two is greater than the type's maximum value,
        /// the return value is wrapped to `0`.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// #![feature(wrapping_next_power_of_two)]
        ///
        #[doc = concat!("assert_eq!(2", stringify!($SelfT), ".wrapping_next_power_of_two(), 2);")]
        #[doc = concat!("assert_eq!(3", stringify!($SelfT), ".wrapping_next_power_of_two(), 4);")]
        #[doc = concat!("assert_eq!(", stringify!($SelfT), "::MAX.wrapping_next_power_of_two(), 0);")]
        /// ```
        #[inline]
        // #[unstable(feature = "wrapping_next_power_of_two", issue = "32463",
        //           reason = "needs decision on wrapping behaviour")]
        #[rustc_const_unstable(feature = "wrapping_next_power_of_two", issue = "32463")]
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        pub const fn wrapping_next_power_of_two(self) -> Self {
            self.one_less_than_next_power_of_two().wrapping_add(1)
        }
    }
}
