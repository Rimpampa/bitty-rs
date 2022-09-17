/// Generates the `bits_max!` macro
/// 
/// Note that this is used to avoid repeating the maximum number more than once,
/// because only by making a macro generator you can convert the token using
/// [`stringify!`], this doesn't work: `stringify!(bits_max!(N))`
macro_rules! bits_max_generator {
    ($($bits:tt = $max:tt;)*) => {
        /// Converts the given number of bits in the maximum number
        /// that can fit in that number of bits
        macro_rules! bits_max {$(
            // Note: the const is used to make the type system happy
            // about a possible integer literal being ≥ than u32::MAX
            ($bits) => {{ ::core::convert::identity::<u128>($max) }};
            (@str $bits) => { stringify!($max); };
        )*}
    }
}

bits_max_generator!{
     1 = 1;
     2 = 3;
     3 = 7;
     4 = 15;
     5 = 31;
     6 = 63;
     7 = 127;
     8 = 255;
     9 = 511;
    10 = 1023;
    11 = 2047;
    12 = 4095;
    13 = 8191;
    14 = 16383;
    15 = 32767;
    16 = 65535;
    17 = 131071;
    18 = 262143;
    19 = 524287;
    20 = 1048575;
    21 = 2097151;
    22 = 4194303;
    23 = 8388607;
    24 = 16777215;
    25 = 33554431;
    26 = 67108863;
    27 = 134217727;
    28 = 268435455;
    29 = 536870911;
    30 = 1073741823;
    31 = 2147483647;
    32 = 4294967295;
    33 = 8589934591;
    34 = 17179869183;
    35 = 34359738367;
    36 = 68719476735;
    37 = 137438953471;
    38 = 274877906943;
    39 = 549755813887;
    40 = 1099511627775;
    41 = 2199023255551;
    42 = 4398046511103;
    43 = 8796093022207;
    44 = 17592186044415;
    45 = 35184372088831;
    46 = 70368744177663;
    47 = 140737488355327;
    48 = 281474976710655;
    49 = 562949953421311;
    50 = 1125899906842623;
    51 = 2251799813685247;
    52 = 4503599627370495;
    53 = 9007199254740991;
    54 = 18014398509481983;
    55 = 36028797018963967;
    56 = 72057594037927935;
    57 = 144115188075855871;
    58 = 288230376151711743;
    59 = 576460752303423487;
    60 = 1152921504606846975;
    61 = 2305843009213693951;
    62 = 4611686018427387903;
    63 = 9223372036854775807;
    64 = 18446744073709551615;
}

/// Generates a compile time check for the "implementation"
/// of the [`bits_max!`] macro for the given amount of bits
macro_rules! check_bits_max {
    ([$($bits:tt),* $(,)?]) => {{
        $(let _ = check_bits_max!($bits);)*
    }};

    ($bits:tt) => {{
        // Both checks are important, see the following examples using $bits = 3
        // to understand why
        // - 0b1110 succeeds the first but not the seconds
        // - 0b10111 succeeds the second but not the first 
        if bits_max!($bits).count_ones() != $bits
            || bits_max!($bits).trailing_ones() != $bits
            || bits_max!($bits) != (1u128 << $bits) - 1 {
            panic!(concat!("Wrong bits_max! for ", stringify!($bits), " bits"));
        }
    }}
}

// Compile time checks for the bits_max! macro
const _: () = check_bits_max!{[
    1,  2,  3,  4,  5,  6,  7,  8,
    9, 10, 11, 12, 13, 14, 15, 16,
   17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 29, 30, 31, 32,
   33, 34, 35, 36, 37, 38, 39, 40,
   41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55, 56,
   57, 58, 59, 60, 61, 62, 63, 64,
]};
