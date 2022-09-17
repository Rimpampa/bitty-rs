macro_rules! bits_alias_generator {
    ($($bits:tt = u @ $u:tt, i @ $i:tt;)*) => {
        macro_rules! bits_alias {$(
            (@u $bits) => { $u };
            (@i $bits) => { $i };
            (@u-macro $bits) => { macro_rules! $u { ($v:literal) => { $crate::UBits::<$bits>::cast_bits($v) } } };
            (@i-macro $bits) => { macro_rules! $i { ($v:literal) => { $crate::IBits::<$bits>::cast_bits($v) } } };
        )*}
    }
}

bits_alias_generator! {
    1 = u @ u1, i @ i1;
    2 = u @ u2, i @ i2;
    3 = u @ u3, i @ i3;
    4 = u @ u4, i @ i4;
    5 = u @ u5, i @ i5;
    6 = u @ u6, i @ i6;
    7 = u @ u7, i @ i7;
    8 = u @ u8, i @ i8;
    9 = u @ u9, i @ i9;
   10 = u @ u10, i @ i10;
   11 = u @ u11, i @ i11;
   12 = u @ u12, i @ i12;
   13 = u @ u13, i @ i13;
   14 = u @ u14, i @ i14;
   15 = u @ u15, i @ i15;
   16 = u @ u16, i @ i16;
   17 = u @ u17, i @ i17;
   18 = u @ u18, i @ i18;
   19 = u @ u19, i @ i19;
   20 = u @ u20, i @ i20;
   21 = u @ u21, i @ i21;
   22 = u @ u22, i @ i22;
   23 = u @ u23, i @ i23;
   24 = u @ u24, i @ i24;
   25 = u @ u25, i @ i25;
   26 = u @ u26, i @ i26;
   27 = u @ u27, i @ i27;
   28 = u @ u28, i @ i28;
   29 = u @ u29, i @ i29;
   30 = u @ u30, i @ i30;
   31 = u @ u31, i @ i31;
   32 = u @ u32, i @ i32;
   33 = u @ u33, i @ i33;
   34 = u @ u34, i @ i34;
   35 = u @ u35, i @ i35;
   36 = u @ u36, i @ i36;
   37 = u @ u37, i @ i37;
   38 = u @ u38, i @ i38;
   39 = u @ u39, i @ i39;
   40 = u @ u40, i @ i40;
   41 = u @ u41, i @ i41;
   42 = u @ u42, i @ i42;
   43 = u @ u43, i @ i43;
   44 = u @ u44, i @ i44;
   45 = u @ u45, i @ i45;
   46 = u @ u46, i @ i46;
   47 = u @ u47, i @ i47;
   48 = u @ u48, i @ i48;
   49 = u @ u49, i @ i49;
   50 = u @ u50, i @ i50;
   51 = u @ u51, i @ i51;
   52 = u @ u52, i @ i52;
   53 = u @ u53, i @ i53;
   54 = u @ u54, i @ i54;
   55 = u @ u55, i @ i55;
   56 = u @ u56, i @ i56;
   57 = u @ u57, i @ i57;
   58 = u @ u58, i @ i58;
   59 = u @ u59, i @ i59;
   60 = u @ u60, i @ i60;
   61 = u @ u61, i @ i61;
   62 = u @ u62, i @ i62;
   63 = u @ u63, i @ i63;
   64 = u @ u64, i @ i64;
}
