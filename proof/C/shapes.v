From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.16".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "../src/shapes.c".
  Definition normalized := true.
End Info.

Definition _N : ident := $"N".
Definition _Nx : ident := $"Nx".
Definition _Ny : ident := $"Ny".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _dN : ident := $"dN".
Definition _dNx : ident := $"dNx".
Definition _dNy : ident := $"dNy".
Definition _densematn_get : ident := $"densematn_get".
Definition _densematn_set : ident := $"densematn_set".
Definition _main : ident := $"main".
Definition _shapes1dP1 : ident := $"shapes1dP1".
Definition _shapes1dP2 : ident := $"shapes1dP2".
Definition _shapes1dP3 : ident := $"shapes1dP3".
Definition _shapes2dP1 : ident := $"shapes2dP1".
Definition _shapes2dP2 : ident := $"shapes2dP2".
Definition _shapes2dS2 : ident := $"shapes2dS2".
Definition _shapes2dT1 : ident := $"shapes2dT1".
Definition _x : ident := $"x".
Definition _xx : ident := $"xx".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_shapes1dP1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_xx, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _densematn_get (Tfunction
                             ((tptr tdouble) :: tint :: tint :: tint :: nil)
                             tdouble cc_default))
      ((Etempvar _xx (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0) tint) ::
       nil))
    (Sset _x (Etempvar _t'1 tdouble)))
  (Ssequence
    (Sifthenelse (Etempvar _N (tptr tdouble))
      (Ssequence
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _N (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Ebinop Omul
             (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
             (Ebinop Osub (Econst_int (Int.repr 1) tint)
               (Etempvar _x tdouble) tdouble) tdouble) :: nil))
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _N (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 1) tint) ::
           (Ebinop Omul
             (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
             (Ebinop Oadd (Econst_int (Int.repr 1) tint)
               (Etempvar _x tdouble) tdouble) tdouble) :: nil)))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _dN (tptr tdouble))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _dN (tptr tdouble)) ::
             (Econst_int (Int.repr 2) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Eunop Oneg
               (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
               tdouble) :: nil))
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _dN (tptr tdouble)) ::
             (Econst_int (Int.repr 2) tint) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble) ::
             nil)))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 2) tint))))))
|}.

Definition f_shapes1dP2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_xx, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _densematn_get (Tfunction
                             ((tptr tdouble) :: tint :: tint :: tint :: nil)
                             tdouble cc_default))
      ((Etempvar _xx (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0) tint) ::
       nil))
    (Sset _x (Etempvar _t'1 tdouble)))
  (Ssequence
    (Sifthenelse (Etempvar _N (tptr tdouble))
      (Ssequence
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _N (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Ebinop Omul
             (Ebinop Omul
               (Eunop Oneg
                 (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                 tdouble)
               (Ebinop Osub (Econst_int (Int.repr 1) tint)
                 (Etempvar _x tdouble) tdouble) tdouble)
             (Etempvar _x tdouble) tdouble) :: nil))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _N (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) ::
             (Ebinop Omul
               (Ebinop Osub (Econst_int (Int.repr 1) tint)
                 (Etempvar _x tdouble) tdouble)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Etempvar _x tdouble) tdouble) tdouble) :: nil))
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _N (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 2) tint) ::
             (Ebinop Omul
               (Ebinop Omul
                 (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                 (Etempvar _x tdouble) tdouble)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Etempvar _x tdouble) tdouble) tdouble) :: nil))))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _dN (tptr tdouble))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _dN (tptr tdouble)) ::
             (Econst_int (Int.repr 3) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Ebinop Omul
               (Eunop Oneg
                 (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                 tdouble)
               (Ebinop Osub (Econst_int (Int.repr 1) tint)
                 (Ebinop Omul (Econst_int (Int.repr 2) tint)
                   (Etempvar _x tdouble) tdouble) tdouble) tdouble) :: nil))
          (Ssequence
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _dN (tptr tdouble)) ::
               (Econst_int (Int.repr 3) tint) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)
                 (Etempvar _x tdouble) tdouble) :: nil))
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _dN (tptr tdouble)) ::
               (Econst_int (Int.repr 3) tint) ::
               (Econst_int (Int.repr 2) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul
                 (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                   (Ebinop Omul (Econst_int (Int.repr 2) tint)
                     (Etempvar _x tdouble) tdouble) tdouble) tdouble) :: nil))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 3) tint))))))
|}.

Definition f_shapes1dP3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_xx, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _densematn_get (Tfunction
                             ((tptr tdouble) :: tint :: tint :: tint :: nil)
                             tdouble cc_default))
      ((Etempvar _xx (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0) tint) ::
       nil))
    (Sset _x (Etempvar _t'1 tdouble)))
  (Ssequence
    (Sifthenelse (Etempvar _N (tptr tdouble))
      (Ssequence
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _N (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Ebinop Omul
             (Ebinop Omul
               (Ebinop Omul
                 (Ebinop Odiv
                   (Eunop Oneg
                     (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                     tdouble) (Econst_int (Int.repr 16) tint) tdouble)
                 (Ebinop Osub (Econst_int (Int.repr 1) tint)
                   (Etempvar _x tdouble) tdouble) tdouble)
               (Ebinop Osub (Econst_int (Int.repr 1) tint)
                 (Ebinop Omul (Econst_int (Int.repr 3) tint)
                   (Etempvar _x tdouble) tdouble) tdouble) tdouble)
             (Ebinop Oadd (Econst_int (Int.repr 1) tint)
               (Ebinop Omul (Econst_int (Int.repr 3) tint)
                 (Etempvar _x tdouble) tdouble) tdouble) tdouble) :: nil))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _N (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) ::
             (Ebinop Omul
               (Ebinop Omul
                 (Ebinop Omul
                   (Ebinop Odiv
                     (Econst_float (Float.of_bits (Int64.repr 4621256167635550208)) tdouble)
                     (Econst_int (Int.repr 16) tint) tdouble)
                   (Ebinop Osub (Econst_int (Int.repr 1) tint)
                     (Etempvar _x tdouble) tdouble) tdouble)
                 (Ebinop Osub (Econst_int (Int.repr 1) tint)
                   (Ebinop Omul (Econst_int (Int.repr 3) tint)
                     (Etempvar _x tdouble) tdouble) tdouble) tdouble)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Etempvar _x tdouble) tdouble) tdouble) :: nil))
          (Ssequence
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 2) tint) ::
               (Ebinop Omul
                 (Ebinop Omul
                   (Ebinop Omul
                     (Ebinop Odiv
                       (Econst_float (Float.of_bits (Int64.repr 4621256167635550208)) tdouble)
                       (Econst_int (Int.repr 16) tint) tdouble)
                     (Ebinop Osub (Econst_int (Int.repr 1) tint)
                       (Etempvar _x tdouble) tdouble) tdouble)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Ebinop Omul (Econst_int (Int.repr 3) tint)
                       (Etempvar _x tdouble) tdouble) tdouble) tdouble)
                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                   (Etempvar _x tdouble) tdouble) tdouble) :: nil))
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 3) tint) ::
               (Ebinop Omul
                 (Ebinop Omul
                   (Ebinop Omul
                     (Ebinop Odiv
                       (Eunop Oneg
                         (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                         tdouble) (Econst_int (Int.repr 16) tint) tdouble)
                     (Ebinop Osub (Econst_int (Int.repr 1) tint)
                       (Ebinop Omul (Econst_int (Int.repr 3) tint)
                         (Etempvar _x tdouble) tdouble) tdouble) tdouble)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Ebinop Omul (Econst_int (Int.repr 3) tint)
                       (Etempvar _x tdouble) tdouble) tdouble) tdouble)
                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                   (Etempvar _x tdouble) tdouble) tdouble) :: nil)))))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _dN (tptr tdouble))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _dN (tptr tdouble)) ::
             (Econst_int (Int.repr 4) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Ebinop Omul
               (Ebinop Odiv
                 (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                 (Econst_int (Int.repr 16) tint) tdouble)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Ebinop Omul (Etempvar _x tdouble)
                   (Ebinop Oadd (Econst_int (Int.repr 18) tint)
                     (Ebinop Omul (Etempvar _x tdouble)
                       (Eunop Oneg (Econst_int (Int.repr 27) tint) tint)
                       tdouble) tdouble) tdouble) tdouble) tdouble) :: nil))
          (Ssequence
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _dN (tptr tdouble)) ::
               (Econst_int (Int.repr 4) tint) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul
                 (Ebinop Odiv
                   (Econst_float (Float.of_bits (Int64.repr 4621256167635550208)) tdouble)
                   (Econst_int (Int.repr 16) tint) tdouble)
                 (Ebinop Oadd
                   (Eunop Oneg (Econst_int (Int.repr 3) tint) tint)
                   (Ebinop Omul (Etempvar _x tdouble)
                     (Ebinop Oadd
                       (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)
                       (Ebinop Omul (Etempvar _x tdouble)
                         (Econst_int (Int.repr 9) tint) tdouble) tdouble)
                     tdouble) tdouble) tdouble) :: nil))
            (Ssequence
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 4) tint) ::
                 (Econst_int (Int.repr 2) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Omul
                   (Ebinop Odiv
                     (Econst_float (Float.of_bits (Int64.repr 4621256167635550208)) tdouble)
                     (Econst_int (Int.repr 16) tint) tdouble)
                   (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                     (Ebinop Omul (Etempvar _x tdouble)
                       (Ebinop Oadd
                         (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)
                         (Ebinop Omul (Etempvar _x tdouble)
                           (Eunop Oneg (Econst_int (Int.repr 9) tint) tint)
                           tdouble) tdouble) tdouble) tdouble) tdouble) ::
                 nil))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 4) tint) ::
                 (Econst_int (Int.repr 3) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Omul
                   (Ebinop Odiv
                     (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                     (Econst_int (Int.repr 16) tint) tdouble)
                   (Ebinop Oadd
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                     (Ebinop Omul (Etempvar _x tdouble)
                       (Ebinop Oadd (Econst_int (Int.repr 18) tint)
                         (Ebinop Omul (Etempvar _x tdouble)
                           (Econst_int (Int.repr 27) tint) tdouble) tdouble)
                       tdouble) tdouble) tdouble) :: nil)))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 4) tint))))))
|}.

Definition f_shapes2dP1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_x, (tptr tdouble)) :: nil);
  fn_vars := ((_Nx, (tarray tdouble 2)) :: (_dNx, (tarray tdouble 2)) ::
              (_Ny, (tarray tdouble 2)) :: (_dNy, (tarray tdouble 2)) :: nil);
  fn_temps := ((_t'24, tdouble) :: (_t'23, tdouble) :: (_t'22, tdouble) ::
               (_t'21, tdouble) :: (_t'20, tdouble) :: (_t'19, tdouble) ::
               (_t'18, tdouble) :: (_t'17, tdouble) :: (_t'16, tdouble) ::
               (_t'15, tdouble) :: (_t'14, tdouble) :: (_t'13, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _shapes1dP1 (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))
    ((Evar _Nx (tarray tdouble 2)) :: (Evar _dNx (tarray tdouble 2)) ::
     (Ebinop Oadd (Etempvar _x (tptr tdouble)) (Econst_int (Int.repr 0) tint)
       (tptr tdouble)) :: nil))
  (Ssequence
    (Scall None
      (Evar _shapes1dP1 (Tfunction
                          ((tptr tdouble) :: (tptr tdouble) ::
                           (tptr tdouble) :: nil) tint cc_default))
      ((Evar _Ny (tarray tdouble 2)) :: (Evar _dNy (tarray tdouble 2)) ::
       (Ebinop Oadd (Etempvar _x (tptr tdouble))
         (Econst_int (Int.repr 1) tint) (tptr tdouble)) :: nil))
    (Ssequence
      (Sifthenelse (Etempvar _N (tptr tdouble))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Nx (tarray tdouble 2)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Scall (Some _t'2)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Ny (tarray tdouble 2)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil)))
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul (Etempvar _t'1 tdouble) (Etempvar _t'2 tdouble)
                 tdouble) :: nil)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Nx (tarray tdouble 2)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) :: nil))
                (Scall (Some _t'4)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 2)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _N (tptr tdouble)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Ebinop Omul (Etempvar _t'3 tdouble) (Etempvar _t'4 tdouble)
                   tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 1) tint) :: nil))
                  (Scall (Some _t'6)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Ny (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 1) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _N (tptr tdouble)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Ebinop Omul (Etempvar _t'5 tdouble)
                     (Etempvar _t'6 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Scall (Some _t'8)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Ny (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 1) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _N (tptr tdouble)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 3) tint) ::
                   (Ebinop Omul (Etempvar _t'7 tdouble)
                     (Etempvar _t'8 tdouble) tdouble) :: nil))))))
        Sskip)
      (Ssequence
        (Sifthenelse (Etempvar _dN (tptr tdouble))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _dNx (tarray tdouble 2)) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Scall (Some _t'10)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 2)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 4) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Omul (Etempvar _t'9 tdouble)
                   (Etempvar _t'10 tdouble) tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'11)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Scall (Some _t'12)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _dNy (tarray tdouble 2)) ::
                     (Econst_int (Int.repr 2) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _dN (tptr tdouble)) ::
                   (Econst_int (Int.repr 4) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Ebinop Omul (Etempvar _t'11 tdouble)
                     (Etempvar _t'12 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'13)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _dNx (tarray tdouble 2)) ::
                       (Econst_int (Int.repr 2) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Scall (Some _t'14)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Ny (tarray tdouble 2)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil)))
                  (Scall None
                    (Evar _densematn_set (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: tdouble :: nil) tvoid
                                           cc_default))
                    ((Etempvar _dN (tptr tdouble)) ::
                     (Econst_int (Int.repr 4) tint) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _t'13 tdouble)
                       (Etempvar _t'14 tdouble) tdouble) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'15)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Nx (tarray tdouble 2)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Scall (Some _t'16)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _dNy (tarray tdouble 2)) ::
                         (Econst_int (Int.repr 2) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Scall None
                      (Evar _densematn_set (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: tdouble :: nil)
                                             tvoid cc_default))
                      ((Etempvar _dN (tptr tdouble)) ::
                       (Econst_int (Int.repr 4) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Ebinop Omul (Etempvar _t'15 tdouble)
                         (Etempvar _t'16 tdouble) tdouble) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'17)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _dNx (tarray tdouble 2)) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) :: nil))
                        (Scall (Some _t'18)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Ny (tarray tdouble 2)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 1) tint) :: nil)))
                      (Scall None
                        (Evar _densematn_set (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: tdouble ::
                                                nil) tvoid cc_default))
                        ((Etempvar _dN (tptr tdouble)) ::
                         (Econst_int (Int.repr 4) tint) ::
                         (Econst_int (Int.repr 2) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Ebinop Omul (Etempvar _t'17 tdouble)
                           (Etempvar _t'18 tdouble) tdouble) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'19)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 2)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 1) tint) :: nil))
                          (Scall (Some _t'20)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _dNy (tarray tdouble 2)) ::
                             (Econst_int (Int.repr 2) tint) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _dN (tptr tdouble)) ::
                           (Econst_int (Int.repr 4) tint) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Ebinop Omul (Etempvar _t'19 tdouble)
                             (Etempvar _t'20 tdouble) tdouble) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'21)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _dNx (tarray tdouble 2)) ::
                               (Econst_int (Int.repr 2) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall (Some _t'22)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Ny (tarray tdouble 2)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _dN (tptr tdouble)) ::
                             (Econst_int (Int.repr 4) tint) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Ebinop Omul (Etempvar _t'21 tdouble)
                               (Etempvar _t'22 tdouble) tdouble) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'23)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Nx (tarray tdouble 2)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall (Some _t'24)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _dNy (tarray tdouble 2)) ::
                               (Econst_int (Int.repr 2) tint) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _dN (tptr tdouble)) ::
                             (Econst_int (Int.repr 4) tint) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Ebinop Omul (Etempvar _t'23 tdouble)
                               (Etempvar _t'24 tdouble) tdouble) :: nil))))))))))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 4) tint)))))))
|}.

Definition f_shapes2dP2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_x, (tptr tdouble)) :: nil);
  fn_vars := ((_Nx, (tarray tdouble 3)) :: (_dNx, (tarray tdouble 3)) ::
              (_Ny, (tarray tdouble 3)) :: (_dNy, (tarray tdouble 3)) :: nil);
  fn_temps := ((_t'54, tdouble) :: (_t'53, tdouble) :: (_t'52, tdouble) ::
               (_t'51, tdouble) :: (_t'50, tdouble) :: (_t'49, tdouble) ::
               (_t'48, tdouble) :: (_t'47, tdouble) :: (_t'46, tdouble) ::
               (_t'45, tdouble) :: (_t'44, tdouble) :: (_t'43, tdouble) ::
               (_t'42, tdouble) :: (_t'41, tdouble) :: (_t'40, tdouble) ::
               (_t'39, tdouble) :: (_t'38, tdouble) :: (_t'37, tdouble) ::
               (_t'36, tdouble) :: (_t'35, tdouble) :: (_t'34, tdouble) ::
               (_t'33, tdouble) :: (_t'32, tdouble) :: (_t'31, tdouble) ::
               (_t'30, tdouble) :: (_t'29, tdouble) :: (_t'28, tdouble) ::
               (_t'27, tdouble) :: (_t'26, tdouble) :: (_t'25, tdouble) ::
               (_t'24, tdouble) :: (_t'23, tdouble) :: (_t'22, tdouble) ::
               (_t'21, tdouble) :: (_t'20, tdouble) :: (_t'19, tdouble) ::
               (_t'18, tdouble) :: (_t'17, tdouble) :: (_t'16, tdouble) ::
               (_t'15, tdouble) :: (_t'14, tdouble) :: (_t'13, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _shapes1dP2 (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))
    ((Evar _Nx (tarray tdouble 3)) :: (Evar _dNx (tarray tdouble 3)) ::
     (Ebinop Oadd (Etempvar _x (tptr tdouble)) (Econst_int (Int.repr 0) tint)
       (tptr tdouble)) :: nil))
  (Ssequence
    (Scall None
      (Evar _shapes1dP2 (Tfunction
                          ((tptr tdouble) :: (tptr tdouble) ::
                           (tptr tdouble) :: nil) tint cc_default))
      ((Evar _Ny (tarray tdouble 3)) :: (Evar _dNy (tarray tdouble 3)) ::
       (Ebinop Oadd (Etempvar _x (tptr tdouble))
         (Econst_int (Int.repr 1) tint) (tptr tdouble)) :: nil))
    (Ssequence
      (Sifthenelse (Etempvar _N (tptr tdouble))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Nx (tarray tdouble 3)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Scall (Some _t'2)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Ny (tarray tdouble 3)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil)))
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul (Etempvar _t'1 tdouble) (Etempvar _t'2 tdouble)
                 tdouble) :: nil)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Nx (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) :: nil))
                (Scall (Some _t'4)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _N (tptr tdouble)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Ebinop Omul (Etempvar _t'3 tdouble) (Etempvar _t'4 tdouble)
                   tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 2) tint) :: nil))
                  (Scall (Some _t'6)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Ny (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _N (tptr tdouble)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Ebinop Omul (Etempvar _t'5 tdouble)
                     (Etempvar _t'6 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Nx (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 2) tint) :: nil))
                    (Scall (Some _t'8)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Ny (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 1) tint) :: nil)))
                  (Scall None
                    (Evar _densematn_set (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: tdouble :: nil) tvoid
                                           cc_default))
                    ((Etempvar _N (tptr tdouble)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 3) tint) ::
                     (Ebinop Omul (Etempvar _t'7 tdouble)
                       (Etempvar _t'8 tdouble) tdouble) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Nx (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 2) tint) :: nil))
                      (Scall (Some _t'10)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Ny (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 2) tint) :: nil)))
                    (Scall None
                      (Evar _densematn_set (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: tdouble :: nil)
                                             tvoid cc_default))
                      ((Etempvar _N (tptr tdouble)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 4) tint) ::
                       (Ebinop Omul (Etempvar _t'9 tdouble)
                         (Etempvar _t'10 tdouble) tdouble) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'11)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Nx (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 1) tint) :: nil))
                        (Scall (Some _t'12)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Ny (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 2) tint) :: nil)))
                      (Scall None
                        (Evar _densematn_set (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: tdouble ::
                                                nil) tvoid cc_default))
                        ((Etempvar _N (tptr tdouble)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 5) tint) ::
                         (Ebinop Omul (Etempvar _t'11 tdouble)
                           (Etempvar _t'12 tdouble) tdouble) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'13)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil))
                          (Scall (Some _t'14)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Ny (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 2) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _N (tptr tdouble)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 6) tint) ::
                           (Ebinop Omul (Etempvar _t'13 tdouble)
                             (Etempvar _t'14 tdouble) tdouble) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'15)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Nx (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall (Some _t'16)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Ny (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _N (tptr tdouble)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 7) tint) ::
                             (Ebinop Omul (Etempvar _t'15 tdouble)
                               (Etempvar _t'16 tdouble) tdouble) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'17)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Nx (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil))
                            (Scall (Some _t'18)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Ny (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _N (tptr tdouble)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 8) tint) ::
                             (Ebinop Omul (Etempvar _t'17 tdouble)
                               (Etempvar _t'18 tdouble) tdouble) :: nil)))))))))))
        Sskip)
      (Ssequence
        (Sifthenelse (Etempvar _dN (tptr tdouble))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'19)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _dNx (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 3) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Scall (Some _t'20)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 9) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Omul (Etempvar _t'19 tdouble)
                   (Etempvar _t'20 tdouble) tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'21)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Scall (Some _t'22)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _dNy (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 3) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _dN (tptr tdouble)) ::
                   (Econst_int (Int.repr 9) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Ebinop Omul (Etempvar _t'21 tdouble)
                     (Etempvar _t'22 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'23)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _dNx (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 3) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Scall (Some _t'24)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Ny (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil)))
                  (Scall None
                    (Evar _densematn_set (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: tdouble :: nil) tvoid
                                           cc_default))
                    ((Etempvar _dN (tptr tdouble)) ::
                     (Econst_int (Int.repr 9) tint) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _t'23 tdouble)
                       (Etempvar _t'24 tdouble) tdouble) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'25)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Nx (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Scall (Some _t'26)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _dNy (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 3) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Scall None
                      (Evar _densematn_set (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: tdouble :: nil)
                                             tvoid cc_default))
                      ((Etempvar _dN (tptr tdouble)) ::
                       (Econst_int (Int.repr 9) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Ebinop Omul (Etempvar _t'25 tdouble)
                         (Etempvar _t'26 tdouble) tdouble) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'27)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _dNx (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 3) tint) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 0) tint) :: nil))
                        (Scall (Some _t'28)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Ny (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 0) tint) :: nil)))
                      (Scall None
                        (Evar _densematn_set (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: tdouble ::
                                                nil) tvoid cc_default))
                        ((Etempvar _dN (tptr tdouble)) ::
                         (Econst_int (Int.repr 9) tint) ::
                         (Econst_int (Int.repr 2) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Ebinop Omul (Etempvar _t'27 tdouble)
                           (Etempvar _t'28 tdouble) tdouble) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'29)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 2) tint) :: nil))
                          (Scall (Some _t'30)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _dNy (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _dN (tptr tdouble)) ::
                           (Econst_int (Int.repr 9) tint) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Ebinop Omul (Etempvar _t'29 tdouble)
                             (Etempvar _t'30 tdouble) tdouble) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'31)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _dNx (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 3) tint) ::
                               (Econst_int (Int.repr 2) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall (Some _t'32)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Ny (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _dN (tptr tdouble)) ::
                             (Econst_int (Int.repr 9) tint) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Ebinop Omul (Etempvar _t'31 tdouble)
                               (Etempvar _t'32 tdouble) tdouble) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'33)
                                (Evar _densematn_get (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: nil) tdouble
                                                       cc_default))
                                ((Evar _Nx (tarray tdouble 3)) ::
                                 (Econst_int (Int.repr 1) tint) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Econst_int (Int.repr 2) tint) :: nil))
                              (Scall (Some _t'34)
                                (Evar _densematn_get (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: nil) tdouble
                                                       cc_default))
                                ((Evar _dNy (tarray tdouble 3)) ::
                                 (Econst_int (Int.repr 3) tint) ::
                                 (Econst_int (Int.repr 1) tint) ::
                                 (Econst_int (Int.repr 0) tint) :: nil)))
                            (Scall None
                              (Evar _densematn_set (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      tdouble :: nil) tvoid
                                                     cc_default))
                              ((Etempvar _dN (tptr tdouble)) ::
                               (Econst_int (Int.repr 9) tint) ::
                               (Econst_int (Int.repr 3) tint) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Ebinop Omul (Etempvar _t'33 tdouble)
                                 (Etempvar _t'34 tdouble) tdouble) :: nil)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'35)
                                  (Evar _densematn_get (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: nil)
                                                         tdouble cc_default))
                                  ((Evar _dNx (tarray tdouble 3)) ::
                                   (Econst_int (Int.repr 3) tint) ::
                                   (Econst_int (Int.repr 2) tint) ::
                                   (Econst_int (Int.repr 0) tint) :: nil))
                                (Scall (Some _t'36)
                                  (Evar _densematn_get (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: nil)
                                                         tdouble cc_default))
                                  ((Evar _Ny (tarray tdouble 3)) ::
                                   (Econst_int (Int.repr 1) tint) ::
                                   (Econst_int (Int.repr 0) tint) ::
                                   (Econst_int (Int.repr 2) tint) :: nil)))
                              (Scall None
                                (Evar _densematn_set (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: tdouble ::
                                                        nil) tvoid
                                                       cc_default))
                                ((Etempvar _dN (tptr tdouble)) ::
                                 (Econst_int (Int.repr 9) tint) ::
                                 (Econst_int (Int.repr 4) tint) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Ebinop Omul (Etempvar _t'35 tdouble)
                                   (Etempvar _t'36 tdouble) tdouble) :: nil)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'37)
                                    (Evar _densematn_get (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint :: nil)
                                                           tdouble
                                                           cc_default))
                                    ((Evar _Nx (tarray tdouble 3)) ::
                                     (Econst_int (Int.repr 1) tint) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Econst_int (Int.repr 2) tint) :: nil))
                                  (Scall (Some _t'38)
                                    (Evar _densematn_get (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint :: nil)
                                                           tdouble
                                                           cc_default))
                                    ((Evar _dNy (tarray tdouble 3)) ::
                                     (Econst_int (Int.repr 3) tint) ::
                                     (Econst_int (Int.repr 2) tint) ::
                                     (Econst_int (Int.repr 0) tint) :: nil)))
                                (Scall None
                                  (Evar _densematn_set (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: tdouble ::
                                                          nil) tvoid
                                                         cc_default))
                                  ((Etempvar _dN (tptr tdouble)) ::
                                   (Econst_int (Int.repr 9) tint) ::
                                   (Econst_int (Int.repr 4) tint) ::
                                   (Econst_int (Int.repr 1) tint) ::
                                   (Ebinop Omul (Etempvar _t'37 tdouble)
                                     (Etempvar _t'38 tdouble) tdouble) ::
                                   nil)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'39)
                                      (Evar _densematn_get (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint :: nil)
                                                             tdouble
                                                             cc_default))
                                      ((Evar _dNx (tarray tdouble 3)) ::
                                       (Econst_int (Int.repr 3) tint) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Econst_int (Int.repr 0) tint) :: nil))
                                    (Scall (Some _t'40)
                                      (Evar _densematn_get (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint :: nil)
                                                             tdouble
                                                             cc_default))
                                      ((Evar _Ny (tarray tdouble 3)) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Econst_int (Int.repr 0) tint) ::
                                       (Econst_int (Int.repr 2) tint) :: nil)))
                                  (Scall None
                                    (Evar _densematn_set (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint ::
                                                            tdouble :: nil)
                                                           tvoid cc_default))
                                    ((Etempvar _dN (tptr tdouble)) ::
                                     (Econst_int (Int.repr 9) tint) ::
                                     (Econst_int (Int.repr 5) tint) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Ebinop Omul (Etempvar _t'39 tdouble)
                                       (Etempvar _t'40 tdouble) tdouble) ::
                                     nil)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'41)
                                        (Evar _densematn_get (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint :: nil)
                                                               tdouble
                                                               cc_default))
                                        ((Evar _Nx (tarray tdouble 3)) ::
                                         (Econst_int (Int.repr 1) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         (Econst_int (Int.repr 1) tint) ::
                                         nil))
                                      (Scall (Some _t'42)
                                        (Evar _densematn_get (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint :: nil)
                                                               tdouble
                                                               cc_default))
                                        ((Evar _dNy (tarray tdouble 3)) ::
                                         (Econst_int (Int.repr 3) tint) ::
                                         (Econst_int (Int.repr 2) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         nil)))
                                    (Scall None
                                      (Evar _densematn_set (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint ::
                                                              tdouble :: nil)
                                                             tvoid
                                                             cc_default))
                                      ((Etempvar _dN (tptr tdouble)) ::
                                       (Econst_int (Int.repr 9) tint) ::
                                       (Econst_int (Int.repr 5) tint) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Ebinop Omul (Etempvar _t'41 tdouble)
                                         (Etempvar _t'42 tdouble) tdouble) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'43)
                                          (Evar _densematn_get (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  nil)
                                                                 tdouble
                                                                 cc_default))
                                          ((Evar _dNx (tarray tdouble 3)) ::
                                           (Econst_int (Int.repr 3) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           nil))
                                        (Scall (Some _t'44)
                                          (Evar _densematn_get (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  nil)
                                                                 tdouble
                                                                 cc_default))
                                          ((Evar _Ny (tarray tdouble 3)) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           (Econst_int (Int.repr 2) tint) ::
                                           nil)))
                                      (Scall None
                                        (Evar _densematn_set (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint ::
                                                                tdouble ::
                                                                nil) tvoid
                                                               cc_default))
                                        ((Etempvar _dN (tptr tdouble)) ::
                                         (Econst_int (Int.repr 9) tint) ::
                                         (Econst_int (Int.repr 6) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         (Ebinop Omul
                                           (Etempvar _t'43 tdouble)
                                           (Etempvar _t'44 tdouble) tdouble) ::
                                         nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'45)
                                            (Evar _densematn_get (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                   tdouble
                                                                   cc_default))
                                            ((Evar _Nx (tarray tdouble 3)) ::
                                             (Econst_int (Int.repr 1) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             nil))
                                          (Scall (Some _t'46)
                                            (Evar _densematn_get (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                   tdouble
                                                                   cc_default))
                                            ((Evar _dNy (tarray tdouble 3)) ::
                                             (Econst_int (Int.repr 3) tint) ::
                                             (Econst_int (Int.repr 2) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             nil)))
                                        (Scall None
                                          (Evar _densematn_set (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  tdouble ::
                                                                  nil) tvoid
                                                                 cc_default))
                                          ((Etempvar _dN (tptr tdouble)) ::
                                           (Econst_int (Int.repr 9) tint) ::
                                           (Econst_int (Int.repr 6) tint) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           (Ebinop Omul
                                             (Etempvar _t'45 tdouble)
                                             (Etempvar _t'46 tdouble)
                                             tdouble) :: nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'47)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _dNx (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 3) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               nil))
                                            (Scall (Some _t'48)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _Ny (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               nil)))
                                          (Scall None
                                            (Evar _densematn_set (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tdouble ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _dN (tptr tdouble)) ::
                                             (Econst_int (Int.repr 9) tint) ::
                                             (Econst_int (Int.repr 7) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Ebinop Omul
                                               (Etempvar _t'47 tdouble)
                                               (Etempvar _t'48 tdouble)
                                               tdouble) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'49)
                                                (Evar _densematn_get 
                                                (Tfunction
                                                  ((tptr tdouble) :: tint ::
                                                   tint :: tint :: nil)
                                                  tdouble cc_default))
                                                ((Evar _Nx (tarray tdouble 3)) ::
                                                 (Econst_int (Int.repr 1) tint) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 nil))
                                              (Scall (Some _t'50)
                                                (Evar _densematn_get 
                                                (Tfunction
                                                  ((tptr tdouble) :: tint ::
                                                   tint :: tint :: nil)
                                                  tdouble cc_default))
                                                ((Evar _dNy (tarray tdouble 3)) ::
                                                 (Econst_int (Int.repr 3) tint) ::
                                                 (Econst_int (Int.repr 1) tint) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 nil)))
                                            (Scall None
                                              (Evar _densematn_set (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tdouble ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _dN (tptr tdouble)) ::
                                               (Econst_int (Int.repr 9) tint) ::
                                               (Econst_int (Int.repr 7) tint) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               (Ebinop Omul
                                                 (Etempvar _t'49 tdouble)
                                                 (Etempvar _t'50 tdouble)
                                                 tdouble) :: nil)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'51)
                                                  (Evar _densematn_get 
                                                  (Tfunction
                                                    ((tptr tdouble) ::
                                                     tint :: tint :: tint ::
                                                     nil) tdouble cc_default))
                                                  ((Evar _dNx (tarray tdouble 3)) ::
                                                   (Econst_int (Int.repr 3) tint) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   nil))
                                                (Scall (Some _t'52)
                                                  (Evar _densematn_get 
                                                  (Tfunction
                                                    ((tptr tdouble) ::
                                                     tint :: tint :: tint ::
                                                     nil) tdouble cc_default))
                                                  ((Evar _Ny (tarray tdouble 3)) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   nil)))
                                              (Scall None
                                                (Evar _densematn_set 
                                                (Tfunction
                                                  ((tptr tdouble) :: tint ::
                                                   tint :: tint :: tdouble ::
                                                   nil) tvoid cc_default))
                                                ((Etempvar _dN (tptr tdouble)) ::
                                                 (Econst_int (Int.repr 9) tint) ::
                                                 (Econst_int (Int.repr 8) tint) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 (Ebinop Omul
                                                   (Etempvar _t'51 tdouble)
                                                   (Etempvar _t'52 tdouble)
                                                   tdouble) :: nil)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'53)
                                                  (Evar _densematn_get 
                                                  (Tfunction
                                                    ((tptr tdouble) ::
                                                     tint :: tint :: tint ::
                                                     nil) tdouble cc_default))
                                                  ((Evar _Nx (tarray tdouble 3)) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   nil))
                                                (Scall (Some _t'54)
                                                  (Evar _densematn_get 
                                                  (Tfunction
                                                    ((tptr tdouble) ::
                                                     tint :: tint :: tint ::
                                                     nil) tdouble cc_default))
                                                  ((Evar _dNy (tarray tdouble 3)) ::
                                                   (Econst_int (Int.repr 3) tint) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   nil)))
                                              (Scall None
                                                (Evar _densematn_set 
                                                (Tfunction
                                                  ((tptr tdouble) :: tint ::
                                                   tint :: tint :: tdouble ::
                                                   nil) tvoid cc_default))
                                                ((Etempvar _dN (tptr tdouble)) ::
                                                 (Econst_int (Int.repr 9) tint) ::
                                                 (Econst_int (Int.repr 8) tint) ::
                                                 (Econst_int (Int.repr 1) tint) ::
                                                 (Ebinop Omul
                                                   (Etempvar _t'53 tdouble)
                                                   (Etempvar _t'54 tdouble)
                                                   tdouble) :: nil))))))))))))))))))))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 9) tint)))))))
|}.

Definition f_shapes2dS2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_x, (tptr tdouble)) :: nil);
  fn_vars := ((_Nx, (tarray tdouble 3)) :: (_dNx, (tarray tdouble 3)) ::
              (_Ny, (tarray tdouble 3)) :: (_dNy, (tarray tdouble 3)) :: nil);
  fn_temps := ((_t'48, tdouble) :: (_t'47, tdouble) :: (_t'46, tdouble) ::
               (_t'45, tdouble) :: (_t'44, tdouble) :: (_t'43, tdouble) ::
               (_t'42, tdouble) :: (_t'41, tdouble) :: (_t'40, tdouble) ::
               (_t'39, tdouble) :: (_t'38, tdouble) :: (_t'37, tdouble) ::
               (_t'36, tdouble) :: (_t'35, tdouble) :: (_t'34, tdouble) ::
               (_t'33, tdouble) :: (_t'32, tdouble) :: (_t'31, tdouble) ::
               (_t'30, tdouble) :: (_t'29, tdouble) :: (_t'28, tdouble) ::
               (_t'27, tdouble) :: (_t'26, tdouble) :: (_t'25, tdouble) ::
               (_t'24, tdouble) :: (_t'23, tdouble) :: (_t'22, tdouble) ::
               (_t'21, tdouble) :: (_t'20, tdouble) :: (_t'19, tdouble) ::
               (_t'18, tdouble) :: (_t'17, tdouble) :: (_t'16, tdouble) ::
               (_t'15, tdouble) :: (_t'14, tdouble) :: (_t'13, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _shapes1dP2 (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))
    ((Evar _Nx (tarray tdouble 3)) :: (Evar _dNx (tarray tdouble 3)) ::
     (Ebinop Oadd (Etempvar _x (tptr tdouble)) (Econst_int (Int.repr 0) tint)
       (tptr tdouble)) :: nil))
  (Ssequence
    (Scall None
      (Evar _shapes1dP2 (Tfunction
                          ((tptr tdouble) :: (tptr tdouble) ::
                           (tptr tdouble) :: nil) tint cc_default))
      ((Evar _Ny (tarray tdouble 3)) :: (Evar _dNy (tarray tdouble 3)) ::
       (Ebinop Oadd (Etempvar _x (tptr tdouble))
         (Econst_int (Int.repr 1) tint) (tptr tdouble)) :: nil))
    (Ssequence
      (Sifthenelse (Etempvar _N (tptr tdouble))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Nx (tarray tdouble 3)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Scall (Some _t'2)
                (Evar _densematn_get (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: nil) tdouble cc_default))
                ((Evar _Ny (tarray tdouble 3)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) :: nil)))
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Ebinop Omul (Etempvar _t'1 tdouble) (Etempvar _t'2 tdouble)
                 tdouble) :: nil)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Nx (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) :: nil))
                (Scall (Some _t'4)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _N (tptr tdouble)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Ebinop Omul (Etempvar _t'3 tdouble) (Etempvar _t'4 tdouble)
                   tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 2) tint) :: nil))
                  (Scall (Some _t'6)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Ny (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _N (tptr tdouble)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Ebinop Omul (Etempvar _t'5 tdouble)
                     (Etempvar _t'6 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Nx (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 2) tint) :: nil))
                    (Scall (Some _t'8)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Ny (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 1) tint) :: nil)))
                  (Scall None
                    (Evar _densematn_set (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: tdouble :: nil) tvoid
                                           cc_default))
                    ((Etempvar _N (tptr tdouble)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 3) tint) ::
                     (Ebinop Omul (Etempvar _t'7 tdouble)
                       (Etempvar _t'8 tdouble) tdouble) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Nx (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 2) tint) :: nil))
                      (Scall (Some _t'10)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Ny (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 2) tint) :: nil)))
                    (Scall None
                      (Evar _densematn_set (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: tdouble :: nil)
                                             tvoid cc_default))
                      ((Etempvar _N (tptr tdouble)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 4) tint) ::
                       (Ebinop Omul (Etempvar _t'9 tdouble)
                         (Etempvar _t'10 tdouble) tdouble) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'11)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Nx (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 1) tint) :: nil))
                        (Scall (Some _t'12)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Ny (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 2) tint) :: nil)))
                      (Scall None
                        (Evar _densematn_set (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: tdouble ::
                                                nil) tvoid cc_default))
                        ((Etempvar _N (tptr tdouble)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 5) tint) ::
                         (Ebinop Omul (Etempvar _t'11 tdouble)
                           (Etempvar _t'12 tdouble) tdouble) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'13)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil))
                          (Scall (Some _t'14)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Ny (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 2) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _N (tptr tdouble)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 6) tint) ::
                           (Ebinop Omul (Etempvar _t'13 tdouble)
                             (Etempvar _t'14 tdouble) tdouble) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'15)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil))
                          (Scall (Some _t'16)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Ny (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 1) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _N (tptr tdouble)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 7) tint) ::
                           (Ebinop Omul (Etempvar _t'15 tdouble)
                             (Etempvar _t'16 tdouble) tdouble) :: nil))))))))))
        Sskip)
      (Ssequence
        (Sifthenelse (Etempvar _dN (tptr tdouble))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'17)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _dNx (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 3) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Scall (Some _t'18)
                  (Evar _densematn_get (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: nil) tdouble cc_default))
                  ((Evar _Ny (tarray tdouble 3)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 8) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Omul (Etempvar _t'17 tdouble)
                   (Etempvar _t'18 tdouble) tdouble) :: nil)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'19)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _Nx (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Scall (Some _t'20)
                    (Evar _densematn_get (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: nil) tdouble cc_default))
                    ((Evar _dNy (tarray tdouble 3)) ::
                     (Econst_int (Int.repr 3) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _dN (tptr tdouble)) ::
                   (Econst_int (Int.repr 8) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Ebinop Omul (Etempvar _t'19 tdouble)
                     (Etempvar _t'20 tdouble) tdouble) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'21)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _dNx (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 3) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Scall (Some _t'22)
                      (Evar _densematn_get (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: nil) tdouble
                                             cc_default))
                      ((Evar _Ny (tarray tdouble 3)) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 0) tint) :: nil)))
                  (Scall None
                    (Evar _densematn_set (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            tint :: tdouble :: nil) tvoid
                                           cc_default))
                    ((Etempvar _dN (tptr tdouble)) ::
                     (Econst_int (Int.repr 8) tint) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _t'21 tdouble)
                       (Etempvar _t'22 tdouble) tdouble) :: nil)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'23)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _Nx (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Scall (Some _t'24)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Evar _dNy (tarray tdouble 3)) ::
                         (Econst_int (Int.repr 3) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Scall None
                      (Evar _densematn_set (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: tint :: tdouble :: nil)
                                             tvoid cc_default))
                      ((Etempvar _dN (tptr tdouble)) ::
                       (Econst_int (Int.repr 8) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Ebinop Omul (Etempvar _t'23 tdouble)
                         (Etempvar _t'24 tdouble) tdouble) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'25)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _dNx (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 3) tint) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 0) tint) :: nil))
                        (Scall (Some _t'26)
                          (Evar _densematn_get (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: nil)
                                                 tdouble cc_default))
                          ((Evar _Ny (tarray tdouble 3)) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Econst_int (Int.repr 0) tint) :: nil)))
                      (Scall None
                        (Evar _densematn_set (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: tdouble ::
                                                nil) tvoid cc_default))
                        ((Etempvar _dN (tptr tdouble)) ::
                         (Econst_int (Int.repr 8) tint) ::
                         (Econst_int (Int.repr 2) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Ebinop Omul (Etempvar _t'25 tdouble)
                           (Etempvar _t'26 tdouble) tdouble) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'27)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _Nx (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 1) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 2) tint) :: nil))
                          (Scall (Some _t'28)
                            (Evar _densematn_get (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint :: nil)
                                                   tdouble cc_default))
                            ((Evar _dNy (tarray tdouble 3)) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 0) tint) :: nil)))
                        (Scall None
                          (Evar _densematn_set (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: tint :: tdouble ::
                                                  nil) tvoid cc_default))
                          ((Etempvar _dN (tptr tdouble)) ::
                           (Econst_int (Int.repr 8) tint) ::
                           (Econst_int (Int.repr 2) tint) ::
                           (Econst_int (Int.repr 1) tint) ::
                           (Ebinop Omul (Etempvar _t'27 tdouble)
                             (Etempvar _t'28 tdouble) tdouble) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'29)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _dNx (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 3) tint) ::
                               (Econst_int (Int.repr 2) tint) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall (Some _t'30)
                              (Evar _densematn_get (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      nil) tdouble
                                                     cc_default))
                              ((Evar _Ny (tarray tdouble 3)) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Econst_int (Int.repr 1) tint) :: nil)))
                          (Scall None
                            (Evar _densematn_set (Tfunction
                                                   ((tptr tdouble) :: tint ::
                                                    tint :: tint ::
                                                    tdouble :: nil) tvoid
                                                   cc_default))
                            ((Etempvar _dN (tptr tdouble)) ::
                             (Econst_int (Int.repr 8) tint) ::
                             (Econst_int (Int.repr 3) tint) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Ebinop Omul (Etempvar _t'29 tdouble)
                               (Etempvar _t'30 tdouble) tdouble) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'31)
                                (Evar _densematn_get (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: nil) tdouble
                                                       cc_default))
                                ((Evar _Nx (tarray tdouble 3)) ::
                                 (Econst_int (Int.repr 1) tint) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Econst_int (Int.repr 2) tint) :: nil))
                              (Scall (Some _t'32)
                                (Evar _densematn_get (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: nil) tdouble
                                                       cc_default))
                                ((Evar _dNy (tarray tdouble 3)) ::
                                 (Econst_int (Int.repr 3) tint) ::
                                 (Econst_int (Int.repr 1) tint) ::
                                 (Econst_int (Int.repr 0) tint) :: nil)))
                            (Scall None
                              (Evar _densematn_set (Tfunction
                                                     ((tptr tdouble) ::
                                                      tint :: tint :: tint ::
                                                      tdouble :: nil) tvoid
                                                     cc_default))
                              ((Etempvar _dN (tptr tdouble)) ::
                               (Econst_int (Int.repr 8) tint) ::
                               (Econst_int (Int.repr 3) tint) ::
                               (Econst_int (Int.repr 1) tint) ::
                               (Ebinop Omul (Etempvar _t'31 tdouble)
                                 (Etempvar _t'32 tdouble) tdouble) :: nil)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'33)
                                  (Evar _densematn_get (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: nil)
                                                         tdouble cc_default))
                                  ((Evar _dNx (tarray tdouble 3)) ::
                                   (Econst_int (Int.repr 3) tint) ::
                                   (Econst_int (Int.repr 2) tint) ::
                                   (Econst_int (Int.repr 0) tint) :: nil))
                                (Scall (Some _t'34)
                                  (Evar _densematn_get (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: nil)
                                                         tdouble cc_default))
                                  ((Evar _Ny (tarray tdouble 3)) ::
                                   (Econst_int (Int.repr 1) tint) ::
                                   (Econst_int (Int.repr 0) tint) ::
                                   (Econst_int (Int.repr 2) tint) :: nil)))
                              (Scall None
                                (Evar _densematn_set (Tfunction
                                                       ((tptr tdouble) ::
                                                        tint :: tint ::
                                                        tint :: tdouble ::
                                                        nil) tvoid
                                                       cc_default))
                                ((Etempvar _dN (tptr tdouble)) ::
                                 (Econst_int (Int.repr 8) tint) ::
                                 (Econst_int (Int.repr 4) tint) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Ebinop Omul (Etempvar _t'33 tdouble)
                                   (Etempvar _t'34 tdouble) tdouble) :: nil)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'35)
                                    (Evar _densematn_get (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint :: nil)
                                                           tdouble
                                                           cc_default))
                                    ((Evar _Nx (tarray tdouble 3)) ::
                                     (Econst_int (Int.repr 1) tint) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Econst_int (Int.repr 2) tint) :: nil))
                                  (Scall (Some _t'36)
                                    (Evar _densematn_get (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint :: nil)
                                                           tdouble
                                                           cc_default))
                                    ((Evar _dNy (tarray tdouble 3)) ::
                                     (Econst_int (Int.repr 3) tint) ::
                                     (Econst_int (Int.repr 2) tint) ::
                                     (Econst_int (Int.repr 0) tint) :: nil)))
                                (Scall None
                                  (Evar _densematn_set (Tfunction
                                                         ((tptr tdouble) ::
                                                          tint :: tint ::
                                                          tint :: tdouble ::
                                                          nil) tvoid
                                                         cc_default))
                                  ((Etempvar _dN (tptr tdouble)) ::
                                   (Econst_int (Int.repr 8) tint) ::
                                   (Econst_int (Int.repr 4) tint) ::
                                   (Econst_int (Int.repr 1) tint) ::
                                   (Ebinop Omul (Etempvar _t'35 tdouble)
                                     (Etempvar _t'36 tdouble) tdouble) ::
                                   nil)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'37)
                                      (Evar _densematn_get (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint :: nil)
                                                             tdouble
                                                             cc_default))
                                      ((Evar _dNx (tarray tdouble 3)) ::
                                       (Econst_int (Int.repr 3) tint) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Econst_int (Int.repr 0) tint) :: nil))
                                    (Scall (Some _t'38)
                                      (Evar _densematn_get (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint :: nil)
                                                             tdouble
                                                             cc_default))
                                      ((Evar _Ny (tarray tdouble 3)) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Econst_int (Int.repr 0) tint) ::
                                       (Econst_int (Int.repr 2) tint) :: nil)))
                                  (Scall None
                                    (Evar _densematn_set (Tfunction
                                                           ((tptr tdouble) ::
                                                            tint :: tint ::
                                                            tint ::
                                                            tdouble :: nil)
                                                           tvoid cc_default))
                                    ((Etempvar _dN (tptr tdouble)) ::
                                     (Econst_int (Int.repr 8) tint) ::
                                     (Econst_int (Int.repr 5) tint) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Ebinop Omul (Etempvar _t'37 tdouble)
                                       (Etempvar _t'38 tdouble) tdouble) ::
                                     nil)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'39)
                                        (Evar _densematn_get (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint :: nil)
                                                               tdouble
                                                               cc_default))
                                        ((Evar _Nx (tarray tdouble 3)) ::
                                         (Econst_int (Int.repr 1) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         (Econst_int (Int.repr 1) tint) ::
                                         nil))
                                      (Scall (Some _t'40)
                                        (Evar _densematn_get (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint :: nil)
                                                               tdouble
                                                               cc_default))
                                        ((Evar _dNy (tarray tdouble 3)) ::
                                         (Econst_int (Int.repr 3) tint) ::
                                         (Econst_int (Int.repr 2) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         nil)))
                                    (Scall None
                                      (Evar _densematn_set (Tfunction
                                                             ((tptr tdouble) ::
                                                              tint :: tint ::
                                                              tint ::
                                                              tdouble :: nil)
                                                             tvoid
                                                             cc_default))
                                      ((Etempvar _dN (tptr tdouble)) ::
                                       (Econst_int (Int.repr 8) tint) ::
                                       (Econst_int (Int.repr 5) tint) ::
                                       (Econst_int (Int.repr 1) tint) ::
                                       (Ebinop Omul (Etempvar _t'39 tdouble)
                                         (Etempvar _t'40 tdouble) tdouble) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'41)
                                          (Evar _densematn_get (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  nil)
                                                                 tdouble
                                                                 cc_default))
                                          ((Evar _dNx (tarray tdouble 3)) ::
                                           (Econst_int (Int.repr 3) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           nil))
                                        (Scall (Some _t'42)
                                          (Evar _densematn_get (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  nil)
                                                                 tdouble
                                                                 cc_default))
                                          ((Evar _Ny (tarray tdouble 3)) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           (Econst_int (Int.repr 2) tint) ::
                                           nil)))
                                      (Scall None
                                        (Evar _densematn_set (Tfunction
                                                               ((tptr tdouble) ::
                                                                tint ::
                                                                tint ::
                                                                tint ::
                                                                tdouble ::
                                                                nil) tvoid
                                                               cc_default))
                                        ((Etempvar _dN (tptr tdouble)) ::
                                         (Econst_int (Int.repr 8) tint) ::
                                         (Econst_int (Int.repr 6) tint) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         (Ebinop Omul
                                           (Etempvar _t'41 tdouble)
                                           (Etempvar _t'42 tdouble) tdouble) ::
                                         nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'43)
                                            (Evar _densematn_get (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                   tdouble
                                                                   cc_default))
                                            ((Evar _Nx (tarray tdouble 3)) ::
                                             (Econst_int (Int.repr 1) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             nil))
                                          (Scall (Some _t'44)
                                            (Evar _densematn_get (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                   tdouble
                                                                   cc_default))
                                            ((Evar _dNy (tarray tdouble 3)) ::
                                             (Econst_int (Int.repr 3) tint) ::
                                             (Econst_int (Int.repr 2) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             nil)))
                                        (Scall None
                                          (Evar _densematn_set (Tfunction
                                                                 ((tptr tdouble) ::
                                                                  tint ::
                                                                  tint ::
                                                                  tint ::
                                                                  tdouble ::
                                                                  nil) tvoid
                                                                 cc_default))
                                          ((Etempvar _dN (tptr tdouble)) ::
                                           (Econst_int (Int.repr 8) tint) ::
                                           (Econst_int (Int.repr 6) tint) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           (Ebinop Omul
                                             (Etempvar _t'43 tdouble)
                                             (Etempvar _t'44 tdouble)
                                             tdouble) :: nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'45)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _dNx (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 3) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               nil))
                                            (Scall (Some _t'46)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _Ny (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               nil)))
                                          (Scall None
                                            (Evar _densematn_set (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tdouble ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _dN (tptr tdouble)) ::
                                             (Econst_int (Int.repr 8) tint) ::
                                             (Econst_int (Int.repr 7) tint) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Ebinop Omul
                                               (Etempvar _t'45 tdouble)
                                               (Etempvar _t'46 tdouble)
                                               tdouble) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'47)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _Nx (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               nil))
                                            (Scall (Some _t'48)
                                              (Evar _densematn_get (Tfunction
                                                                    ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil)
                                                                    tdouble
                                                                    cc_default))
                                              ((Evar _dNy (tarray tdouble 3)) ::
                                               (Econst_int (Int.repr 3) tint) ::
                                               (Econst_int (Int.repr 1) tint) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               nil)))
                                          (Scall None
                                            (Evar _densematn_set (Tfunction
                                                                   ((tptr tdouble) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tdouble ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _dN (tptr tdouble)) ::
                                             (Econst_int (Int.repr 8) tint) ::
                                             (Econst_int (Int.repr 7) tint) ::
                                             (Econst_int (Int.repr 1) tint) ::
                                             (Ebinop Omul
                                               (Etempvar _t'47 tdouble)
                                               (Etempvar _t'48 tdouble)
                                               tdouble) :: nil))))))))))))))))))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 8) tint)))))))
|}.

Definition f_shapes2dT1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) ::
                (_x, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tdouble) :: (_t'3, tdouble) :: (_t'2, tdouble) ::
               (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _N (tptr tdouble))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _densematn_get (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    nil) tdouble cc_default))
            ((Etempvar _x (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Scall (Some _t'2)
            (Evar _densematn_get (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    nil) tdouble cc_default))
            ((Etempvar _x (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) :: nil)))
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _N (tptr tdouble)) :: (Econst_int (Int.repr 1) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Ebinop Osub
             (Ebinop Osub (Econst_int (Int.repr 1) tint)
               (Etempvar _t'1 tdouble) tdouble) (Etempvar _t'2 tdouble)
             tdouble) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _densematn_get (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    nil) tdouble cc_default))
            ((Etempvar _x (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _N (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) :: (Etempvar _t'3 tdouble) ::
             nil)))
        (Ssequence
          (Scall (Some _t'4)
            (Evar _densematn_get (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    nil) tdouble cc_default))
            ((Etempvar _x (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) :: nil))
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _N (tptr tdouble)) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 2) tint) :: (Etempvar _t'4 tdouble) ::
             nil)))))
    Sskip)
  (Ssequence
    (Sifthenelse (Etempvar _dN (tptr tdouble))
      (Ssequence
        (Scall None
          (Evar _densematn_set (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: tint ::
                                  tdouble :: nil) tvoid cc_default))
          ((Etempvar _dN (tptr tdouble)) :: (Econst_int (Int.repr 3) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 0) tint) ::
           (Eunop Oneg
             (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
             tdouble) :: nil))
        (Ssequence
          (Scall None
            (Evar _densematn_set (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: tint ::
                                    tdouble :: nil) tvoid cc_default))
            ((Etempvar _dN (tptr tdouble)) ::
             (Econst_int (Int.repr 3) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) ::
             (Eunop Oneg
               (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
               tdouble) :: nil))
          (Ssequence
            (Scall None
              (Evar _densematn_set (Tfunction
                                     ((tptr tdouble) :: tint :: tint ::
                                      tint :: tdouble :: nil) tvoid
                                     cc_default))
              ((Etempvar _dN (tptr tdouble)) ::
               (Econst_int (Int.repr 3) tint) ::
               (Econst_int (Int.repr 1) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
               nil))
            (Ssequence
              (Scall None
                (Evar _densematn_set (Tfunction
                                       ((tptr tdouble) :: tint :: tint ::
                                        tint :: tdouble :: nil) tvoid
                                       cc_default))
                ((Etempvar _dN (tptr tdouble)) ::
                 (Econst_int (Int.repr 3) tint) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) ::
                 nil))
              (Ssequence
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _dN (tptr tdouble)) ::
                   (Econst_int (Int.repr 3) tint) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) ::
                   nil))
                (Scall None
                  (Evar _densematn_set (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          tint :: tdouble :: nil) tvoid
                                         cc_default))
                  ((Etempvar _dN (tptr tdouble)) ::
                   (Econst_int (Int.repr 3) tint) ::
                   (Econst_int (Int.repr 2) tint) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                   nil)))))))
      Sskip)
    (Sreturn (Some (Econst_int (Int.repr 3) tint)))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tint :: nil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_densematn_get,
   Gfun(External (EF_external "densematn_get"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xint :: nil)
                     AST.Xfloat cc_default))
     ((tptr tdouble) :: tint :: tint :: tint :: nil) tdouble cc_default)) ::
 (_densematn_set,
   Gfun(External (EF_external "densematn_set"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xint ::
                      AST.Xfloat :: nil) AST.Xvoid cc_default))
     ((tptr tdouble) :: tint :: tint :: tint :: tdouble :: nil) tvoid
     cc_default)) :: (_shapes1dP1, Gfun(Internal f_shapes1dP1)) ::
 (_shapes1dP2, Gfun(Internal f_shapes1dP2)) ::
 (_shapes1dP3, Gfun(Internal f_shapes1dP3)) ::
 (_shapes2dP1, Gfun(Internal f_shapes2dP1)) ::
 (_shapes2dP2, Gfun(Internal f_shapes2dP2)) ::
 (_shapes2dS2, Gfun(Internal f_shapes2dS2)) ::
 (_shapes2dT1, Gfun(Internal f_shapes2dT1)) :: nil).

Definition public_idents : list ident :=
(_shapes2dT1 :: _shapes2dS2 :: _shapes2dP2 :: _shapes2dP1 :: _shapes1dP3 ::
 _shapes1dP2 :: _shapes1dP1 :: _densematn_set :: _densematn_get ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


