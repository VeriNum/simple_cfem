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
  Definition source_file := "../src/quadrules.c".
  Definition normalized := true.
End Info.

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
Definition ___sFILE : ident := $"__sFILE".
Definition ___sFILEX : ident := $"__sFILEX".
Definition ___sbuf : ident := $"__sbuf".
Definition ___stderrp : ident := $"__stderrp".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __extra : ident := $"_extra".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __nbuf : ident := $"_nbuf".
Definition __offset : ident := $"_offset".
Definition __p : ident := $"_p".
Definition __r : ident := $"_r".
Definition __read : ident := $"_read".
Definition __seek : ident := $"_seek".
Definition __size : ident := $"_size".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __write : ident := $"_write".
Definition _d : ident := $"d".
Definition _exit : ident := $"exit".
Definition _fprintf : ident := $"fprintf".
Definition _gauss2d_npoint1d : ident := $"gauss2d_npoint1d".
Definition _gauss2d_point : ident := $"gauss2d_point".
Definition _gauss2d_weight : ident := $"gauss2d_weight".
Definition _gauss_point : ident := $"gauss_point".
Definition _gauss_pts : ident := $"gauss_pts".
Definition _gauss_weight : ident := $"gauss_weight".
Definition _gauss_wts : ident := $"gauss_wts".
Definition _hughes_point : ident := $"hughes_point".
Definition _hughes_weight : ident := $"hughes_weight".
Definition _i : ident := $"i".
Definition _ix : ident := $"ix".
Definition _iy : ident := $"iy".
Definition _main : ident := $"main".
Definition _npts : ident := $"npts".
Definition _xi : ident := $"xi".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 42);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stderrp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_gauss_point := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: (_npts, tint) :: nil);
  fn_vars := ((_gauss_pts, (tarray tdouble 55)) :: nil);
  fn_temps := ((_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
        (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
    (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
          (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
      (Eunop Oneg
        (Econst_float (Float.of_bits (Int64.repr 4603375528459645726)) tdouble)
        tdouble))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
            (Econst_int (Int.repr 2) tint) (tptr tdouble)) tdouble)
        (Econst_float (Float.of_bits (Int64.repr 4603375528459645726)) tdouble))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
              (Econst_int (Int.repr 3) tint) (tptr tdouble)) tdouble)
          (Eunop Oneg
            (Econst_float (Float.of_bits (Int64.repr 4605152166087193156)) tdouble)
            tdouble))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                (Econst_int (Int.repr 4) tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                  (Econst_int (Int.repr 5) tint) (tptr tdouble)) tdouble)
              (Econst_float (Float.of_bits (Int64.repr 4605152166087193156)) tdouble))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                    (Econst_int (Int.repr 6) tint) (tptr tdouble)) tdouble)
                (Eunop Oneg
                  (Econst_float (Float.of_bits (Int64.repr 4605931645889296777)) tdouble)
                  tdouble))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                      (Econst_int (Int.repr 7) tint) (tptr tdouble)) tdouble)
                  (Eunop Oneg
                    (Econst_float (Float.of_bits (Int64.repr 4599796173922713079)) tdouble)
                    tdouble))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                        (Econst_int (Int.repr 8) tint) (tptr tdouble))
                      tdouble)
                    (Econst_float (Float.of_bits (Int64.repr 4599796173922713079)) tdouble))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                          (Econst_int (Int.repr 9) tint) (tptr tdouble))
                        tdouble)
                      (Econst_float (Float.of_bits (Int64.repr 4605931645889296777)) tdouble))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _gauss_pts (tarray tdouble 55))
                            (Econst_int (Int.repr 10) tint) (tptr tdouble))
                          tdouble)
                        (Eunop Oneg
                          (Econst_float (Float.of_bits (Int64.repr 4606337361978276457)) tdouble)
                          tdouble))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Evar _gauss_pts (tarray tdouble 55))
                              (Econst_int (Int.repr 11) tint) (tptr tdouble))
                            tdouble)
                          (Eunop Oneg
                            (Econst_float (Float.of_bits (Int64.repr 4603025319913961220)) tdouble)
                            tdouble))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Evar _gauss_pts (tarray tdouble 55))
                                (Econst_int (Int.repr 12) tint)
                                (tptr tdouble)) tdouble)
                            (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _gauss_pts (tarray tdouble 55))
                                  (Econst_int (Int.repr 13) tint)
                                  (tptr tdouble)) tdouble)
                              (Econst_float (Float.of_bits (Int64.repr 4603025319913961220)) tdouble))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _gauss_pts (tarray tdouble 55))
                                    (Econst_int (Int.repr 14) tint)
                                    (tptr tdouble)) tdouble)
                                (Econst_float (Float.of_bits (Int64.repr 4606337361978276457)) tdouble))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _gauss_pts (tarray tdouble 55))
                                      (Econst_int (Int.repr 15) tint)
                                      (tptr tdouble)) tdouble)
                                  (Eunop Oneg
                                    (Econst_float (Float.of_bits (Int64.repr 4606574158258675742)) tdouble)
                                    tdouble))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _gauss_pts (tarray tdouble 55))
                                        (Econst_int (Int.repr 16) tint)
                                        (tptr tdouble)) tdouble)
                                    (Eunop Oneg
                                      (Econst_float (Float.of_bits (Int64.repr 4604130864238283107)) tdouble)
                                      tdouble))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _gauss_pts (tarray tdouble 55))
                                          (Econst_int (Int.repr 17) tint)
                                          (tptr tdouble)) tdouble)
                                      (Eunop Oneg
                                        (Econst_float (Float.of_bits (Int64.repr 4597765182510757320)) tdouble)
                                        tdouble))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _gauss_pts (tarray tdouble 55))
                                            (Econst_int (Int.repr 18) tint)
                                            (tptr tdouble)) tdouble)
                                        (Econst_float (Float.of_bits (Int64.repr 4597765182510757320)) tdouble))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _gauss_pts (tarray tdouble 55))
                                              (Econst_int (Int.repr 19) tint)
                                              (tptr tdouble)) tdouble)
                                          (Econst_float (Float.of_bits (Int64.repr 4604130864238283107)) tdouble))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _gauss_pts (tarray tdouble 55))
                                                (Econst_int (Int.repr 20) tint)
                                                (tptr tdouble)) tdouble)
                                            (Econst_float (Float.of_bits (Int64.repr 4606574158258675742)) tdouble))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _gauss_pts (tarray tdouble 55))
                                                  (Econst_int (Int.repr 21) tint)
                                                  (tptr tdouble)) tdouble)
                                              (Eunop Oneg
                                                (Econst_float (Float.of_bits (Int64.repr 4606724023625998894)) tdouble)
                                                tdouble))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                    (Econst_int (Int.repr 22) tint)
                                                    (tptr tdouble)) tdouble)
                                                (Eunop Oneg
                                                  (Econst_float (Float.of_bits (Int64.repr 4604854338687574482)) tdouble)
                                                  tdouble))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _gauss_pts (tarray tdouble 55))
                                                      (Econst_int (Int.repr 23) tint)
                                                      (tptr tdouble))
                                                    tdouble)
                                                  (Eunop Oneg
                                                    (Econst_float (Float.of_bits (Int64.repr 4600982676207959391)) tdouble)
                                                    tdouble))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _gauss_pts (tarray tdouble 55))
                                                        (Econst_int (Int.repr 24) tint)
                                                        (tptr tdouble))
                                                      tdouble)
                                                    (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _gauss_pts (tarray tdouble 55))
                                                          (Econst_int (Int.repr 25) tint)
                                                          (tptr tdouble))
                                                        tdouble)
                                                      (Econst_float (Float.of_bits (Int64.repr 4600982676207959391)) tdouble))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _gauss_pts (tarray tdouble 55))
                                                            (Econst_int (Int.repr 26) tint)
                                                            (tptr tdouble))
                                                          tdouble)
                                                        (Econst_float (Float.of_bits (Int64.repr 4604854338687574482)) tdouble))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _gauss_pts (tarray tdouble 55))
                                                              (Econst_int (Int.repr 27) tint)
                                                              (tptr tdouble))
                                                            tdouble)
                                                          (Econst_float (Float.of_bits (Int64.repr 4606724023625998894)) tdouble))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _gauss_pts (tarray tdouble 55))
                                                                (Econst_int (Int.repr 28) tint)
                                                                (tptr tdouble))
                                                              tdouble)
                                                            (Eunop Oneg
                                                              (Econst_float (Float.of_bits (Int64.repr 4606824741625056356)) tdouble)
                                                              tdouble))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _gauss_pts (tarray tdouble 55))
                                                                  (Econst_int (Int.repr 29) tint)
                                                                  (tptr tdouble))
                                                                tdouble)
                                                              (Eunop Oneg
                                                                (Econst_float (Float.of_bits (Int64.repr 4605350953246913568)) tdouble)
                                                                tdouble))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    (tptr tdouble))
                                                                  tdouble)
                                                                (Eunop Oneg
                                                                  (Econst_float (Float.of_bits (Int64.repr 4602908794676217012)) tdouble)
                                                                  tdouble))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                  (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4595776949791257420)) tdouble)
                                                                    tdouble))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4595776949791257420)) tdouble))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 33) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4602908794676217012)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 34) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4605350953246913568)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 35) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4606824741625056356)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4606895631733039365)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 37) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4605705518312129178)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 38) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4603699978256776585)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 39) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599512850305165928)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 40) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 41) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599512850305165928)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 42) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4603699978256776585)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 43) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4605705518312129178)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 44) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4606895631733039365)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 45) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4606947389703123674)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 46) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4605967017657021175)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 47) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4604294796902523284)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 48) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4601478977259924184)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 49) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Eunop Oneg
                                                                    (Econst_float (Float.of_bits (Int64.repr 4594531783631037042)) tdouble)
                                                                    tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 50) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4594531783631037042)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 51) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4601478977259924184)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 52) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4604294796902523284)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 53) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4605967017657021175)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4606947389703123674)) tdouble))
                                                                    (Ssequence
                                                                    (Sset _t'1
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_pts (tarray tdouble 55))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Etempvar _npts tint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _npts tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Etempvar _i tint)
                                                                    tint)
                                                                    (tptr tdouble))
                                                                    tdouble))
                                                                    (Sreturn (Some (Etempvar _t'1 tdouble)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_gauss_weight := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: (_npts, tint) :: nil);
  fn_vars := ((_gauss_wts, (tarray tdouble 55)) :: nil);
  fn_temps := ((_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
        (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
    (Econst_float (Float.of_bits (Int64.repr 4611686018427387904)) tdouble))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
          (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
      (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
            (Econst_int (Int.repr 2) tint) (tptr tdouble)) tdouble)
        (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
              (Econst_int (Int.repr 3) tint) (tptr tdouble)) tdouble)
          (Econst_float (Float.of_bits (Int64.repr 4603179219131243638)) tdouble))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                (Econst_int (Int.repr 4) tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 4606181618882823965)) tdouble))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                  (Econst_int (Int.repr 5) tint) (tptr tdouble)) tdouble)
              (Econst_float (Float.of_bits (Int64.repr 4603179219131243638)) tdouble))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                    (Econst_int (Int.repr 6) tint) (tptr tdouble)) tdouble)
                (Econst_float (Float.of_bits (Int64.repr 4599938015721666158)) tdouble))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                      (Econst_int (Int.repr 7) tint) (tptr tdouble)) tdouble)
                  (Econst_float (Float.of_bits (Int64.repr 4604049220898137289)) tdouble))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                        (Econst_int (Int.repr 8) tint) (tptr tdouble))
                      tdouble)
                    (Econst_float (Float.of_bits (Int64.repr 4604049220898137289)) tdouble))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                          (Econst_int (Int.repr 9) tint) (tptr tdouble))
                        tdouble)
                      (Econst_float (Float.of_bits (Int64.repr 4599938015721666158)) tdouble))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _gauss_wts (tarray tdouble 55))
                            (Econst_int (Int.repr 10) tint) (tptr tdouble))
                          tdouble)
                        (Econst_float (Float.of_bits (Int64.repr 4597704210940560265)) tdouble))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Evar _gauss_wts (tarray tdouble 55))
                              (Econst_int (Int.repr 11) tint) (tptr tdouble))
                            tdouble)
                          (Econst_float (Float.of_bits (Int64.repr 4602293827526345043)) tdouble))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Evar _gauss_wts (tarray tdouble 55))
                                (Econst_int (Int.repr 12) tint)
                                (tptr tdouble)) tdouble)
                            (Econst_float (Float.of_bits (Int64.repr 4603299315121306848)) tdouble))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _gauss_wts (tarray tdouble 55))
                                  (Econst_int (Int.repr 13) tint)
                                  (tptr tdouble)) tdouble)
                              (Econst_float (Float.of_bits (Int64.repr 4602293827526345043)) tdouble))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _gauss_wts (tarray tdouble 55))
                                    (Econst_int (Int.repr 14) tint)
                                    (tptr tdouble)) tdouble)
                                (Econst_float (Float.of_bits (Int64.repr 4597704210940560265)) tdouble))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _gauss_wts (tarray tdouble 55))
                                      (Econst_int (Int.repr 15) tint)
                                      (tptr tdouble)) tdouble)
                                  (Econst_float (Float.of_bits (Int64.repr 4595340635650841579)) tdouble))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _gauss_wts (tarray tdouble 55))
                                        (Econst_int (Int.repr 16) tint)
                                        (tptr tdouble)) tdouble)
                                    (Econst_float (Float.of_bits (Int64.repr 4600170522661702691)) tdouble))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _gauss_wts (tarray tdouble 55))
                                          (Econst_int (Int.repr 17) tint)
                                          (tptr tdouble)) tdouble)
                                      (Econst_float (Float.of_bits (Int64.repr 4602100808003438055)) tdouble))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _gauss_wts (tarray tdouble 55))
                                            (Econst_int (Int.repr 18) tint)
                                            (tptr tdouble)) tdouble)
                                        (Econst_float (Float.of_bits (Int64.repr 4602100808003438055)) tdouble))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _gauss_wts (tarray tdouble 55))
                                              (Econst_int (Int.repr 19) tint)
                                              (tptr tdouble)) tdouble)
                                          (Econst_float (Float.of_bits (Int64.repr 4600170522661702691)) tdouble))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _gauss_wts (tarray tdouble 55))
                                                (Econst_int (Int.repr 20) tint)
                                                (tptr tdouble)) tdouble)
                                            (Econst_float (Float.of_bits (Int64.repr 4595340635650841579)) tdouble))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _gauss_wts (tarray tdouble 55))
                                                  (Econst_int (Int.repr 21) tint)
                                                  (tptr tdouble)) tdouble)
                                              (Econst_float (Float.of_bits (Int64.repr 4593833207853641058)) tdouble))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                    (Econst_int (Int.repr 22) tint)
                                                    (tptr tdouble)) tdouble)
                                                (Econst_float (Float.of_bits (Int64.repr 4598710344305444426)) tdouble))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _gauss_wts (tarray tdouble 55))
                                                      (Econst_int (Int.repr 23) tint)
                                                      (tptr tdouble))
                                                    tdouble)
                                                  (Econst_float (Float.of_bits (Int64.repr 4600550058610600766)) tdouble))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _gauss_wts (tarray tdouble 55))
                                                        (Econst_int (Int.repr 24) tint)
                                                        (tptr tdouble))
                                                      tdouble)
                                                    (Econst_float (Float.of_bits (Int64.repr 4601200903213297567)) tdouble))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _gauss_wts (tarray tdouble 55))
                                                          (Econst_int (Int.repr 25) tint)
                                                          (tptr tdouble))
                                                        tdouble)
                                                      (Econst_float (Float.of_bits (Int64.repr 4600550058610600766)) tdouble))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _gauss_wts (tarray tdouble 55))
                                                            (Econst_int (Int.repr 26) tint)
                                                            (tptr tdouble))
                                                          tdouble)
                                                        (Econst_float (Float.of_bits (Int64.repr 4598710344305444426)) tdouble))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _gauss_wts (tarray tdouble 55))
                                                              (Econst_int (Int.repr 27) tint)
                                                              (tptr tdouble))
                                                            tdouble)
                                                          (Econst_float (Float.of_bits (Int64.repr 4593833207853641058)) tdouble))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _gauss_wts (tarray tdouble 55))
                                                                (Econst_int (Int.repr 28) tint)
                                                                (tptr tdouble))
                                                              tdouble)
                                                            (Econst_float (Float.of_bits (Int64.repr 4591958705436230497)) tdouble))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _gauss_wts (tarray tdouble 55))
                                                                  (Econst_int (Int.repr 29) tint)
                                                                  (tptr tdouble))
                                                                tdouble)
                                                              (Econst_float (Float.of_bits (Int64.repr 4597180141441723269)) tdouble))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    (tptr tdouble))
                                                                  tdouble)
                                                                (Econst_float (Float.of_bits (Int64.repr 4599322856451823120)) tdouble))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                  (Econst_float (Float.of_bits (Int64.repr 4600205150124610371)) tdouble))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4600205150124610371)) tdouble))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 33) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599322856451823120)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 34) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4597180141441723269)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 35) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4591958705436230497)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4590520857545404122)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 37) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4595676556204059612)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 38) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598366364858742014)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 39) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599298364636976404)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 40) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599620683262412910)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 41) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4599298364636976404)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 42) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598366364858742014)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 43) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4595676556204059612)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 44) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4590520857545404122)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 45) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4589468597325323285)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 46) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4594552572613292020)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 47) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4597061438375246896)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 48) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598522297904897016)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 49) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598995311071123185)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 50) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598995311071123185)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 51) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4598522297904897016)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 52) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4597061438375246896)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 53) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4594552572613292020)) tdouble))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    (tptr tdouble))
                                                                    tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4589468597325323285)) tdouble))
                                                                    (Ssequence
                                                                    (Sset _t'1
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _gauss_wts (tarray tdouble 55))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Etempvar _npts tint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _npts tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Etempvar _i tint)
                                                                    tint)
                                                                    (tptr tdouble))
                                                                    tdouble))
                                                                    (Sreturn (Some (Etempvar _t'1 tdouble)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_gauss2d_npoint1d := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_npts, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Sswitch (Etempvar _npts tint)
  (LScons (Some 1)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 4)
      (Sreturn (Some (Econst_int (Int.repr 2) tint)))
      (LScons (Some 9)
        (Sreturn (Some (Econst_int (Int.repr 3) tint)))
        (LScons (Some 16)
          (Sreturn (Some (Econst_int (Int.repr 4) tint)))
          (LScons (Some 25)
            (Sreturn (Some (Econst_int (Int.repr 5) tint)))
            (LScons None
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
                  (Scall None
                    (Evar _fprintf (Tfunction
                                     ((tptr (Tstruct ___sFILE noattr)) ::
                                      (tptr tschar) :: nil) tint
                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                    ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
                     (Evar ___stringlit_1 (tarray tschar 42)) ::
                     (Etempvar _npts tint) :: nil)))
                (Scall None
                  (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
                  ((Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil)))
              LSnil)))))))
|}.

Definition f_gauss2d_point := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_xi, (tptr tdouble)) :: (_i, tint) :: (_npts, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: (_ix, tint) :: (_iy, tint) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _gauss2d_npoint1d (Tfunction (tint :: nil) tint cc_default))
      ((Etempvar _npts tint) :: nil))
    (Sset _d (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _ix (Ebinop Omod (Etempvar _i tint) (Etempvar _d tint) tint))
    (Ssequence
      (Sset _iy (Ebinop Odiv (Etempvar _i tint) (Etempvar _d tint) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _gauss_point (Tfunction (tint :: tint :: nil) tdouble
                                 cc_default))
            ((Etempvar _ix tint) :: (Etempvar _d tint) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _xi (tptr tdouble))
                (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
            (Etempvar _t'2 tdouble)))
        (Ssequence
          (Scall (Some _t'3)
            (Evar _gauss_point (Tfunction (tint :: tint :: nil) tdouble
                                 cc_default))
            ((Etempvar _iy tint) :: (Etempvar _d tint) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _xi (tptr tdouble))
                (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
            (Etempvar _t'3 tdouble)))))))
|}.

Definition f_gauss2d_weight := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: (_npts, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: (_ix, tint) :: (_iy, tint) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _gauss2d_npoint1d (Tfunction (tint :: nil) tint cc_default))
      ((Etempvar _npts tint) :: nil))
    (Sset _d (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _ix (Ebinop Omod (Etempvar _i tint) (Etempvar _d tint) tint))
    (Ssequence
      (Sset _iy (Ebinop Odiv (Etempvar _i tint) (Etempvar _d tint) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _gauss_weight (Tfunction (tint :: tint :: nil) tdouble
                                  cc_default))
            ((Etempvar _ix tint) :: (Etempvar _d tint) :: nil))
          (Scall (Some _t'3)
            (Evar _gauss_weight (Tfunction (tint :: tint :: nil) tdouble
                                  cc_default))
            ((Etempvar _iy tint) :: (Etempvar _d tint) :: nil)))
        (Sreturn (Some (Ebinop Omul (Etempvar _t'2 tdouble)
                         (Etempvar _t'3 tdouble) tdouble)))))))
|}.

Definition f_hughes_point := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_xi, (tptr tdouble)) :: (_i, tint) :: (_npts, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Sswitch (Etempvar _i tint)
  (LScons (Some 0)
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _xi (tptr tdouble))
            (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
        (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _xi (tptr tdouble))
              (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
          (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
        (Sreturn None)))
    (LScons (Some 1)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _xi (tptr tdouble))
              (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
          (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _xi (tptr tdouble))
                (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble))
          (Sreturn None)))
      (LScons (Some 2)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _xi (tptr tdouble))
                (Econst_int (Int.repr 0) tint) (tptr tdouble)) tdouble)
            (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _xi (tptr tdouble))
                  (Econst_int (Int.repr 1) tint) (tptr tdouble)) tdouble)
              (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble))
            (Sreturn None)))
        (LScons None
          (Ssequence
            (Ssequence
              (Sset _t'1 (Evar ___stderrp (tptr (Tstruct ___sFILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 ((tptr (Tstruct ___sFILE noattr)) ::
                                  (tptr tschar) :: nil) tint
                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'1 (tptr (Tstruct ___sFILE noattr))) ::
                 (Evar ___stringlit_2 (tarray tschar 37)) :: nil)))
            (Scall None
              (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
              ((Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil)))
          LSnil)))))
|}.

Definition f_hughes_weight := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: (_npts, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Odiv
                 (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                 (Econst_float (Float.of_bits (Int64.repr 4618441417868443648)) tdouble)
                 tdouble)))
|}.

Definition composites : list composite_definition :=
(Composite ___sbuf Struct
   (Member_plain __base (tptr tuchar) :: Member_plain __size tint :: nil)
   noattr ::
 Composite ___sFILE Struct
   (Member_plain __p (tptr tuchar) :: Member_plain __r tint ::
    Member_plain __w tint :: Member_plain __flags tshort ::
    Member_plain __file tshort ::
    Member_plain __bf (Tstruct ___sbuf noattr) ::
    Member_plain __lbfsize tint :: Member_plain __cookie (tptr tvoid) ::
    Member_plain __close
      (tptr (Tfunction ((tptr tvoid) :: nil) tint cc_default)) ::
    Member_plain __read
      (tptr (Tfunction ((tptr tvoid) :: (tptr tschar) :: tint :: nil) tint
              cc_default)) ::
    Member_plain __seek
      (tptr (Tfunction ((tptr tvoid) :: tlong :: tint :: nil) tlong
              cc_default)) ::
    Member_plain __write
      (tptr (Tfunction ((tptr tvoid) :: (tptr tschar) :: tint :: nil) tint
              cc_default)) :: Member_plain __ub (Tstruct ___sbuf noattr) ::
    Member_plain __extra (tptr (Tstruct ___sFILEX noattr)) ::
    Member_plain __ur tint :: Member_plain __ubuf (tarray tuchar 3) ::
    Member_plain __nbuf (tarray tuchar 1) ::
    Member_plain __lb (Tstruct ___sbuf noattr) ::
    Member_plain __blksize tint :: Member_plain __offset tlong :: nil)
   noattr :: nil).

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
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
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
 (___stderrp, Gvar v___stderrp) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     ((tptr (Tstruct ___sFILE noattr)) :: (tptr tschar) :: nil) tint
     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_gauss_point, Gfun(Internal f_gauss_point)) ::
 (_gauss_weight, Gfun(Internal f_gauss_weight)) ::
 (_gauss2d_npoint1d, Gfun(Internal f_gauss2d_npoint1d)) ::
 (_gauss2d_point, Gfun(Internal f_gauss2d_point)) ::
 (_gauss2d_weight, Gfun(Internal f_gauss2d_weight)) ::
 (_hughes_point, Gfun(Internal f_hughes_point)) ::
 (_hughes_weight, Gfun(Internal f_hughes_weight)) :: nil).

Definition public_idents : list ident :=
(_hughes_weight :: _hughes_point :: _gauss2d_weight :: _gauss2d_point ::
 _gauss2d_npoint1d :: _gauss_weight :: _gauss_point :: _exit :: _fprintf ::
 ___stderrp :: ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
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


