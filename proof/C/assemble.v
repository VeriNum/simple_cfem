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
  Definition source_file := "../src/assemble.c".
  Definition normalized := true.
End Info.

Definition _A : ident := $"A".
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
Definition _add : ident := $"add".
Definition _assemble_add : ident := $"assemble_add".
Definition _assemble_clear : ident := $"assemble_clear".
Definition _assemble_data_t : ident := $"assemble_data_t".
Definition _assemble_norm : ident := $"assemble_norm".
Definition _assemble_norm2 : ident := $"assemble_norm2".
Definition _assemble_print : ident := $"assemble_print".
Definition _assemble_t : ident := $"assemble_t".
Definition _assembler : ident := $"assembler".
Definition _b : ident := $"b".
Definition _bandmat_addto : ident := $"bandmat_addto".
Definition _bandmat_clear : ident := $"bandmat_clear".
Definition _bandmat_norm2 : ident := $"bandmat_norm2".
Definition _bandmat_print : ident := $"bandmat_print".
Definition _bandmat_t : ident := $"bandmat_t".
Definition _casted_bandmat_add : ident := $"casted_bandmat_add".
Definition _casted_bandmat_clear : ident := $"casted_bandmat_clear".
Definition _casted_bandmat_norm2 : ident := $"casted_bandmat_norm2".
Definition _casted_bandmat_print : ident := $"casted_bandmat_print".
Definition _casted_densemat_add : ident := $"casted_densemat_add".
Definition _casted_densemat_clear : ident := $"casted_densemat_clear".
Definition _casted_densemat_norm2 : ident := $"casted_densemat_norm2".
Definition _casted_densemat_print : ident := $"casted_densemat_print".
Definition _clear : ident := $"clear".
Definition _data : ident := $"data".
Definition _densemat_addto : ident := $"densemat_addto".
Definition _densemat_clear : ident := $"densemat_clear".
Definition _densemat_norm2 : ident := $"densemat_norm2".
Definition _densemat_print : ident := $"densemat_print".
Definition _densemat_t : ident := $"densemat_t".
Definition _i : ident := $"i".
Definition _init_assemble_band : ident := $"init_assemble_band".
Definition _init_assemble_dense : ident := $"init_assemble_dense".
Definition _j : ident := $"j".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _norm2 : ident := $"norm2".
Definition _p : ident := $"p".
Definition _print : ident := $"print".
Definition _sqrt : ident := $"sqrt".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_assemble_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) ::
                (_i, tint) :: (_j, tint) :: (_x, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _assemble_data_t noattr))) ::
               (_t'1,
                (tptr (Tfunction
                        ((tptr (Tstruct _assemble_data_t noattr)) :: tint ::
                         tint :: tdouble :: nil) tvoid cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
        (Tstruct _assemble_t noattr)) _add
      (tptr (Tfunction
              ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
               tdouble :: nil) tvoid cc_default))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _p
        (tptr (Tstruct _assemble_data_t noattr))))
    (Scall None
      (Ederef
        (Etempvar _t'1 (tptr (Tfunction
                               ((tptr (Tstruct _assemble_data_t noattr)) ::
                                tint :: tint :: tdouble :: nil) tvoid
                               cc_default)))
        (Tfunction
          ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
           tdouble :: nil) tvoid cc_default))
      ((Etempvar _t'2 (tptr (Tstruct _assemble_data_t noattr))) ::
       (Etempvar _i tint) :: (Etempvar _j tint) :: (Etempvar _x tdouble) ::
       nil))))
|}.

Definition f_assemble_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _assemble_data_t noattr))) ::
               (_t'1,
                (tptr (Tfunction
                        ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                        tvoid cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
        (Tstruct _assemble_t noattr)) _clear
      (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
              tvoid cc_default))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _p
        (tptr (Tstruct _assemble_data_t noattr))))
    (Scall None
      (Ederef
        (Etempvar _t'1 (tptr (Tfunction
                               ((tptr (Tstruct _assemble_data_t noattr)) ::
                                nil) tvoid cc_default)))
        (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tvoid
          cc_default))
      ((Etempvar _t'2 (tptr (Tstruct _assemble_data_t noattr))) :: nil))))
|}.

Definition f_assemble_norm2 := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tdouble) ::
               (_t'3, (tptr (Tstruct _assemble_data_t noattr))) ::
               (_t'2,
                (tptr (Tfunction
                        ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                        tdouble cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _norm2
        (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                tdouble cc_default))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
            (Tstruct _assemble_t noattr)) _p
          (tptr (Tstruct _assemble_data_t noattr))))
      (Scall (Some _t'1)
        (Ederef
          (Etempvar _t'2 (tptr (Tfunction
                                 ((tptr (Tstruct _assemble_data_t noattr)) ::
                                  nil) tdouble cc_default)))
          (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
            tdouble cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _assemble_data_t noattr))) :: nil))))
  (Sreturn (Some (Etempvar _t'1 tdouble))))
|}.

Definition f_assemble_norm := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _assemble_norm2 (Tfunction
                              ((tptr (Tstruct _assemble_t noattr)) :: nil)
                              tdouble cc_default))
      ((Etempvar _assembler (tptr (Tstruct _assemble_t noattr))) :: nil))
    (Scall (Some _t'2)
      (Evar _sqrt (Tfunction (tdouble :: nil) tdouble cc_default))
      ((Etempvar _t'1 tdouble) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tdouble))))
|}.

Definition f_assemble_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _assemble_data_t noattr))) ::
               (_t'1,
                (tptr (Tfunction
                        ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                        tvoid cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
        (Tstruct _assemble_t noattr)) _print
      (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
              tvoid cc_default))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _p
        (tptr (Tstruct _assemble_data_t noattr))))
    (Scall None
      (Ederef
        (Etempvar _t'1 (tptr (Tfunction
                               ((tptr (Tstruct _assemble_data_t noattr)) ::
                                nil) tvoid cc_default)))
        (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tvoid
          cc_default))
      ((Etempvar _t'2 (tptr (Tstruct _assemble_data_t noattr))) :: nil))))
|}.

Definition f_casted_densemat_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) ::
                (_i, tint) :: (_j, tint) :: (_x, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _densemat_addto (Tfunction
                          ((tptr (Tstruct _densemat_t noattr)) :: tint ::
                           tint :: tdouble :: nil) tvoid cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _densemat_t noattr))) :: (Etempvar _i tint) ::
   (Etempvar _j tint) :: (Etempvar _x tdouble) :: nil))
|}.

Definition f_casted_densemat_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _densemat_clear (Tfunction
                          ((tptr (Tstruct _densemat_t noattr)) :: nil) tvoid
                          cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _densemat_t noattr))) :: nil))
|}.

Definition f_casted_densemat_norm2 := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _densemat_norm2 (Tfunction
                            ((tptr (Tstruct _densemat_t noattr)) :: nil)
                            tdouble cc_default))
    ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
       (tptr (Tstruct _densemat_t noattr))) :: nil))
  (Sreturn (Some (Etempvar _t'1 tdouble))))
|}.

Definition f_casted_densemat_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _densemat_print (Tfunction
                          ((tptr (Tstruct _densemat_t noattr)) :: nil) tvoid
                          cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _densemat_t noattr))) :: nil))
|}.

Definition f_init_assemble_dense := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) ::
                (_A, (tptr (Tstruct _densemat_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
        (Tstruct _assemble_t noattr)) _p
      (tptr (Tstruct _assemble_data_t noattr)))
    (Ecast (Etempvar _A (tptr (Tstruct _densemat_t noattr)))
      (tptr (Tstruct _assemble_data_t noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _add
        (tptr (Tfunction
                ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
                 tdouble :: nil) tvoid cc_default)))
      (Eaddrof
        (Evar _casted_densemat_add (Tfunction
                                     ((tptr (Tstruct _assemble_data_t noattr)) ::
                                      tint :: tint :: tdouble :: nil) tvoid
                                     cc_default))
        (tptr (Tfunction
                ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
                 tdouble :: nil) tvoid cc_default))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
            (Tstruct _assemble_t noattr)) _clear
          (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                  tvoid cc_default)))
        (Eaddrof
          (Evar _casted_densemat_clear (Tfunction
                                         ((tptr (Tstruct _assemble_data_t noattr)) ::
                                          nil) tvoid cc_default))
          (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                  tvoid cc_default))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
              (Tstruct _assemble_t noattr)) _norm2
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tdouble
                    cc_default)))
          (Eaddrof
            (Evar _casted_densemat_norm2 (Tfunction
                                           ((tptr (Tstruct _assemble_data_t noattr)) ::
                                            nil) tdouble cc_default))
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tdouble
                    cc_default))))
        (Sassign
          (Efield
            (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
              (Tstruct _assemble_t noattr)) _print
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tvoid
                    cc_default)))
          (Eaddrof
            (Evar _casted_densemat_print (Tfunction
                                           ((tptr (Tstruct _assemble_data_t noattr)) ::
                                            nil) tvoid cc_default))
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tvoid
                    cc_default))))))))
|}.

Definition f_casted_bandmat_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) ::
                (_i, tint) :: (_j, tint) :: (_x, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _bandmat_addto (Tfunction
                         ((tptr (Tstruct _bandmat_t noattr)) :: tint ::
                          tint :: tdouble :: nil) tvoid cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _bandmat_t noattr))) :: (Etempvar _j tint) ::
   (Ebinop Osub (Etempvar _j tint) (Etempvar _i tint) tint) ::
   (Etempvar _x tdouble) :: nil))
|}.

Definition f_casted_bandmat_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _bandmat_clear (Tfunction ((tptr (Tstruct _bandmat_t noattr)) :: nil)
                         tvoid cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _bandmat_t noattr))) :: nil))
|}.

Definition f_casted_bandmat_norm2 := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _bandmat_norm2 (Tfunction
                           ((tptr (Tstruct _bandmat_t noattr)) :: nil)
                           tdouble cc_default))
    ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
       (tptr (Tstruct _bandmat_t noattr))) :: nil))
  (Sreturn (Some (Etempvar _t'1 tdouble))))
|}.

Definition f_casted_bandmat_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _assemble_data_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _bandmat_print (Tfunction ((tptr (Tstruct _bandmat_t noattr)) :: nil)
                         tvoid cc_default))
  ((Ecast (Etempvar _p (tptr (Tstruct _assemble_data_t noattr)))
     (tptr (Tstruct _bandmat_t noattr))) :: nil))
|}.

Definition f_init_assemble_band := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_assembler, (tptr (Tstruct _assemble_t noattr))) ::
                (_b, (tptr (Tstruct _bandmat_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
        (Tstruct _assemble_t noattr)) _p
      (tptr (Tstruct _assemble_data_t noattr)))
    (Ecast (Etempvar _b (tptr (Tstruct _bandmat_t noattr)))
      (tptr (Tstruct _assemble_data_t noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
          (Tstruct _assemble_t noattr)) _add
        (tptr (Tfunction
                ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
                 tdouble :: nil) tvoid cc_default)))
      (Evar _casted_bandmat_add (Tfunction
                                  ((tptr (Tstruct _assemble_data_t noattr)) ::
                                   tint :: tint :: tdouble :: nil) tvoid
                                  cc_default)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
            (Tstruct _assemble_t noattr)) _clear
          (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
                  tvoid cc_default)))
        (Evar _casted_bandmat_clear (Tfunction
                                      ((tptr (Tstruct _assemble_data_t noattr)) ::
                                       nil) tvoid cc_default)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
              (Tstruct _assemble_t noattr)) _norm2
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tdouble
                    cc_default)))
          (Evar _casted_bandmat_norm2 (Tfunction
                                        ((tptr (Tstruct _assemble_data_t noattr)) ::
                                         nil) tdouble cc_default)))
        (Sassign
          (Efield
            (Ederef (Etempvar _assembler (tptr (Tstruct _assemble_t noattr)))
              (Tstruct _assemble_t noattr)) _print
            (tptr (Tfunction
                    ((tptr (Tstruct _assemble_data_t noattr)) :: nil) tvoid
                    cc_default)))
          (Evar _casted_bandmat_print (Tfunction
                                        ((tptr (Tstruct _assemble_data_t noattr)) ::
                                         nil) tvoid cc_default)))))))
|}.

Definition composites : list composite_definition :=
(Composite _densemat_t Struct
   (Member_plain _m tint :: Member_plain _n tint ::
    Member_plain _data (tarray tdouble 0) :: nil)
   noattr ::
 Composite _bandmat_t Struct
   (Member_plain _m tint :: Member_plain _b tint ::
    Member_plain _data (tarray tdouble 0) :: nil)
   noattr ::
 Composite _assemble_t Struct
   (Member_plain _p (tptr (Tstruct _assemble_data_t noattr)) ::
    Member_plain _add
      (tptr (Tfunction
              ((tptr (Tstruct _assemble_data_t noattr)) :: tint :: tint ::
               tdouble :: nil) tvoid cc_default)) ::
    Member_plain _clear
      (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
              tvoid cc_default)) ::
    Member_plain _norm2
      (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
              tdouble cc_default)) ::
    Member_plain _print
      (tptr (Tfunction ((tptr (Tstruct _assemble_data_t noattr)) :: nil)
              tvoid cc_default)) :: nil)
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
 (_sqrt,
   Gfun(External (EF_external "sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (_densemat_clear,
   Gfun(External (EF_external "densemat_clear"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _densemat_t noattr)) :: nil) tvoid cc_default)) ::
 (_densemat_print,
   Gfun(External (EF_external "densemat_print"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _densemat_t noattr)) :: nil) tvoid cc_default)) ::
 (_densemat_norm2,
   Gfun(External (EF_external "densemat_norm2"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr (Tstruct _densemat_t noattr)) :: nil) tdouble cc_default)) ::
 (_densemat_addto,
   Gfun(External (EF_external "densemat_addto"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xfloat :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _densemat_t noattr)) :: tint :: tint :: tdouble :: nil)
     tvoid cc_default)) ::
 (_bandmat_clear,
   Gfun(External (EF_external "bandmat_clear"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _bandmat_t noattr)) :: nil) tvoid cc_default)) ::
 (_bandmat_print,
   Gfun(External (EF_external "bandmat_print"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _bandmat_t noattr)) :: nil) tvoid cc_default)) ::
 (_bandmat_norm2,
   Gfun(External (EF_external "bandmat_norm2"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr (Tstruct _bandmat_t noattr)) :: nil) tdouble cc_default)) ::
 (_bandmat_addto,
   Gfun(External (EF_external "bandmat_addto"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xfloat :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _bandmat_t noattr)) :: tint :: tint :: tdouble :: nil)
     tvoid cc_default)) :: (_assemble_add, Gfun(Internal f_assemble_add)) ::
 (_assemble_clear, Gfun(Internal f_assemble_clear)) ::
 (_assemble_norm2, Gfun(Internal f_assemble_norm2)) ::
 (_assemble_norm, Gfun(Internal f_assemble_norm)) ::
 (_assemble_print, Gfun(Internal f_assemble_print)) ::
 (_casted_densemat_add, Gfun(Internal f_casted_densemat_add)) ::
 (_casted_densemat_clear, Gfun(Internal f_casted_densemat_clear)) ::
 (_casted_densemat_norm2, Gfun(Internal f_casted_densemat_norm2)) ::
 (_casted_densemat_print, Gfun(Internal f_casted_densemat_print)) ::
 (_init_assemble_dense, Gfun(Internal f_init_assemble_dense)) ::
 (_casted_bandmat_add, Gfun(Internal f_casted_bandmat_add)) ::
 (_casted_bandmat_clear, Gfun(Internal f_casted_bandmat_clear)) ::
 (_casted_bandmat_norm2, Gfun(Internal f_casted_bandmat_norm2)) ::
 (_casted_bandmat_print, Gfun(Internal f_casted_bandmat_print)) ::
 (_init_assemble_band, Gfun(Internal f_init_assemble_band)) :: nil).

Definition public_idents : list ident :=
(_init_assemble_band :: _casted_bandmat_print :: _casted_bandmat_norm2 ::
 _casted_bandmat_clear :: _casted_bandmat_add :: _init_assemble_dense ::
 _casted_densemat_print :: _casted_densemat_norm2 ::
 _casted_densemat_clear :: _casted_densemat_add :: _assemble_print ::
 _assemble_norm :: _assemble_norm2 :: _assemble_clear :: _assemble_add ::
 _bandmat_addto :: _bandmat_norm2 :: _bandmat_print :: _bandmat_clear ::
 _densemat_addto :: _densemat_norm2 :: _densemat_print :: _densemat_clear ::
 _sqrt :: ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
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


