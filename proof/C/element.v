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
  Definition source_file := "../src/element.c".
  Definition normalized := true.
End Info.

Definition _F : ident := $"F".
Definition _J : ident := $"J".
Definition _Ke : ident := $"Ke".
Definition _N : ident := $"N".
Definition _Re : ident := $"Re".
Definition _U : ident := $"U".
Definition _X : ident := $"X".
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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition _abort : ident := $"abort".
Definition _d : ident := $"d".
Definition _dN : ident := $"dN".
Definition _dR : ident := $"dR".
Definition _degree : ident := $"degree".
Definition _densematn_clear : ident := $"densematn_clear".
Definition _double_clear : ident := $"double_clear".
Definition _du : ident := $"du".
Definition _e : ident := $"e".
Definition _element_dR : ident := $"element_dR".
Definition _element_free : ident := $"element_free".
Definition _element_t : ident := $"element_t".
Definition _elt : ident := $"elt".
Definition _eltid : ident := $"eltid".
Definition _etype : ident := $"etype".
Definition _fe : ident := $"fe".
Definition _fem_t : ident := $"fem_t".
Definition _free : ident := $"free".
Definition _fx : ident := $"fx".
Definition _gauss2d_point : ident := $"gauss2d_point".
Definition _gauss2d_weight : ident := $"gauss2d_weight".
Definition _gauss_point : ident := $"gauss_point".
Definition _gauss_weight : ident := $"gauss_weight".
Definition _get_quad2d : ident := $"get_quad2d".
Definition _hughes_point : ident := $"hughes_point".
Definition _hughes_weight : ident := $"hughes_weight".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _id : ident := $"id".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _k : ident := $"k".
Definition _le : ident := $"le".
Definition _main : ident := $"main".
Definition _malloc_poisson1d_element : ident := $"malloc_poisson1d_element".
Definition _malloc_poisson2d_element : ident := $"malloc_poisson2d_element".
Definition _mesh : ident := $"mesh".
Definition _mesh_shapes : ident := $"mesh_shapes".
Definition _mesh_t : ident := $"mesh_t".
Definition _nactive : ident := $"nactive".
Definition _ndof : ident := $"ndof".
Definition _nen : ident := $"nen".
Definition _nquad : ident := $"nquad".
Definition _numelt : ident := $"numelt".
Definition _numnp : ident := $"numnp".
Definition _p : ident := $"p".
Definition _poisson1d_elt_dR : ident := $"poisson1d_elt_dR".
Definition _poisson2d_elt_dR : ident := $"poisson2d_elt_dR".
Definition _poisson_elt_t : ident := $"poisson_elt_t".
Definition _printf : ident := $"printf".
Definition _quad_pt : ident := $"quad_pt".
Definition _quad_wt : ident := $"quad_wt".
Definition _shape : ident := $"shape".
Definition _shapefn : ident := $"shapefn".
Definition _shapes2dP1 : ident := $"shapes2dP1".
Definition _shapes2dP2 : ident := $"shapes2dP2".
Definition _shapes2dS2 : ident := $"shapes2dS2".
Definition _shapes2dT1 : ident := $"shapes2dT1".
Definition _simple_elt_free : ident := $"simple_elt_free".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _wt : ident := $"wt".
Definition _x : ident := $"x".
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
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_element_dR := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_e, (tptr (Tstruct _element_t noattr))) ::
                (_fe, (tptr (Tstruct _fem_t noattr))) :: (_eltid, tint) ::
                (_Re, (tptr tdouble)) :: (_Ke, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tvoid)) ::
               (_t'1,
                (tptr (Tfunction
                        ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) ::
                         tint :: (tptr tdouble) :: (tptr tdouble) :: nil)
                        tvoid cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _e (tptr (Tstruct _element_t noattr)))
        (Tstruct _element_t noattr)) _dR
      (tptr (Tfunction
              ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) :: tint ::
               (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _e (tptr (Tstruct _element_t noattr)))
          (Tstruct _element_t noattr)) _p (tptr tvoid)))
    (Scall None
      (Ederef
        (Etempvar _t'1 (tptr (Tfunction
                               ((tptr tvoid) ::
                                (tptr (Tstruct _fem_t noattr)) :: tint ::
                                (tptr tdouble) :: (tptr tdouble) :: nil)
                               tvoid cc_default)))
        (Tfunction
          ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) :: tint ::
           (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default))
      ((Etempvar _t'2 (tptr tvoid)) ::
       (Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
       (Etempvar _eltid tint) :: (Etempvar _Re (tptr tdouble)) ::
       (Etempvar _Ke (tptr tdouble)) :: nil))))
|}.

Definition f_element_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_e, (tptr (Tstruct _element_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tvoid)) ::
               (_t'1,
                (tptr (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _e (tptr (Tstruct _element_t noattr)))
        (Tstruct _element_t noattr)) _free
      (tptr (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _e (tptr (Tstruct _element_t noattr)))
          (Tstruct _element_t noattr)) _p (tptr tvoid)))
    (Scall None
      (Ederef
        (Etempvar _t'1 (tptr (Tfunction ((tptr tvoid) :: nil) tvoid
                               cc_default)))
        (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _t'2 (tptr tvoid)) :: nil))))
|}.

Definition f_malloc_poisson1d_element := {|
  fn_return := (tptr (Tstruct _element_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_le, (tptr (Tstruct _poisson_elt_t noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _poisson_elt_t noattr) tulong) :: nil))
    (Sset _le
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _poisson_elt_t noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
            (Tstruct _poisson_elt_t noattr)) _e (Tstruct _element_t noattr))
        _p (tptr tvoid))
      (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Efield
            (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
              (Tstruct _poisson_elt_t noattr)) _e
            (Tstruct _element_t noattr)) _dR
          (tptr (Tfunction
                  ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) :: tint ::
                   (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default)))
        (Evar _poisson1d_elt_dR (Tfunction
                                  ((tptr tvoid) ::
                                   (tptr (Tstruct _fem_t noattr)) :: tint ::
                                   (tptr tdouble) :: (tptr tdouble) :: nil)
                                  tvoid cc_default)))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
                (Tstruct _poisson_elt_t noattr)) _e
              (Tstruct _element_t noattr)) _free
            (tptr (Tfunction ((tptr tvoid) :: nil) tvoid cc_default)))
          (Evar _simple_elt_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                   cc_default)))
        (Sreturn (Some (Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
                             (Tstruct _poisson_elt_t noattr)) _e
                           (Tstruct _element_t noattr))
                         (tptr (Tstruct _element_t noattr)))))))))
|}.

Definition f_malloc_poisson2d_element := {|
  fn_return := (tptr (Tstruct _element_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_le, (tptr (Tstruct _poisson_elt_t noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _poisson_elt_t noattr) tulong) :: nil))
    (Sset _le
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _poisson_elt_t noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
            (Tstruct _poisson_elt_t noattr)) _e (Tstruct _element_t noattr))
        _p (tptr tvoid))
      (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Efield
            (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
              (Tstruct _poisson_elt_t noattr)) _e
            (Tstruct _element_t noattr)) _dR
          (tptr (Tfunction
                  ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) :: tint ::
                   (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default)))
        (Evar _poisson2d_elt_dR (Tfunction
                                  ((tptr tvoid) ::
                                   (tptr (Tstruct _fem_t noattr)) :: tint ::
                                   (tptr tdouble) :: (tptr tdouble) :: nil)
                                  tvoid cc_default)))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
                (Tstruct _poisson_elt_t noattr)) _e
              (Tstruct _element_t noattr)) _free
            (tptr (Tfunction ((tptr tvoid) :: nil) tvoid cc_default)))
          (Evar _simple_elt_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                   cc_default)))
        (Sreturn (Some (Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _le (tptr (Tstruct _poisson_elt_t noattr)))
                             (Tstruct _poisson_elt_t noattr)) _e
                           (Tstruct _element_t noattr))
                         (tptr (Tstruct _element_t noattr)))))))))
|}.

Definition f_simple_elt_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
  ((Etempvar _p (tptr tvoid)) :: nil))
|}.

Definition f_poisson1d_elt_dR := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) ::
                (_fe, (tptr (Tstruct _fem_t noattr))) :: (_eltid, tint) ::
                (_Re, (tptr tdouble)) :: (_Ke, (tptr tdouble)) :: nil);
  fn_vars := ((_N, (tarray tdouble 4)) :: (_dN, (tarray tdouble 4)) ::
              (_x, tdouble) :: nil);
  fn_temps := ((_nen, tint) :: (_ndof, tint) :: (_degree, tint) ::
               (_nquad, tint) :: (_elt, (tptr tint)) :: (_k, tint) ::
               (_wt, tdouble) :: (_du, tdouble) :: (_fx, tdouble) ::
               (_U, (tptr tdouble)) :: (_F, (tptr tdouble)) :: (_j, tint) ::
               (_i, tint) :: (_j__1, tint) :: (_i__1, tint) ::
               (_t'3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) ::
               (_t'19, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'18, (tptr tint)) ::
               (_t'17, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'16, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'15, tdouble) :: (_t'14, tint) :: (_t'13, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tint) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'19
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
    (Sset _nen
      (Efield
        (Ederef (Etempvar _t'19 (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _nen tint)))
  (Ssequence
    (Sset _ndof
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _ndof tint))
    (Ssequence
      (Sset _degree
        (Ebinop Osub (Etempvar _nen tint) (Econst_int (Int.repr 1) tint)
          tint))
      (Ssequence
        (Sset _nquad (Etempvar _degree tint))
        (Ssequence
          (Ssequence
            (Sset _t'17
              (Efield
                (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                  (Tstruct _fem_t noattr)) _mesh
                (tptr (Tstruct _mesh_t noattr))))
            (Ssequence
              (Sset _t'18
                (Efield
                  (Ederef (Etempvar _t'17 (tptr (Tstruct _mesh_t noattr)))
                    (Tstruct _mesh_t noattr)) _elt (tptr tint)))
              (Sset _elt
                (Ebinop Oadd (Etempvar _t'18 (tptr tint))
                  (Ebinop Omul (Etempvar _eltid tint) (Etempvar _nen tint)
                    tint) (tptr tint)))))
          (Ssequence
            (Sifthenelse (Etempvar _Re (tptr tdouble))
              (Scall None
                (Evar _double_clear (Tfunction
                                      ((tptr tdouble) :: tint :: nil) tvoid
                                      cc_default))
                ((Etempvar _Re (tptr tdouble)) :: (Etempvar _nen tint) ::
                 nil))
              Sskip)
            (Ssequence
              (Sifthenelse (Etempvar _Ke (tptr tdouble))
                (Scall None
                  (Evar _densematn_clear (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            nil) tvoid cc_default))
                  ((Etempvar _Ke (tptr tdouble)) :: (Etempvar _nen tint) ::
                   (Etempvar _nen tint) :: nil))
                Sskip)
              (Ssequence
                (Sset _k (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                   (Etempvar _nquad tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'1)
                          (Evar _gauss_point (Tfunction (tint :: tint :: nil)
                                               tdouble cc_default))
                          ((Etempvar _k tint) :: (Etempvar _nquad tint) ::
                           nil))
                        (Sassign (Evar _x tdouble) (Etempvar _t'1 tdouble)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _gauss_weight (Tfunction
                                                  (tint :: tint :: nil)
                                                  tdouble cc_default))
                            ((Etempvar _k tint) :: (Etempvar _nquad tint) ::
                             nil))
                          (Sset _wt (Etempvar _t'2 tdouble)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'16
                                (Efield
                                  (Ederef
                                    (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                    (Tstruct _fem_t noattr)) _mesh
                                  (tptr (Tstruct _mesh_t noattr))))
                              (Scall (Some _t'3)
                                (Evar _mesh_shapes (Tfunction
                                                     ((tptr (Tstruct _mesh_t noattr)) ::
                                                      tint ::
                                                      (tptr tdouble) ::
                                                      (tptr tdouble) ::
                                                      (tptr tdouble) :: nil)
                                                     tdouble cc_default))
                                ((Etempvar _t'16 (tptr (Tstruct _mesh_t noattr))) ::
                                 (Etempvar _eltid tint) ::
                                 (Eaddrof (Evar _x tdouble) (tptr tdouble)) ::
                                 (Evar _N (tarray tdouble 4)) ::
                                 (Evar _dN (tarray tdouble 4)) :: nil)))
                            (Sset _wt
                              (Ebinop Omul (Etempvar _wt tdouble)
                                (Etempvar _t'3 tdouble) tdouble)))
                          (Ssequence
                            (Sifthenelse (Etempvar _Re (tptr tdouble))
                              (Ssequence
                                (Sset _du
                                  (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                (Ssequence
                                  (Sset _fx
                                    (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                  (Ssequence
                                    (Sset _U
                                      (Efield
                                        (Ederef
                                          (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                          (Tstruct _fem_t noattr)) _U
                                        (tptr tdouble)))
                                    (Ssequence
                                      (Sset _F
                                        (Efield
                                          (Ederef
                                            (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                            (Tstruct _fem_t noattr)) _F
                                          (tptr tdouble)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _j
                                            (Econst_int (Int.repr 0) tint))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _j tint)
                                                             (Etempvar _nen tint)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'13
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _dN (tarray tdouble 4))
                                                        (Etempvar _j tint)
                                                        (tptr tdouble))
                                                      tdouble))
                                                  (Ssequence
                                                    (Sset _t'14
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _elt (tptr tint))
                                                          (Etempvar _j tint)
                                                          (tptr tint)) tint))
                                                    (Ssequence
                                                      (Sset _t'15
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _U (tptr tdouble))
                                                            (Ebinop Omul
                                                              (Etempvar _ndof tint)
                                                              (Etempvar _t'14 tint)
                                                              tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Sset _du
                                                        (Ebinop Oadd
                                                          (Etempvar _du tdouble)
                                                          (Ebinop Omul
                                                            (Etempvar _t'13 tdouble)
                                                            (Etempvar _t'15 tdouble)
                                                            tdouble) tdouble)))))
                                                (Ssequence
                                                  (Sset _t'10
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _N (tarray tdouble 4))
                                                        (Etempvar _j tint)
                                                        (tptr tdouble))
                                                      tdouble))
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _elt (tptr tint))
                                                          (Etempvar _j tint)
                                                          (tptr tint)) tint))
                                                    (Ssequence
                                                      (Sset _t'12
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _F (tptr tdouble))
                                                            (Ebinop Omul
                                                              (Etempvar _ndof tint)
                                                              (Etempvar _t'11 tint)
                                                              tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Sset _fx
                                                        (Ebinop Oadd
                                                          (Etempvar _fx tdouble)
                                                          (Ebinop Omul
                                                            (Etempvar _t'10 tdouble)
                                                            (Etempvar _t'12 tdouble)
                                                            tdouble) tdouble)))))))
                                            (Sset _j
                                              (Ebinop Oadd (Etempvar _j tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint))))
                                        (Ssequence
                                          (Sset _i
                                            (Econst_int (Int.repr 0) tint))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _i tint)
                                                             (Etempvar _nen tint)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Sset _t'7
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _Re (tptr tdouble))
                                                      (Etempvar _i tint)
                                                      (tptr tdouble))
                                                    tdouble))
                                                (Ssequence
                                                  (Sset _t'8
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _dN (tarray tdouble 4))
                                                        (Etempvar _i tint)
                                                        (tptr tdouble))
                                                      tdouble))
                                                  (Ssequence
                                                    (Sset _t'9
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _N (tarray tdouble 4))
                                                          (Etempvar _i tint)
                                                          (tptr tdouble))
                                                        tdouble))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _Re (tptr tdouble))
                                                          (Etempvar _i tint)
                                                          (tptr tdouble))
                                                        tdouble)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'7 tdouble)
                                                        (Ebinop Omul
                                                          (Ebinop Osub
                                                            (Ebinop Omul
                                                              (Etempvar _t'8 tdouble)
                                                              (Etempvar _du tdouble)
                                                              tdouble)
                                                            (Ebinop Omul
                                                              (Etempvar _t'9 tdouble)
                                                              (Etempvar _fx tdouble)
                                                              tdouble)
                                                            tdouble)
                                                          (Etempvar _wt tdouble)
                                                          tdouble) tdouble))))))
                                            (Sset _i
                                              (Ebinop Oadd (Etempvar _i tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)))))))))
                              Sskip)
                            (Sifthenelse (Etempvar _Ke (tptr tdouble))
                              (Ssequence
                                (Sset _j__1 (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j__1 tint)
                                                   (Etempvar _nen tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _i__1
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i__1 tint)
                                                         (Etempvar _nen tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sset _t'4
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _Ke (tptr tdouble))
                                                  (Ebinop Oadd
                                                    (Etempvar _i__1 tint)
                                                    (Ebinop Omul
                                                      (Etempvar _j__1 tint)
                                                      (Etempvar _nen tint)
                                                      tint) tint)
                                                  (tptr tdouble)) tdouble))
                                            (Ssequence
                                              (Sset _t'5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _dN (tarray tdouble 4))
                                                    (Etempvar _i__1 tint)
                                                    (tptr tdouble)) tdouble))
                                              (Ssequence
                                                (Sset _t'6
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _dN (tarray tdouble 4))
                                                      (Etempvar _j__1 tint)
                                                      (tptr tdouble))
                                                    tdouble))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _Ke (tptr tdouble))
                                                      (Ebinop Oadd
                                                        (Etempvar _i__1 tint)
                                                        (Ebinop Omul
                                                          (Etempvar _j__1 tint)
                                                          (Etempvar _nen tint)
                                                          tint) tint)
                                                      (tptr tdouble))
                                                    tdouble)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'4 tdouble)
                                                    (Ebinop Omul
                                                      (Ebinop Omul
                                                        (Etempvar _t'5 tdouble)
                                                        (Etempvar _t'6 tdouble)
                                                        tdouble)
                                                      (Etempvar _wt tdouble)
                                                      tdouble) tdouble))))))
                                        (Sset _i__1
                                          (Ebinop Oadd (Etempvar _i__1 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))))
                                  (Sset _j__1
                                    (Ebinop Oadd (Etempvar _j__1 tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              Sskip))))))
                  (Sset _k
                    (Ebinop Oadd (Etempvar _k tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_get_quad2d := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_shapefn,
                 (tptr (Tfunction
                         ((tptr tdouble) :: (tptr tdouble) ::
                          (tptr tdouble) :: nil) tint cc_default))) ::
                (_quad_pt,
                 (tptr (tptr (Tfunction
                               ((tptr tdouble) :: tint :: tint :: nil) tvoid
                               cc_default)))) ::
                (_quad_wt,
                 (tptr (tptr (Tfunction (tint :: tint :: nil) tdouble
                               cc_default)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _shapefn (tptr (Tfunction
                                            ((tptr tdouble) ::
                                             (tptr tdouble) ::
                                             (tptr tdouble) :: nil) tint
                                            cc_default)))
                 (Evar _shapes2dP1 (Tfunction
                                     ((tptr tdouble) :: (tptr tdouble) ::
                                      (tptr tdouble) :: nil) tint cc_default))
                 tint)
    (Ssequence
      (Sassign
        (Ederef
          (Etempvar _quad_pt (tptr (tptr (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            nil) tvoid cc_default))))
          (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil) tvoid
                  cc_default)))
        (Evar _gauss2d_point (Tfunction
                               ((tptr tdouble) :: tint :: tint :: nil) tvoid
                               cc_default)))
      (Ssequence
        (Sassign
          (Ederef
            (Etempvar _quad_wt (tptr (tptr (Tfunction (tint :: tint :: nil)
                                             tdouble cc_default))))
            (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default)))
          (Evar _gauss2d_weight (Tfunction (tint :: tint :: nil) tdouble
                                  cc_default)))
        (Sreturn (Some (Econst_int (Int.repr 4) tint)))))
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _shapefn (tptr (Tfunction
                                              ((tptr tdouble) ::
                                               (tptr tdouble) ::
                                               (tptr tdouble) :: nil) tint
                                              cc_default)))
                   (Evar _shapes2dP2 (Tfunction
                                       ((tptr tdouble) :: (tptr tdouble) ::
                                        (tptr tdouble) :: nil) tint
                                       cc_default)) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Etempvar _quad_pt (tptr (tptr (Tfunction
                                             ((tptr tdouble) :: tint ::
                                              tint :: nil) tvoid cc_default))))
            (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil) tvoid
                    cc_default)))
          (Evar _gauss2d_point (Tfunction
                                 ((tptr tdouble) :: tint :: tint :: nil)
                                 tvoid cc_default)))
        (Ssequence
          (Sassign
            (Ederef
              (Etempvar _quad_wt (tptr (tptr (Tfunction (tint :: tint :: nil)
                                               tdouble cc_default))))
              (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default)))
            (Evar _gauss2d_weight (Tfunction (tint :: tint :: nil) tdouble
                                    cc_default)))
          (Sreturn (Some (Econst_int (Int.repr 9) tint)))))
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _shapefn (tptr (Tfunction
                                                ((tptr tdouble) ::
                                                 (tptr tdouble) ::
                                                 (tptr tdouble) :: nil) tint
                                                cc_default)))
                     (Evar _shapes2dS2 (Tfunction
                                         ((tptr tdouble) :: (tptr tdouble) ::
                                          (tptr tdouble) :: nil) tint
                                         cc_default)) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Etempvar _quad_pt (tptr (tptr (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: nil) tvoid
                                               cc_default))))
              (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil) tvoid
                      cc_default)))
            (Evar _gauss2d_point (Tfunction
                                   ((tptr tdouble) :: tint :: tint :: nil)
                                   tvoid cc_default)))
          (Ssequence
            (Sassign
              (Ederef
                (Etempvar _quad_wt (tptr (tptr (Tfunction
                                                 (tint :: tint :: nil)
                                                 tdouble cc_default))))
                (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default)))
              (Evar _gauss2d_weight (Tfunction (tint :: tint :: nil) tdouble
                                      cc_default)))
            (Sreturn (Some (Econst_int (Int.repr 9) tint)))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _shapefn (tptr (Tfunction
                                                  ((tptr tdouble) ::
                                                   (tptr tdouble) ::
                                                   (tptr tdouble) :: nil)
                                                  tint cc_default)))
                       (Evar _shapes2dT1 (Tfunction
                                           ((tptr tdouble) ::
                                            (tptr tdouble) ::
                                            (tptr tdouble) :: nil) tint
                                           cc_default)) tint)
          (Ssequence
            (Sassign
              (Ederef
                (Etempvar _quad_pt (tptr (tptr (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: nil) tvoid
                                                 cc_default))))
                (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil)
                        tvoid cc_default)))
              (Evar _hughes_point (Tfunction
                                    ((tptr tdouble) :: tint :: tint :: nil)
                                    tvoid cc_default)))
            (Ssequence
              (Sassign
                (Ederef
                  (Etempvar _quad_wt (tptr (tptr (Tfunction
                                                   (tint :: tint :: nil)
                                                   tdouble cc_default))))
                  (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default)))
                (Evar _hughes_weight (Tfunction (tint :: tint :: nil) tdouble
                                       cc_default)))
              (Sreturn (Some (Econst_int (Int.repr 3) tint)))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_3 (tarray tschar 30)) ::
               (Evar ___stringlit_2 (tarray tschar 10)) ::
               (Econst_int (Int.repr 195) tint) ::
               (Evar ___stringlit_1 (tarray tschar 2)) :: nil))
            (Scall None (Evar _abort (Tfunction nil tvoid cc_default)) nil))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_poisson2d_elt_dR := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) ::
                (_fe, (tptr (Tstruct _fem_t noattr))) :: (_eltid, tint) ::
                (_Re, (tptr tdouble)) :: (_Ke, (tptr tdouble)) :: nil);
  fn_vars := ((_quad_pt,
               (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil) tvoid
                       cc_default))) ::
              (_quad_wt,
               (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default))) ::
              (_N, (tarray tdouble 4)) :: (_dN, (tarray tdouble 8)) ::
              (_x, (tarray tdouble 2)) :: (_du, (tarray tdouble 2)) :: nil);
  fn_temps := ((_nen, tint) :: (_ndof, tint) :: (_nquad, tint) ::
               (_elt, (tptr tint)) :: (_k, tint) :: (_wt, tdouble) ::
               (_J, tdouble) :: (_fx, tdouble) :: (_U, (tptr tdouble)) ::
               (_F, (tptr tdouble)) :: (_j, tint) :: (_i, tint) ::
               (_j__1, tint) :: (_i__1, tint) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tint) ::
               (_t'33, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'32,
                (tptr (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))) ::
               (_t'31, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'30, (tptr tint)) ::
               (_t'29, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'28,
                (tptr (Tfunction ((tptr tdouble) :: tint :: tint :: nil)
                        tvoid cc_default))) ::
               (_t'27,
                (tptr (Tfunction (tint :: tint :: nil) tdouble cc_default))) ::
               (_t'26, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'25, tdouble) :: (_t'24, tdouble) :: (_t'23, tint) ::
               (_t'22, tdouble) :: (_t'21, tdouble) :: (_t'20, tdouble) ::
               (_t'19, tint) :: (_t'18, tdouble) :: (_t'17, tdouble) ::
               (_t'16, tint) :: (_t'15, tdouble) :: (_t'14, tdouble) ::
               (_t'13, tdouble) :: (_t'12, tdouble) :: (_t'11, tdouble) ::
               (_t'10, tdouble) :: (_t'9, tdouble) :: (_t'8, tdouble) ::
               (_t'7, tdouble) :: (_t'6, tdouble) :: (_t'5, tdouble) ::
               (_t'4, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'33
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
    (Sset _nen
      (Efield
        (Ederef (Etempvar _t'33 (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _nen tint)))
  (Ssequence
    (Sset _ndof
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _ndof tint))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'31
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _mesh
              (tptr (Tstruct _mesh_t noattr))))
          (Ssequence
            (Sset _t'32
              (Efield
                (Ederef (Etempvar _t'31 (tptr (Tstruct _mesh_t noattr)))
                  (Tstruct _mesh_t noattr)) _shape
                (tptr (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))))
            (Scall (Some _t'1)
              (Evar _get_quad2d (Tfunction
                                  ((tptr (Tfunction
                                           ((tptr tdouble) ::
                                            (tptr tdouble) ::
                                            (tptr tdouble) :: nil) tint
                                           cc_default)) ::
                                   (tptr (tptr (Tfunction
                                                 ((tptr tdouble) :: tint ::
                                                  tint :: nil) tvoid
                                                 cc_default))) ::
                                   (tptr (tptr (Tfunction
                                                 (tint :: tint :: nil)
                                                 tdouble cc_default))) ::
                                   nil) tint cc_default))
              ((Etempvar _t'32 (tptr (Tfunction
                                       ((tptr tdouble) :: (tptr tdouble) ::
                                        (tptr tdouble) :: nil) tint
                                       cc_default))) ::
               (Eaddrof
                 (Evar _quad_pt (tptr (Tfunction
                                        ((tptr tdouble) :: tint :: tint ::
                                         nil) tvoid cc_default)))
                 (tptr (tptr (Tfunction
                               ((tptr tdouble) :: tint :: tint :: nil) tvoid
                               cc_default)))) ::
               (Eaddrof
                 (Evar _quad_wt (tptr (Tfunction (tint :: tint :: nil)
                                        tdouble cc_default)))
                 (tptr (tptr (Tfunction (tint :: tint :: nil) tdouble
                               cc_default)))) :: nil))))
        (Sset _nquad (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Sset _t'29
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _mesh
              (tptr (Tstruct _mesh_t noattr))))
          (Ssequence
            (Sset _t'30
              (Efield
                (Ederef (Etempvar _t'29 (tptr (Tstruct _mesh_t noattr)))
                  (Tstruct _mesh_t noattr)) _elt (tptr tint)))
            (Sset _elt
              (Ebinop Oadd (Etempvar _t'30 (tptr tint))
                (Ebinop Omul (Etempvar _eltid tint) (Etempvar _nen tint)
                  tint) (tptr tint)))))
        (Ssequence
          (Sifthenelse (Etempvar _Re (tptr tdouble))
            (Scall None
              (Evar _double_clear (Tfunction ((tptr tdouble) :: tint :: nil)
                                    tvoid cc_default))
              ((Etempvar _Re (tptr tdouble)) :: (Etempvar _nen tint) :: nil))
            Sskip)
          (Ssequence
            (Sifthenelse (Etempvar _Ke (tptr tdouble))
              (Scall None
                (Evar _densematn_clear (Tfunction
                                         ((tptr tdouble) :: tint :: tint ::
                                          nil) tvoid cc_default))
                ((Etempvar _Ke (tptr tdouble)) :: (Etempvar _nen tint) ::
                 (Etempvar _nen tint) :: nil))
              Sskip)
            (Ssequence
              (Sset _k (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                 (Etempvar _nquad tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'28
                        (Evar _quad_pt (tptr (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: nil) tvoid
                                               cc_default))))
                      (Scall None
                        (Ederef
                          (Etempvar _t'28 (tptr (Tfunction
                                                  ((tptr tdouble) :: tint ::
                                                   tint :: nil) tvoid
                                                  cc_default)))
                          (Tfunction ((tptr tdouble) :: tint :: tint :: nil)
                            tvoid cc_default))
                        ((Evar _x (tarray tdouble 2)) ::
                         (Etempvar _k tint) :: (Etempvar _nquad tint) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'27
                            (Evar _quad_wt (tptr (Tfunction
                                                   (tint :: tint :: nil)
                                                   tdouble cc_default))))
                          (Scall (Some _t'2)
                            (Ederef
                              (Etempvar _t'27 (tptr (Tfunction
                                                      (tint :: tint :: nil)
                                                      tdouble cc_default)))
                              (Tfunction (tint :: tint :: nil) tdouble
                                cc_default))
                            ((Etempvar _k tint) :: (Etempvar _nquad tint) ::
                             nil)))
                        (Sset _wt (Etempvar _t'2 tdouble)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'26
                              (Efield
                                (Ederef
                                  (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                  (Tstruct _fem_t noattr)) _mesh
                                (tptr (Tstruct _mesh_t noattr))))
                            (Scall (Some _t'3)
                              (Evar _mesh_shapes (Tfunction
                                                   ((tptr (Tstruct _mesh_t noattr)) ::
                                                    tint :: (tptr tdouble) ::
                                                    (tptr tdouble) ::
                                                    (tptr tdouble) :: nil)
                                                   tdouble cc_default))
                              ((Etempvar _t'26 (tptr (Tstruct _mesh_t noattr))) ::
                               (Etempvar _eltid tint) ::
                               (Evar _x (tarray tdouble 2)) ::
                               (Evar _N (tarray tdouble 4)) ::
                               (Evar _dN (tarray tdouble 8)) :: nil)))
                          (Sset _J (Etempvar _t'3 tdouble)))
                        (Ssequence
                          (Sset _wt
                            (Ebinop Omul (Etempvar _wt tdouble)
                              (Etempvar _J tdouble) tdouble))
                          (Ssequence
                            (Sifthenelse (Etempvar _Re (tptr tdouble))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _du (tarray tdouble 2))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr tdouble)) tdouble)
                                  (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _du (tarray tdouble 2))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tdouble)) tdouble)
                                    (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                  (Ssequence
                                    (Sset _fx
                                      (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
                                    (Ssequence
                                      (Sset _U
                                        (Efield
                                          (Ederef
                                            (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                            (Tstruct _fem_t noattr)) _U
                                          (tptr tdouble)))
                                      (Ssequence
                                        (Sset _F
                                          (Efield
                                            (Ederef
                                              (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                              (Tstruct _fem_t noattr)) _F
                                            (tptr tdouble)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _j
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _j tint)
                                                               (Etempvar _nen tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'22
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _du (tarray tdouble 2))
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tdouble))
                                                        tdouble))
                                                    (Ssequence
                                                      (Sset _t'23
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _elt (tptr tint))
                                                            (Etempvar _j tint)
                                                            (tptr tint))
                                                          tint))
                                                      (Ssequence
                                                        (Sset _t'24
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _U (tptr tdouble))
                                                              (Ebinop Omul
                                                                (Etempvar _ndof tint)
                                                                (Etempvar _t'23 tint)
                                                                tint)
                                                              (tptr tdouble))
                                                            tdouble))
                                                        (Ssequence
                                                          (Sset _t'25
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _dN (tarray tdouble 8))
                                                                (Ebinop Oadd
                                                                  (Etempvar _j tint)
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (Etempvar _nen tint)
                                                                    tint)
                                                                  tint)
                                                                (tptr tdouble))
                                                              tdouble))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _du (tarray tdouble 2))
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tdouble))
                                                              tdouble)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'22 tdouble)
                                                              (Ebinop Omul
                                                                (Etempvar _t'24 tdouble)
                                                                (Etempvar _t'25 tdouble)
                                                                tdouble)
                                                              tdouble))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'18
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _du (tarray tdouble 2))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Ssequence
                                                        (Sset _t'19
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _elt (tptr tint))
                                                              (Etempvar _j tint)
                                                              (tptr tint))
                                                            tint))
                                                        (Ssequence
                                                          (Sset _t'20
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _U (tptr tdouble))
                                                                (Ebinop Omul
                                                                  (Etempvar _ndof tint)
                                                                  (Etempvar _t'19 tint)
                                                                  tint)
                                                                (tptr tdouble))
                                                              tdouble))
                                                          (Ssequence
                                                            (Sset _t'21
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _dN (tarray tdouble 8))
                                                                  (Ebinop Oadd
                                                                    (Etempvar _j tint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Etempvar _nen tint)
                                                                    tint)
                                                                    tint)
                                                                  (tptr tdouble))
                                                                tdouble))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _du (tarray tdouble 2))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tdouble))
                                                                tdouble)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'18 tdouble)
                                                                (Ebinop Omul
                                                                  (Etempvar _t'20 tdouble)
                                                                  (Etempvar _t'21 tdouble)
                                                                  tdouble)
                                                                tdouble))))))
                                                    (Ssequence
                                                      (Sset _t'15
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _N (tarray tdouble 4))
                                                            (Etempvar _j tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Ssequence
                                                        (Sset _t'16
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _elt (tptr tint))
                                                              (Etempvar _j tint)
                                                              (tptr tint))
                                                            tint))
                                                        (Ssequence
                                                          (Sset _t'17
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _F (tptr tdouble))
                                                                (Ebinop Omul
                                                                  (Etempvar _ndof tint)
                                                                  (Etempvar _t'16 tint)
                                                                  tint)
                                                                (tptr tdouble))
                                                              tdouble))
                                                          (Sset _fx
                                                            (Ebinop Oadd
                                                              (Etempvar _fx tdouble)
                                                              (Ebinop Omul
                                                                (Etempvar _t'15 tdouble)
                                                                (Etempvar _t'17 tdouble)
                                                                tdouble)
                                                              tdouble))))))))
                                              (Sset _j
                                                (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))
                                          (Ssequence
                                            (Sset _i
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i tint)
                                                               (Etempvar _nen tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Sset _t'9
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _Re (tptr tdouble))
                                                        (Etempvar _i tint)
                                                        (tptr tdouble))
                                                      tdouble))
                                                  (Ssequence
                                                    (Sset _t'10
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _dN (tarray tdouble 8))
                                                          (Ebinop Oadd
                                                            (Etempvar _i tint)
                                                            (Ebinop Omul
                                                              (Econst_int (Int.repr 0) tint)
                                                              (Etempvar _nen tint)
                                                              tint) tint)
                                                          (tptr tdouble))
                                                        tdouble))
                                                    (Ssequence
                                                      (Sset _t'11
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _du (tarray tdouble 2))
                                                            (Econst_int (Int.repr 0) tint)
                                                            (tptr tdouble))
                                                          tdouble))
                                                      (Ssequence
                                                        (Sset _t'12
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _dN (tarray tdouble 8))
                                                              (Ebinop Oadd
                                                                (Etempvar _i tint)
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (Etempvar _nen tint)
                                                                  tint) tint)
                                                              (tptr tdouble))
                                                            tdouble))
                                                        (Ssequence
                                                          (Sset _t'13
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _du (tarray tdouble 2))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tdouble))
                                                              tdouble))
                                                          (Ssequence
                                                            (Sset _t'14
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _N (tarray tdouble 4))
                                                                  (Etempvar _i tint)
                                                                  (tptr tdouble))
                                                                tdouble))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _Re (tptr tdouble))
                                                                  (Etempvar _i tint)
                                                                  (tptr tdouble))
                                                                tdouble)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'9 tdouble)
                                                                (Ebinop Omul
                                                                  (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Etempvar _t'10 tdouble)
                                                                    (Etempvar _t'11 tdouble)
                                                                    tdouble)
                                                                    (Ebinop Omul
                                                                    (Etempvar _t'12 tdouble)
                                                                    (Etempvar _t'13 tdouble)
                                                                    tdouble)
                                                                    tdouble)
                                                                    (Ebinop Omul
                                                                    (Etempvar _t'14 tdouble)
                                                                    (Etempvar _fx tdouble)
                                                                    tdouble)
                                                                    tdouble)
                                                                  (Etempvar _wt tdouble)
                                                                  tdouble)
                                                                tdouble)))))))))
                                              (Sset _i
                                                (Ebinop Oadd
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))))))))
                              Sskip)
                            (Sifthenelse (Etempvar _Ke (tptr tdouble))
                              (Ssequence
                                (Sset _j__1 (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j__1 tint)
                                                   (Etempvar _nen tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _i__1
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i__1 tint)
                                                         (Etempvar _nen tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sset _t'4
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _Ke (tptr tdouble))
                                                  (Ebinop Oadd
                                                    (Etempvar _i__1 tint)
                                                    (Ebinop Omul
                                                      (Etempvar _j__1 tint)
                                                      (Etempvar _nen tint)
                                                      tint) tint)
                                                  (tptr tdouble)) tdouble))
                                            (Ssequence
                                              (Sset _t'5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _dN (tarray tdouble 8))
                                                    (Etempvar _i__1 tint)
                                                    (tptr tdouble)) tdouble))
                                              (Ssequence
                                                (Sset _t'6
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _dN (tarray tdouble 8))
                                                      (Etempvar _j__1 tint)
                                                      (tptr tdouble))
                                                    tdouble))
                                                (Ssequence
                                                  (Sset _t'7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _dN (tarray tdouble 8))
                                                        (Ebinop Oadd
                                                          (Etempvar _i__1 tint)
                                                          (Etempvar _nen tint)
                                                          tint)
                                                        (tptr tdouble))
                                                      tdouble))
                                                  (Ssequence
                                                    (Sset _t'8
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _dN (tarray tdouble 8))
                                                          (Ebinop Oadd
                                                            (Etempvar _j__1 tint)
                                                            (Etempvar _nen tint)
                                                            tint)
                                                          (tptr tdouble))
                                                        tdouble))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _Ke (tptr tdouble))
                                                          (Ebinop Oadd
                                                            (Etempvar _i__1 tint)
                                                            (Ebinop Omul
                                                              (Etempvar _j__1 tint)
                                                              (Etempvar _nen tint)
                                                              tint) tint)
                                                          (tptr tdouble))
                                                        tdouble)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'4 tdouble)
                                                        (Ebinop Omul
                                                          (Ebinop Oadd
                                                            (Ebinop Omul
                                                              (Etempvar _t'5 tdouble)
                                                              (Etempvar _t'6 tdouble)
                                                              tdouble)
                                                            (Ebinop Omul
                                                              (Etempvar _t'7 tdouble)
                                                              (Etempvar _t'8 tdouble)
                                                              tdouble)
                                                            tdouble)
                                                          (Etempvar _wt tdouble)
                                                          tdouble) tdouble))))))))
                                        (Sset _i__1
                                          (Ebinop Oadd (Etempvar _i__1 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))))
                                  (Sset _j__1
                                    (Ebinop Oadd (Etempvar _j__1 tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              Sskip)))))))
                (Sset _k
                  (Ebinop Oadd (Etempvar _k tint)
                    (Econst_int (Int.repr 1) tint) tint))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _mesh_t Struct
   (Member_plain _X (tptr tdouble) :: Member_plain _elt (tptr tint) ::
    Member_plain _d tint :: Member_plain _numnp tint ::
    Member_plain _nen tint :: Member_plain _numelt tint ::
    Member_plain _shape
      (tptr (Tfunction
              ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil)
              tint cc_default)) :: nil)
   noattr ::
 Composite _fem_t Struct
   (Member_plain _mesh (tptr (Tstruct _mesh_t noattr)) ::
    Member_plain _etype (tptr (Tstruct _element_t noattr)) ::
    Member_plain _U (tptr tdouble) :: Member_plain _F (tptr tdouble) ::
    Member_plain _id (tptr tint) :: Member_plain _ndof tint ::
    Member_plain _nactive tint :: nil)
   noattr ::
 Composite _element_t Struct
   (Member_plain _p (tptr tvoid) ::
    Member_plain _dR
      (tptr (Tfunction
              ((tptr tvoid) :: (tptr (Tstruct _fem_t noattr)) :: tint ::
               (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default)) ::
    Member_plain _free
      (tptr (Tfunction ((tptr tvoid) :: nil) tvoid cc_default)) :: nil)
   noattr ::
 Composite _poisson_elt_t Struct
   (Member_plain _e (Tstruct _element_t noattr) :: nil)
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
     cc_default)) :: (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Xptr :: nil) AST.Xint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_free, Gfun(External EF_free ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil AST.Xvoid cc_default))
     nil tvoid cc_default)) ::
 (_shapes2dP1,
   Gfun(External (EF_external "shapes2dP1"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_shapes2dP2,
   Gfun(External (EF_external "shapes2dP2"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_shapes2dS2,
   Gfun(External (EF_external "shapes2dS2"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_shapes2dT1,
   Gfun(External (EF_external "shapes2dT1"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_gauss_point,
   Gfun(External (EF_external "gauss_point"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xfloat
                     cc_default)) (tint :: tint :: nil) tdouble cc_default)) ::
 (_gauss_weight,
   Gfun(External (EF_external "gauss_weight"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xfloat
                     cc_default)) (tint :: tint :: nil) tdouble cc_default)) ::
 (_gauss2d_point,
   Gfun(External (EF_external "gauss2d_point"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tdouble) :: tint :: tint :: nil) tvoid cc_default)) ::
 (_gauss2d_weight,
   Gfun(External (EF_external "gauss2d_weight"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xfloat
                     cc_default)) (tint :: tint :: nil) tdouble cc_default)) ::
 (_hughes_point,
   Gfun(External (EF_external "hughes_point"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tdouble) :: tint :: tint :: nil) tvoid cc_default)) ::
 (_hughes_weight,
   Gfun(External (EF_external "hughes_weight"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xfloat
                     cc_default)) (tint :: tint :: nil) tdouble cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_double_clear,
   Gfun(External (EF_external "double_clear"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tdouble) :: tint :: nil) tvoid
     cc_default)) ::
 (_densematn_clear,
   Gfun(External (EF_external "densematn_clear"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tdouble) :: tint :: tint :: nil) tvoid cc_default)) ::
 (_mesh_shapes,
   Gfun(External (EF_external "mesh_shapes"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xptr ::
                      AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr (Tstruct _mesh_t noattr)) :: tint :: (tptr tdouble) ::
      (tptr tdouble) :: (tptr tdouble) :: nil) tdouble cc_default)) ::
 (_element_dR, Gfun(Internal f_element_dR)) ::
 (_element_free, Gfun(Internal f_element_free)) ::
 (_malloc_poisson1d_element, Gfun(Internal f_malloc_poisson1d_element)) ::
 (_malloc_poisson2d_element, Gfun(Internal f_malloc_poisson2d_element)) ::
 (_simple_elt_free, Gfun(Internal f_simple_elt_free)) ::
 (_poisson1d_elt_dR, Gfun(Internal f_poisson1d_elt_dR)) ::
 (_get_quad2d, Gfun(Internal f_get_quad2d)) ::
 (_poisson2d_elt_dR, Gfun(Internal f_poisson2d_elt_dR)) :: nil).

Definition public_idents : list ident :=
(_poisson2d_elt_dR :: _get_quad2d :: _poisson1d_elt_dR :: _simple_elt_free ::
 _malloc_poisson2d_element :: _malloc_poisson1d_element :: _element_free ::
 _element_dR :: _mesh_shapes :: _densematn_clear :: _double_clear ::
 _surely_malloc :: _hughes_weight :: _hughes_point :: _gauss2d_weight ::
 _gauss2d_point :: _gauss_weight :: _gauss_point :: _shapes2dT1 ::
 _shapes2dS2 :: _shapes2dP2 :: _shapes2dP1 :: _abort :: _free :: _printf ::
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


