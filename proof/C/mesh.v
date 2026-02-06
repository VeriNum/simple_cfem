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
  Definition source_file := "../src/mesh.c".
  Definition normalized := true.
End Info.

Definition _J : ident := $"J".
Definition _N : ident := $"N".
Definition _X : ident := $"X".
Definition _Xi : ident := $"Xi".
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
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_11 : ident := $"__stringlit_11".
Definition ___stringlit_12 : ident := $"__stringlit_12".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition _a : ident := $"a".
Definition _abort : ident := $"abort".
Definition _b : ident := $"b".
Definition _d : ident := $"d".
Definition _dN : ident := $"dN".
Definition _dNk : ident := $"dNk".
Definition _degree : ident := $"degree".
Definition _densematn_clear : ident := $"densematn_clear".
Definition _densematn_lufactor : ident := $"densematn_lufactor".
Definition _densematn_lujac : ident := $"densematn_lujac".
Definition _densematn_lusolveT : ident := $"densematn_lusolveT".
Definition _double_calloc : ident := $"double_calloc".
Definition _double_clear : ident := $"double_clear".
Definition _elt : ident := $"elt".
Definition _eltid : ident := $"eltid".
Definition _free : ident := $"free".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _i_nw : ident := $"i_nw".
Definition _i_sw : ident := $"i_sw".
Definition _i_ww : ident := $"i_ww".
Definition _int_calloc : ident := $"int_calloc".
Definition _ipiv : ident := $"ipiv".
Definition _ix : ident := $"ix".
Definition _ix__1 : ident := $"ix__1".
Definition _ix__2 : ident := $"ix__2".
Definition _ix__3 : ident := $"ix__3".
Definition _iy : ident := $"iy".
Definition _iy__1 : ident := $"iy__1".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _j__2 : ident := $"j__2".
Definition _k : ident := $"k".
Definition _k__1 : ident := $"k__1".
Definition _k__2 : ident := $"k__2".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _mesh : ident := $"mesh".
Definition _mesh_block2d_P1 : ident := $"mesh_block2d_P1".
Definition _mesh_block2d_P2 : ident := $"mesh_block2d_P2".
Definition _mesh_block2d_S2 : ident := $"mesh_block2d_S2".
Definition _mesh_block2d_T1 : ident := $"mesh_block2d_T1".
Definition _mesh_create1d : ident := $"mesh_create1d".
Definition _mesh_free : ident := $"mesh_free".
Definition _mesh_malloc : ident := $"mesh_malloc".
Definition _mesh_print : ident := $"mesh_print".
Definition _mesh_print_elt : ident := $"mesh_print_elt".
Definition _mesh_print_nodes : ident := $"mesh_print_nodes".
Definition _mesh_shapes : ident := $"mesh_shapes".
Definition _mesh_t : ident := $"mesh_t".
Definition _mesh_to_spatial : ident := $"mesh_to_spatial".
Definition _nen : ident := $"nen".
Definition _nex : ident := $"nex".
Definition _ney : ident := $"ney".
Definition _nshape : ident := $"nshape".
Definition _numelt : ident := $"numelt".
Definition _numnp : ident := $"numnp".
Definition _nx : ident := $"nx".
Definition _nx0 : ident := $"nx0".
Definition _nx1 : ident := $"nx1".
Definition _ny : ident := $"ny".
Definition _printf : ident := $"printf".
Definition _shape : ident := $"shape".
Definition _shapes1dP1 : ident := $"shapes1dP1".
Definition _shapes1dP2 : ident := $"shapes1dP2".
Definition _shapes1dP3 : ident := $"shapes1dP3".
Definition _shapes2dP1 : ident := $"shapes2dP1".
Definition _shapes2dP2 : ident := $"shapes2dP2".
Definition _shapes2dS2 : ident := $"shapes2dS2".
Definition _shapes2dT1 : ident := $"shapes2dT1".
Definition _start : ident := $"start".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _x : ident := $"x".
Definition _xout : ident := $"xout".
Definition _xref : ident := $"xref".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
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

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mesh_malloc := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_d, tint) :: (_numnp, tint) :: (_nen, tint) ::
                (_numelt, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_mesh, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'3, (tptr tint)) :: (_t'2, (tptr tdouble)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _mesh_t noattr) tulong) :: nil))
    (Sset _mesh (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _d tint) (Etempvar _d tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _numnp tint) (Etempvar _numnp tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
              (Tstruct _mesh_t noattr)) _nen tint) (Etempvar _nen tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _numelt tint)
            (Etempvar _numelt tint))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _double_calloc (Tfunction (tint :: nil) (tptr tdouble)
                                       cc_default))
                ((Ebinop Omul (Etempvar _d tint) (Etempvar _numnp tint) tint) ::
                 nil))
              (Sassign
                (Efield
                  (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                    (Tstruct _mesh_t noattr)) _X (tptr tdouble))
                (Etempvar _t'2 (tptr tdouble))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _int_calloc (Tfunction (tint :: nil) (tptr tint)
                                      cc_default))
                  ((Ebinop Omul (Etempvar _nen tint) (Etempvar _numelt tint)
                     tint) :: nil))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                      (Tstruct _mesh_t noattr)) _elt (tptr tint))
                  (Etempvar _t'3 (tptr tint))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                      (Tstruct _mesh_t noattr)) _shape
                    (tptr (Tfunction
                            ((tptr tdouble) :: (tptr tdouble) ::
                             (tptr tdouble) :: nil) tint cc_default)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))))))))))))
|}.

Definition f_mesh_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tint)) :: (_t'1, (tptr tdouble)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _elt (tptr tint)))
    (Scall None
      (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _t'2 (tptr tint)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _X (tptr tdouble)))
      (Scall None
        (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _t'1 (tptr tdouble)) :: nil)))
    (Scall None
      (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _mesh (tptr (Tstruct _mesh_t noattr))) :: nil))))
|}.

Definition f_mesh_create1d := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_numelt, tint) :: (_degree, tint) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_numnp, tint) :: (_nen, tint) ::
               (_mesh, (tptr (Tstruct _mesh_t noattr))) ::
               (_X, (tptr tdouble)) :: (_i, tint) :: (_elt, (tptr tint)) ::
               (_j, tint) :: (_i__1, tint) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _numnp
    (Ebinop Oadd
      (Ebinop Omul (Etempvar _numelt tint) (Etempvar _degree tint) tint)
      (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _nen
      (Ebinop Oadd (Etempvar _degree tint) (Econst_int (Int.repr 1) tint)
        tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mesh_malloc (Tfunction (tint :: tint :: tint :: tint :: nil)
                               (tptr (Tstruct _mesh_t noattr)) cc_default))
          ((Econst_int (Int.repr 1) tint) :: (Etempvar _numnp tint) ::
           (Etempvar _nen tint) :: (Etempvar _numelt tint) :: nil))
        (Sset _mesh (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _degree tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Sassign
            (Efield
              (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _shape
              (tptr (Tfunction
                      ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) ::
                       nil) tint cc_default)))
            (Evar _shapes1dP1 (Tfunction
                                ((tptr tdouble) :: (tptr tdouble) ::
                                 (tptr tdouble) :: nil) tint cc_default)))
          (Sifthenelse (Ebinop Oeq (Etempvar _degree tint)
                         (Econst_int (Int.repr 2) tint) tint)
            (Sassign
              (Efield
                (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                  (Tstruct _mesh_t noattr)) _shape
                (tptr (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default)))
              (Evar _shapes1dP2 (Tfunction
                                  ((tptr tdouble) :: (tptr tdouble) ::
                                   (tptr tdouble) :: nil) tint cc_default)))
            (Sifthenelse (Ebinop Oeq (Etempvar _degree tint)
                           (Econst_int (Int.repr 3) tint) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                    (Tstruct _mesh_t noattr)) _shape
                  (tptr (Tfunction
                          ((tptr tdouble) :: (tptr tdouble) ::
                           (tptr tdouble) :: nil) tint cc_default)))
                (Evar _shapes1dP3 (Tfunction
                                    ((tptr tdouble) :: (tptr tdouble) ::
                                     (tptr tdouble) :: nil) tint cc_default)))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_3 (tarray tschar 30)) ::
                   (Evar ___stringlit_2 (tarray tschar 7)) ::
                   (Econst_int (Int.repr 50) tint) ::
                   (Evar ___stringlit_1 (tarray tschar 2)) :: nil))
                (Scall None (Evar _abort (Tfunction nil tvoid cc_default))
                  nil)))))
        (Ssequence
          (Sset _X
            (Efield
              (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _X (tptr tdouble)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Etempvar _numnp tint) tint)
                    Sskip
                    Sbreak)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _X (tptr tdouble))
                        (Etempvar _i tint) (tptr tdouble)) tdouble)
                    (Ebinop Odiv
                      (Ebinop Oadd
                        (Ebinop Omul (Etempvar _i tint) (Etempvar _b tdouble)
                          tdouble)
                        (Ebinop Omul
                          (Ebinop Osub
                            (Ebinop Osub (Etempvar _numnp tint)
                              (Etempvar _i tint) tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (Etempvar _a tdouble) tdouble) tdouble)
                      (Ebinop Osub (Etempvar _numnp tint)
                        (Econst_int (Int.repr 1) tint) tint) tdouble)))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _elt
                (Efield
                  (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                    (Tstruct _mesh_t noattr)) _elt (tptr tint)))
              (Ssequence
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                     (Etempvar _numelt tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _i__1 (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                                           (Etempvar _nen tint) tint)
                              Sskip
                              Sbreak)
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _elt (tptr tint))
                                  (Ebinop Oadd (Etempvar _i__1 tint)
                                    (Ebinop Omul (Etempvar _j tint)
                                      (Etempvar _nen tint) tint) tint)
                                  (tptr tint)) tint)
                              (Ebinop Oadd (Etempvar _i__1 tint)
                                (Ebinop Omul (Etempvar _j tint)
                                  (Ebinop Osub (Etempvar _nen tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint) tint)))
                          (Sset _i__1
                            (Ebinop Oadd (Etempvar _i__1 tint)
                              (Econst_int (Int.repr 1) tint) tint)))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))))))))))))
|}.

Definition f_mesh_block2d_P1 := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_nex, tint) :: (_ney, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nx, tint) :: (_ny, tint) ::
               (_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_iy, tint) ::
               (_ix, tint) :: (_i, tint) :: (_iy__1, tint) ::
               (_ix__1, tint) :: (_i__1, tint) :: (_i_sw, tint) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'7, (tptr tdouble)) :: (_t'6, (tptr tdouble)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) ::
               (_t'3, (tptr tint)) :: (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _nx
    (Ebinop Oadd (Etempvar _nex tint) (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _ny
      (Ebinop Oadd (Etempvar _ney tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mesh_malloc (Tfunction (tint :: tint :: tint :: tint :: nil)
                               (tptr (Tstruct _mesh_t noattr)) cc_default))
          ((Econst_int (Int.repr 2) tint) ::
           (Ebinop Omul (Etempvar _nx tint) (Etempvar _ny tint) tint) ::
           (Econst_int (Int.repr 4) tint) ::
           (Ebinop Omul (Etempvar _nex tint) (Etempvar _ney tint) tint) ::
           nil))
        (Sset _mesh (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
              (Tstruct _mesh_t noattr)) _shape
            (tptr (Tfunction
                    ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) ::
                     nil) tint cc_default)))
          (Evar _shapes2dP1 (Tfunction
                              ((tptr tdouble) :: (tptr tdouble) ::
                               (tptr tdouble) :: nil) tint cc_default)))
        (Ssequence
          (Ssequence
            (Sset _iy (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _iy tint)
                               (Ebinop Oadd (Etempvar _ney tint)
                                 (Econst_int (Int.repr 1) tint) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _ix (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _ix tint)
                                     (Ebinop Oadd (Etempvar _nex tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                                     tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _i
                          (Ebinop Oadd (Etempvar _ix tint)
                            (Ebinop Omul (Etempvar _iy tint)
                              (Ebinop Oadd (Etempvar _nex tint)
                                (Econst_int (Int.repr 1) tint) tint) tint)
                            tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'7 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 0) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _ix tint) tdouble)
                                (Ebinop Osub (Etempvar _nx tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble)))
                          (Ssequence
                            (Sset _t'6
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'6 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _iy tint) tdouble)
                                (Ebinop Osub (Etempvar _ny tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble))))))
                    (Sset _ix
                      (Ebinop Oadd (Etempvar _ix tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              (Sset _iy
                (Ebinop Oadd (Etempvar _iy tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _iy__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _iy__1 tint)
                                 (Etempvar _ney tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _ix__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _ix__1 tint)
                                       (Etempvar _nex tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _i__1
                            (Ebinop Oadd (Etempvar _ix__1 tint)
                              (Ebinop Omul (Etempvar _iy__1 tint)
                                (Etempvar _nex tint) tint) tint))
                          (Ssequence
                            (Sset _i_sw
                              (Ebinop Oadd (Etempvar _ix__1 tint)
                                (Ebinop Omul (Etempvar _iy__1 tint)
                                  (Ebinop Oadd (Etempvar _nex tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Ederef
                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _elt
                                    (tptr tint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 4) tint)
                                          (Etempvar _i__1 tint) tint)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      (tptr tint)) tint)
                                  (Etempvar _i_sw tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'4
                                    (Efield
                                      (Ederef
                                        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                        (Tstruct _mesh_t noattr)) _elt
                                      (tptr tint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'4 (tptr tint))
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 4) tint)
                                            (Etempvar _i__1 tint) tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) (tptr tint)) tint)
                                    (Ebinop Oadd (Etempvar _i_sw tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'3
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _elt
                                        (tptr tint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'3 (tptr tint))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 4) tint)
                                              (Etempvar _i__1 tint) tint)
                                            (Econst_int (Int.repr 2) tint)
                                            tint) (tptr tint)) tint)
                                      (Ebinop Oadd
                                        (Ebinop Oadd
                                          (Ebinop Oadd (Etempvar _i_sw tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (Etempvar _nex tint) tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  (Ssequence
                                    (Sset _t'2
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _elt
                                        (tptr tint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'2 (tptr tint))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 4) tint)
                                              (Etempvar _i__1 tint) tint)
                                            (Econst_int (Int.repr 3) tint)
                                            tint) (tptr tint)) tint)
                                      (Ebinop Oadd
                                        (Ebinop Oadd (Etempvar _i_sw tint)
                                          (Etempvar _nex tint) tint)
                                        (Econst_int (Int.repr 1) tint) tint)))))))))
                      (Sset _ix__1
                        (Ebinop Oadd (Etempvar _ix__1 tint)
                          (Econst_int (Int.repr 1) tint) tint)))))
                (Sset _iy__1
                  (Ebinop Oadd (Etempvar _iy__1 tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))))))))))
|}.

Definition f_mesh_block2d_P2 := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_nex, tint) :: (_ney, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nx, tint) :: (_ny, tint) ::
               (_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_iy, tint) ::
               (_ix, tint) :: (_i, tint) :: (_iy__1, tint) ::
               (_ix__1, tint) :: (_i__1, tint) :: (_i_sw, tint) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'12, (tptr tdouble)) :: (_t'11, (tptr tdouble)) ::
               (_t'10, (tptr tint)) :: (_t'9, (tptr tint)) ::
               (_t'8, (tptr tint)) :: (_t'7, (tptr tint)) ::
               (_t'6, (tptr tint)) :: (_t'5, (tptr tint)) ::
               (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _nx
    (Ebinop Oadd
      (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _nex tint) tint)
      (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _ny
      (Ebinop Oadd
        (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _ney tint)
          tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mesh_malloc (Tfunction (tint :: tint :: tint :: tint :: nil)
                               (tptr (Tstruct _mesh_t noattr)) cc_default))
          ((Econst_int (Int.repr 2) tint) ::
           (Ebinop Omul (Etempvar _nx tint) (Etempvar _ny tint) tint) ::
           (Econst_int (Int.repr 9) tint) ::
           (Ebinop Omul (Etempvar _nex tint) (Etempvar _ney tint) tint) ::
           nil))
        (Sset _mesh (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
              (Tstruct _mesh_t noattr)) _shape
            (tptr (Tfunction
                    ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) ::
                     nil) tint cc_default)))
          (Evar _shapes2dP2 (Tfunction
                              ((tptr tdouble) :: (tptr tdouble) ::
                               (tptr tdouble) :: nil) tint cc_default)))
        (Ssequence
          (Ssequence
            (Sset _iy (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _iy tint)
                               (Etempvar _ny tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _ix (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _ix tint)
                                     (Etempvar _nx tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _i
                          (Ebinop Oadd (Etempvar _ix tint)
                            (Ebinop Omul (Etempvar _iy tint)
                              (Etempvar _nx tint) tint) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'12
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'12 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 0) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _ix tint) tdouble)
                                (Ebinop Osub (Etempvar _nx tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble)))
                          (Ssequence
                            (Sset _t'11
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'11 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _iy tint) tdouble)
                                (Ebinop Osub (Etempvar _ny tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble))))))
                    (Sset _ix
                      (Ebinop Oadd (Etempvar _ix tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              (Sset _iy
                (Ebinop Oadd (Etempvar _iy tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _iy__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _iy__1 tint)
                                 (Etempvar _ney tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _ix__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _ix__1 tint)
                                       (Etempvar _nex tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _i__1
                            (Ebinop Oadd (Etempvar _ix__1 tint)
                              (Ebinop Omul (Etempvar _iy__1 tint)
                                (Etempvar _nex tint) tint) tint))
                          (Ssequence
                            (Sset _i_sw
                              (Ebinop Oadd
                                (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                  (Etempvar _ix__1 tint) tint)
                                (Ebinop Omul
                                  (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                    (Etempvar _iy__1 tint) tint)
                                  (Etempvar _nx tint) tint) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _elt
                                    (tptr tint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'10 (tptr tint))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 9) tint)
                                          (Etempvar _i__1 tint) tint)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      (tptr tint)) tint)
                                  (Etempvar _i_sw tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'9
                                    (Efield
                                      (Ederef
                                        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                        (Tstruct _mesh_t noattr)) _elt
                                      (tptr tint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'9 (tptr tint))
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 9) tint)
                                            (Etempvar _i__1 tint) tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) (tptr tint)) tint)
                                    (Ebinop Oadd (Etempvar _i_sw tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _elt
                                        (tptr tint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'8 (tptr tint))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 9) tint)
                                              (Etempvar _i__1 tint) tint)
                                            (Econst_int (Int.repr 2) tint)
                                            tint) (tptr tint)) tint)
                                      (Ebinop Oadd (Etempvar _i_sw tint)
                                        (Econst_int (Int.repr 2) tint) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'7
                                        (Efield
                                          (Ederef
                                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _elt
                                          (tptr tint)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'7 (tptr tint))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 9) tint)
                                                (Etempvar _i__1 tint) tint)
                                              (Econst_int (Int.repr 3) tint)
                                              tint) (tptr tint)) tint)
                                        (Ebinop Oadd
                                          (Ebinop Oadd (Etempvar _i_sw tint)
                                            (Econst_int (Int.repr 2) tint)
                                            tint) (Etempvar _nx tint) tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'6
                                          (Efield
                                            (Ederef
                                              (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                              (Tstruct _mesh_t noattr)) _elt
                                            (tptr tint)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'6 (tptr tint))
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 9) tint)
                                                  (Etempvar _i__1 tint) tint)
                                                (Econst_int (Int.repr 4) tint)
                                                tint) (tptr tint)) tint)
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Etempvar _i_sw tint)
                                              (Econst_int (Int.repr 2) tint)
                                              tint)
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 2) tint)
                                              (Etempvar _nx tint) tint) tint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'5
                                            (Efield
                                              (Ederef
                                                (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                (Tstruct _mesh_t noattr))
                                              _elt (tptr tint)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'5 (tptr tint))
                                                (Ebinop Oadd
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 9) tint)
                                                    (Etempvar _i__1 tint)
                                                    tint)
                                                  (Econst_int (Int.repr 5) tint)
                                                  tint) (tptr tint)) tint)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _i_sw tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 2) tint)
                                                (Etempvar _nx tint) tint)
                                              tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'4
                                              (Efield
                                                (Ederef
                                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                  (Tstruct _mesh_t noattr))
                                                _elt (tptr tint)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'4 (tptr tint))
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Econst_int (Int.repr 9) tint)
                                                      (Etempvar _i__1 tint)
                                                      tint)
                                                    (Econst_int (Int.repr 6) tint)
                                                    tint) (tptr tint)) tint)
                                              (Ebinop Oadd
                                                (Etempvar _i_sw tint)
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 2) tint)
                                                  (Etempvar _nx tint) tint)
                                                tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'3
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                    (Tstruct _mesh_t noattr))
                                                  _elt (tptr tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'3 (tptr tint))
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 9) tint)
                                                        (Etempvar _i__1 tint)
                                                        tint)
                                                      (Econst_int (Int.repr 7) tint)
                                                      tint) (tptr tint))
                                                  tint)
                                                (Ebinop Oadd
                                                  (Etempvar _i_sw tint)
                                                  (Etempvar _nx tint) tint)))
                                            (Ssequence
                                              (Sset _t'2
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                    (Tstruct _mesh_t noattr))
                                                  _elt (tptr tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'2 (tptr tint))
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 9) tint)
                                                        (Etempvar _i__1 tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) (tptr tint))
                                                  tint)
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Etempvar _i_sw tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (Etempvar _nx tint)
                                                  tint))))))))))))))
                      (Sset _ix__1
                        (Ebinop Oadd (Etempvar _ix__1 tint)
                          (Econst_int (Int.repr 1) tint) tint)))))
                (Sset _iy__1
                  (Ebinop Oadd (Etempvar _iy__1 tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))))))))))
|}.

Definition f_mesh_block2d_S2 := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_nex, tint) :: (_ney, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nx0, tint) :: (_nx1, tint) :: (_numnp, tint) ::
               (_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_iy, tint) ::
               (_start, tint) :: (_ix, tint) :: (_ix__1, tint) ::
               (_ix__2, tint) :: (_iy__1, tint) :: (_ix__3, tint) ::
               (_i, tint) :: (_i_sw, tint) :: (_i_ww, tint) ::
               (_i_nw, tint) :: (_t'1, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'15, (tptr tdouble)) :: (_t'14, (tptr tdouble)) ::
               (_t'13, (tptr tdouble)) :: (_t'12, (tptr tdouble)) ::
               (_t'11, (tptr tdouble)) :: (_t'10, (tptr tdouble)) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tint)) ::
               (_t'7, (tptr tint)) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) ::
               (_t'3, (tptr tint)) :: (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _nx0
    (Ebinop Oadd
      (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _nex tint) tint)
      (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _nx1
      (Ebinop Oadd (Etempvar _nex tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sset _numnp
        (Ebinop Oadd
          (Ebinop Omul
            (Ebinop Oadd (Etempvar _ney tint) (Econst_int (Int.repr 1) tint)
              tint) (Etempvar _nx0 tint) tint)
          (Ebinop Omul (Etempvar _ney tint) (Etempvar _nx1 tint) tint) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _mesh_malloc (Tfunction
                                 (tint :: tint :: tint :: tint :: nil)
                                 (tptr (Tstruct _mesh_t noattr)) cc_default))
            ((Econst_int (Int.repr 2) tint) :: (Etempvar _numnp tint) ::
             (Econst_int (Int.repr 8) tint) ::
             (Ebinop Omul (Etempvar _nex tint) (Etempvar _ney tint) tint) ::
             nil))
          (Sset _mesh (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _shape
              (tptr (Tfunction
                      ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) ::
                       nil) tint cc_default)))
            (Evar _shapes2dS2 (Tfunction
                                ((tptr tdouble) :: (tptr tdouble) ::
                                 (tptr tdouble) :: nil) tint cc_default)))
          (Ssequence
            (Ssequence
              (Sset _iy (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _iy tint)
                                 (Etempvar _ney tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _start
                      (Ebinop Omul (Etempvar _iy tint)
                        (Ebinop Oadd (Etempvar _nx0 tint)
                          (Etempvar _nx1 tint) tint) tint))
                    (Ssequence
                      (Ssequence
                        (Sset _ix (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _ix tint)
                                           (Etempvar _nx0 tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _X
                                    (tptr tdouble)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _t'15 (tptr tdouble))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 2) tint)
                                          (Ebinop Oadd (Etempvar _start tint)
                                            (Etempvar _ix tint) tint) tint)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      (tptr tdouble)) tdouble)
                                  (Ebinop Odiv
                                    (Ecast (Etempvar _ix tint) tdouble)
                                    (Ebinop Osub (Etempvar _nx0 tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tdouble)))
                              (Ssequence
                                (Sset _t'14
                                  (Efield
                                    (Ederef
                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _X
                                    (tptr tdouble)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _t'14 (tptr tdouble))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 2) tint)
                                          (Ebinop Oadd (Etempvar _start tint)
                                            (Etempvar _ix tint) tint) tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr tdouble)) tdouble)
                                  (Ebinop Odiv
                                    (Ecast (Etempvar _iy tint) tdouble)
                                    (Etempvar _ney tint) tdouble)))))
                          (Sset _ix
                            (Ebinop Oadd (Etempvar _ix tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Ssequence
                        (Sset _start
                          (Ebinop Oadd (Etempvar _start tint)
                            (Etempvar _nx0 tint) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _ix__1 (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _ix__1 tint)
                                               (Etempvar _nx1 tint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'13
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _X
                                        (tptr tdouble)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'13 (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 2) tint)
                                              (Ebinop Oadd
                                                (Etempvar _start tint)
                                                (Etempvar _ix__1 tint) tint)
                                              tint)
                                            (Econst_int (Int.repr 0) tint)
                                            tint) (tptr tdouble)) tdouble)
                                      (Ebinop Odiv
                                        (Ecast (Etempvar _ix__1 tint)
                                          tdouble)
                                        (Ebinop Osub (Etempvar _nx1 tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tdouble)))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _X
                                        (tptr tdouble)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'12 (tptr tdouble))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 2) tint)
                                              (Ebinop Oadd
                                                (Etempvar _start tint)
                                                (Etempvar _ix__1 tint) tint)
                                              tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (tptr tdouble)) tdouble)
                                      (Ebinop Odiv
                                        (Ebinop Oadd
                                          (Ecast (Etempvar _iy tint) tdouble)
                                          (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                                          tdouble) (Etempvar _ney tint)
                                        tdouble)))))
                              (Sset _ix__1
                                (Ebinop Oadd (Etempvar _ix__1 tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Sset _start
                              (Ebinop Oadd (Etempvar _start tint)
                                (Etempvar _nx1 tint) tint))
                            (Ssequence
                              (Sset _ix__2 (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _ix__2 tint)
                                                 (Etempvar _nx0 tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'11
                                        (Efield
                                          (Ederef
                                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _X
                                          (tptr tdouble)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'11 (tptr tdouble))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 2) tint)
                                                (Ebinop Oadd
                                                  (Etempvar _start tint)
                                                  (Etempvar _ix__2 tint)
                                                  tint) tint)
                                              (Econst_int (Int.repr 0) tint)
                                              tint) (tptr tdouble)) tdouble)
                                        (Ebinop Odiv
                                          (Ecast (Etempvar _ix__2 tint)
                                            tdouble)
                                          (Ebinop Osub (Etempvar _nx0 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) tdouble)))
                                    (Ssequence
                                      (Sset _t'10
                                        (Efield
                                          (Ederef
                                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _X
                                          (tptr tdouble)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'10 (tptr tdouble))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 2) tint)
                                                (Ebinop Oadd
                                                  (Etempvar _start tint)
                                                  (Etempvar _ix__2 tint)
                                                  tint) tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) (tptr tdouble)) tdouble)
                                        (Ebinop Odiv
                                          (Ebinop Oadd
                                            (Ecast (Etempvar _iy tint)
                                              tdouble)
                                            (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
                                            tdouble) (Etempvar _ney tint)
                                          tdouble)))))
                                (Sset _ix__2
                                  (Ebinop Oadd (Etempvar _ix__2 tint)
                                    (Econst_int (Int.repr 1) tint) tint))))))))))
                (Sset _iy
                  (Ebinop Oadd (Etempvar _iy tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Ssequence
                (Sset _iy__1 (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _iy__1 tint)
                                   (Etempvar _ney tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _ix__3 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _ix__3 tint)
                                         (Etempvar _nex tint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _i
                              (Ebinop Oadd (Etempvar _ix__3 tint)
                                (Ebinop Omul (Etempvar _iy__1 tint)
                                  (Etempvar _nex tint) tint) tint))
                            (Ssequence
                              (Sset _i_sw
                                (Ebinop Oadd
                                  (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                    (Etempvar _ix__3 tint) tint)
                                  (Ebinop Omul (Etempvar _iy__1 tint)
                                    (Ebinop Oadd (Etempvar _nx0 tint)
                                      (Etempvar _nx1 tint) tint) tint) tint))
                              (Ssequence
                                (Sset _i_ww
                                  (Ebinop Oadd
                                    (Ebinop Oadd (Etempvar _ix__3 tint)
                                      (Ebinop Omul (Etempvar _iy__1 tint)
                                        (Ebinop Oadd (Etempvar _nx0 tint)
                                          (Etempvar _nx1 tint) tint) tint)
                                      tint) (Etempvar _nx0 tint) tint))
                                (Ssequence
                                  (Sset _i_nw
                                    (Ebinop Oadd
                                      (Ebinop Oadd
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 2) tint)
                                            (Etempvar _ix__3 tint) tint)
                                          (Ebinop Omul (Etempvar _iy__1 tint)
                                            (Ebinop Oadd (Etempvar _nx0 tint)
                                              (Etempvar _nx1 tint) tint)
                                            tint) tint) (Etempvar _nx0 tint)
                                        tint) (Etempvar _nx1 tint) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _elt
                                          (tptr tint)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'9 (tptr tint))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 8) tint)
                                                (Etempvar _i tint) tint)
                                              (Econst_int (Int.repr 0) tint)
                                              tint) (tptr tint)) tint)
                                        (Etempvar _i_sw tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'8
                                          (Efield
                                            (Ederef
                                              (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                              (Tstruct _mesh_t noattr)) _elt
                                            (tptr tint)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'8 (tptr tint))
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 8) tint)
                                                  (Etempvar _i tint) tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tint)) tint)
                                          (Ebinop Oadd (Etempvar _i_sw tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Efield
                                              (Ederef
                                                (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                (Tstruct _mesh_t noattr))
                                              _elt (tptr tint)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'7 (tptr tint))
                                                (Ebinop Oadd
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 8) tint)
                                                    (Etempvar _i tint) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tint)) tint)
                                            (Ebinop Oadd
                                              (Etempvar _i_sw tint)
                                              (Econst_int (Int.repr 2) tint)
                                              tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'6
                                              (Efield
                                                (Ederef
                                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                  (Tstruct _mesh_t noattr))
                                                _elt (tptr tint)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'6 (tptr tint))
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Econst_int (Int.repr 8) tint)
                                                      (Etempvar _i tint)
                                                      tint)
                                                    (Econst_int (Int.repr 3) tint)
                                                    tint) (tptr tint)) tint)
                                              (Ebinop Oadd
                                                (Etempvar _i_ww tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'5
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                    (Tstruct _mesh_t noattr))
                                                  _elt (tptr tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'5 (tptr tint))
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 8) tint)
                                                        (Etempvar _i tint)
                                                        tint)
                                                      (Econst_int (Int.repr 4) tint)
                                                      tint) (tptr tint))
                                                  tint)
                                                (Ebinop Oadd
                                                  (Etempvar _i_nw tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'4
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                      (Tstruct _mesh_t noattr))
                                                    _elt (tptr tint)))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'4 (tptr tint))
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 8) tint)
                                                          (Etempvar _i tint)
                                                          tint)
                                                        (Econst_int (Int.repr 5) tint)
                                                        tint) (tptr tint))
                                                    tint)
                                                  (Ebinop Oadd
                                                    (Etempvar _i_nw tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'3
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                        (Tstruct _mesh_t noattr))
                                                      _elt (tptr tint)))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'3 (tptr tint))
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 8) tint)
                                                            (Etempvar _i tint)
                                                            tint)
                                                          (Econst_int (Int.repr 6) tint)
                                                          tint) (tptr tint))
                                                      tint)
                                                    (Etempvar _i_nw tint)))
                                                (Ssequence
                                                  (Sset _t'2
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                                        (Tstruct _mesh_t noattr))
                                                      _elt (tptr tint)))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'2 (tptr tint))
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 8) tint)
                                                            (Etempvar _i tint)
                                                            tint)
                                                          (Econst_int (Int.repr 7) tint)
                                                          tint) (tptr tint))
                                                      tint)
                                                    (Etempvar _i_ww tint)))))))))))))))
                        (Sset _ix__3
                          (Ebinop Oadd (Etempvar _ix__3 tint)
                            (Econst_int (Int.repr 1) tint) tint)))))
                  (Sset _iy__1
                    (Ebinop Oadd (Etempvar _iy__1 tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr))))))))))))
|}.

Definition f_mesh_block2d_T1 := {|
  fn_return := (tptr (Tstruct _mesh_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_nex, tint) :: (_ney, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nx, tint) :: (_ny, tint) ::
               (_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_iy, tint) ::
               (_ix, tint) :: (_i, tint) :: (_iy__1, tint) ::
               (_ix__1, tint) :: (_i__1, tint) :: (_i_sw, tint) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'9, (tptr tdouble)) :: (_t'8, (tptr tdouble)) ::
               (_t'7, (tptr tint)) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) ::
               (_t'3, (tptr tint)) :: (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _nx
    (Ebinop Oadd (Etempvar _nex tint) (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _ny
      (Ebinop Oadd (Etempvar _ney tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mesh_malloc (Tfunction (tint :: tint :: tint :: tint :: nil)
                               (tptr (Tstruct _mesh_t noattr)) cc_default))
          ((Econst_int (Int.repr 2) tint) ::
           (Ebinop Omul (Etempvar _nx tint) (Etempvar _ny tint) tint) ::
           (Econst_int (Int.repr 3) tint) ::
           (Ebinop Omul
             (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _nex tint)
               tint) (Etempvar _ney tint) tint) :: nil))
        (Sset _mesh (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
              (Tstruct _mesh_t noattr)) _shape
            (tptr (Tfunction
                    ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) ::
                     nil) tint cc_default)))
          (Evar _shapes2dT1 (Tfunction
                              ((tptr tdouble) :: (tptr tdouble) ::
                               (tptr tdouble) :: nil) tint cc_default)))
        (Ssequence
          (Ssequence
            (Sset _iy (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _iy tint)
                               (Ebinop Oadd (Etempvar _ney tint)
                                 (Econst_int (Int.repr 1) tint) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _ix (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _ix tint)
                                     (Ebinop Oadd (Etempvar _nex tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                                     tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _i
                          (Ebinop Oadd (Etempvar _ix tint)
                            (Ebinop Omul (Etempvar _iy tint)
                              (Ebinop Oadd (Etempvar _nex tint)
                                (Econst_int (Int.repr 1) tint) tint) tint)
                            tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'9 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 0) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _ix tint) tdouble)
                                (Ebinop Osub (Etempvar _nx tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble)))
                          (Ssequence
                            (Sset _t'8
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _X
                                (tptr tdouble)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'8 (tptr tdouble))
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Etempvar _i tint) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr tdouble)) tdouble)
                              (Ebinop Odiv
                                (Ecast (Etempvar _iy tint) tdouble)
                                (Ebinop Osub (Etempvar _ny tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                tdouble))))))
                    (Sset _ix
                      (Ebinop Oadd (Etempvar _ix tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              (Sset _iy
                (Ebinop Oadd (Etempvar _iy tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _iy__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _iy__1 tint)
                                 (Etempvar _ney tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _ix__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _ix__1 tint)
                                       (Etempvar _nex tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _i__1
                            (Ebinop Oadd (Etempvar _ix__1 tint)
                              (Ebinop Omul (Etempvar _iy__1 tint)
                                (Etempvar _nex tint) tint) tint))
                          (Ssequence
                            (Sset _i_sw
                              (Ebinop Oadd (Etempvar _ix__1 tint)
                                (Ebinop Omul (Etempvar _iy__1 tint)
                                  (Ebinop Oadd (Etempvar _nex tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _elt
                                    (tptr tint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'7 (tptr tint))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 6) tint)
                                          (Etempvar _i__1 tint) tint)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      (tptr tint)) tint)
                                  (Etempvar _i_sw tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Ederef
                                        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                        (Tstruct _mesh_t noattr)) _elt
                                      (tptr tint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'6 (tptr tint))
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 6) tint)
                                            (Etempvar _i__1 tint) tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) (tptr tint)) tint)
                                    (Ebinop Oadd (Etempvar _i_sw tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'5
                                      (Efield
                                        (Ederef
                                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                          (Tstruct _mesh_t noattr)) _elt
                                        (tptr tint)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'5 (tptr tint))
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 6) tint)
                                              (Etempvar _i__1 tint) tint)
                                            (Econst_int (Int.repr 2) tint)
                                            tint) (tptr tint)) tint)
                                      (Ebinop Oadd
                                        (Ebinop Oadd (Etempvar _i_sw tint)
                                          (Etempvar _nex tint) tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'4
                                        (Efield
                                          (Ederef
                                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _elt
                                          (tptr tint)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'4 (tptr tint))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 6) tint)
                                                (Etempvar _i__1 tint) tint)
                                              (Econst_int (Int.repr 3) tint)
                                              tint) (tptr tint)) tint)
                                        (Ebinop Oadd
                                          (Ebinop Oadd (Etempvar _i_sw tint)
                                            (Etempvar _nex tint) tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'3
                                          (Efield
                                            (Ederef
                                              (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                              (Tstruct _mesh_t noattr)) _elt
                                            (tptr tint)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'3 (tptr tint))
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 6) tint)
                                                  (Etempvar _i__1 tint) tint)
                                                (Econst_int (Int.repr 4) tint)
                                                tint) (tptr tint)) tint)
                                          (Ebinop Oadd (Etempvar _i_sw tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))
                                      (Ssequence
                                        (Sset _t'2
                                          (Efield
                                            (Ederef
                                              (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                              (Tstruct _mesh_t noattr)) _elt
                                            (tptr tint)))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'2 (tptr tint))
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 6) tint)
                                                  (Etempvar _i__1 tint) tint)
                                                (Econst_int (Int.repr 5) tint)
                                                tint) (tptr tint)) tint)
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _i_sw tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (Etempvar _nex tint)
                                              tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))))))))))
                      (Sset _ix__1
                        (Ebinop Oadd (Etempvar _ix__1 tint)
                          (Econst_int (Int.repr 1) tint) tint)))))
                (Sset _iy__1
                  (Ebinop Oadd (Etempvar _iy__1 tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))))))))))
|}.

Definition f_mesh_to_spatial := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_eltid, tint) ::
                (_xref, (tptr tdouble)) :: (_x, (tptr tdouble)) ::
                (_ipiv, (tptr tint)) :: (_J, (tptr tdouble)) ::
                (_N, (tptr tdouble)) :: (_dN, (tptr tdouble)) :: nil);
  fn_vars := ((_dNk, (tarray tdouble 3)) :: nil);
  fn_temps := ((_d, tint) :: (_elt, (tptr tint)) :: (_X, (tptr tdouble)) ::
               (_nshape, tint) :: (_k, tint) :: (_i, tint) ::
               (_k__1, tint) :: (_j, tint) :: (_i__1, tint) ::
               (_k__2, tint) :: (_j__1, tint) :: (_j__2, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'17, tint) :: (_t'16, (tptr tint)) ::
               (_t'15,
                (tptr (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))) ::
               (_t'14, tdouble) :: (_t'13, tdouble) :: (_t'12, tint) ::
               (_t'11, tdouble) :: (_t'10, tdouble) :: (_t'9, tdouble) ::
               (_t'8, tint) :: (_t'7, tdouble) :: (_t'6, tdouble) ::
               (_t'5, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _d
    (Efield
      (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
        (Tstruct _mesh_t noattr)) _d tint))
  (Ssequence
    (Ssequence
      (Sset _t'16
        (Efield
          (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _elt (tptr tint)))
      (Ssequence
        (Sset _t'17
          (Efield
            (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
              (Tstruct _mesh_t noattr)) _nen tint))
        (Sset _elt
          (Ebinop Oadd (Etempvar _t'16 (tptr tint))
            (Ebinop Omul (Etempvar _t'17 tint) (Etempvar _eltid tint) tint)
            (tptr tint)))))
    (Ssequence
      (Sset _X
        (Efield
          (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _X (tptr tdouble)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'15
              (Efield
                (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                  (Tstruct _mesh_t noattr)) _shape
                (tptr (Tfunction
                        ((tptr tdouble) :: (tptr tdouble) ::
                         (tptr tdouble) :: nil) tint cc_default))))
            (Scall (Some _t'1)
              (Ederef
                (Etempvar _t'15 (tptr (Tfunction
                                        ((tptr tdouble) :: (tptr tdouble) ::
                                         (tptr tdouble) :: nil) tint
                                        cc_default)))
                (Tfunction
                  ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil)
                  tint cc_default))
              ((Etempvar _N (tptr tdouble)) ::
               (Etempvar _dN (tptr tdouble)) ::
               (Etempvar _xref (tptr tdouble)) :: nil)))
          (Sset _nshape (Etempvar _t'1 tint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _x (tptr tdouble))
              (Sset _t'2 (Ecast (Etempvar _N (tptr tdouble)) tbool))
              (Sset _t'2 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'2 tint)
              (Ssequence
                (Scall None
                  (Evar _double_clear (Tfunction
                                        ((tptr tdouble) :: tint :: nil) tvoid
                                        cc_default))
                  ((Etempvar _x (tptr tdouble)) :: (Etempvar _d tint) :: nil))
                (Ssequence
                  (Sset _k (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                                     (Etempvar _nshape tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _i (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                           (Etempvar _d tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'11
                                (Ederef
                                  (Ebinop Oadd (Etempvar _x (tptr tdouble))
                                    (Etempvar _i tint) (tptr tdouble))
                                  tdouble))
                              (Ssequence
                                (Sset _t'12
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _elt (tptr tint))
                                      (Etempvar _k tint) (tptr tint)) tint))
                                (Ssequence
                                  (Sset _t'13
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _X (tptr tdouble))
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Ebinop Omul (Etempvar _d tint)
                                            (Etempvar _t'12 tint) tint) tint)
                                        (tptr tdouble)) tdouble))
                                  (Ssequence
                                    (Sset _t'14
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _N (tptr tdouble))
                                          (Etempvar _k tint) (tptr tdouble))
                                        tdouble))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x (tptr tdouble))
                                          (Etempvar _i tint) (tptr tdouble))
                                        tdouble)
                                      (Ebinop Oadd (Etempvar _t'11 tdouble)
                                        (Ebinop Omul (Etempvar _t'13 tdouble)
                                          (Etempvar _t'14 tdouble) tdouble)
                                        tdouble)))))))
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint)))))
                    (Sset _k
                      (Ebinop Oadd (Etempvar _k tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              Sskip))
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _ipiv (tptr tint))
                (Sset _t'3 (Ecast (Etempvar _J (tptr tdouble)) tbool))
                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'3 tint)
                (Sset _t'4 (Ecast (Etempvar _dN (tptr tdouble)) tbool))
                (Sset _t'4 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Scall None
                  (Evar _densematn_clear (Tfunction
                                           ((tptr tdouble) :: tint :: tint ::
                                            nil) tvoid cc_default))
                  ((Etempvar _J (tptr tdouble)) :: (Etempvar _d tint) ::
                   (Etempvar _d tint) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _k__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _k__1 tint)
                                       (Etempvar _nshape tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _j (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                             (Etempvar _d tint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _i__1 (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i__1 tint)
                                                   (Etempvar _d tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _J (tptr tdouble))
                                            (Ebinop Oadd
                                              (Etempvar _i__1 tint)
                                              (Ebinop Omul (Etempvar _j tint)
                                                (Etempvar _d tint) tint)
                                              tint) (tptr tdouble)) tdouble))
                                      (Ssequence
                                        (Sset _t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _elt (tptr tint))
                                              (Etempvar _k__1 tint)
                                              (tptr tint)) tint))
                                        (Ssequence
                                          (Sset _t'9
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _X (tptr tdouble))
                                                (Ebinop Oadd
                                                  (Etempvar _i__1 tint)
                                                  (Ebinop Omul
                                                    (Etempvar _d tint)
                                                    (Etempvar _t'8 tint)
                                                    tint) tint)
                                                (tptr tdouble)) tdouble))
                                          (Ssequence
                                            (Sset _t'10
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _dN (tptr tdouble))
                                                  (Ebinop Oadd
                                                    (Etempvar _k__1 tint)
                                                    (Ebinop Omul
                                                      (Etempvar _j tint)
                                                      (Etempvar _nshape tint)
                                                      tint) tint)
                                                  (tptr tdouble)) tdouble))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _J (tptr tdouble))
                                                  (Ebinop Oadd
                                                    (Etempvar _i__1 tint)
                                                    (Ebinop Omul
                                                      (Etempvar _j tint)
                                                      (Etempvar _d tint)
                                                      tint) tint)
                                                  (tptr tdouble)) tdouble)
                                              (Ebinop Oadd
                                                (Etempvar _t'7 tdouble)
                                                (Ebinop Omul
                                                  (Etempvar _t'9 tdouble)
                                                  (Etempvar _t'10 tdouble)
                                                  tdouble) tdouble)))))))
                                  (Sset _i__1
                                    (Ebinop Oadd (Etempvar _i__1 tint)
                                      (Econst_int (Int.repr 1) tint) tint)))))
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tint)
                                (Econst_int (Int.repr 1) tint) tint)))))
                      (Sset _k__1
                        (Ebinop Oadd (Etempvar _k__1 tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Scall None
                      (Evar _densematn_lufactor (Tfunction
                                                  ((tptr tint) ::
                                                   (tptr tdouble) :: tint ::
                                                   nil) tvoid cc_default))
                      ((Etempvar _ipiv (tptr tint)) ::
                       (Etempvar _J (tptr tdouble)) :: (Etempvar _d tint) ::
                       nil))
                    (Ssequence
                      (Sset _k__2 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _k__2 tint)
                                         (Etempvar _nshape tint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _j__1 (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _j__1 tint)
                                                 (Etempvar _d tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _dN (tptr tdouble))
                                          (Ebinop Oadd (Etempvar _k__2 tint)
                                            (Ebinop Omul
                                              (Etempvar _j__1 tint)
                                              (Etempvar _nshape tint) tint)
                                            tint) (tptr tdouble)) tdouble))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _dNk (tarray tdouble 3))
                                          (Etempvar _j__1 tint)
                                          (tptr tdouble)) tdouble)
                                      (Etempvar _t'6 tdouble))))
                                (Sset _j__1
                                  (Ebinop Oadd (Etempvar _j__1 tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Scall None
                                (Evar _densematn_lusolveT (Tfunction
                                                            ((tptr tint) ::
                                                             (tptr tdouble) ::
                                                             (tptr tdouble) ::
                                                             tint :: nil)
                                                            tvoid cc_default))
                                ((Etempvar _ipiv (tptr tint)) ::
                                 (Etempvar _J (tptr tdouble)) ::
                                 (Evar _dNk (tarray tdouble 3)) ::
                                 (Etempvar _d tint) :: nil))
                              (Ssequence
                                (Sset _j__2 (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j__2 tint)
                                                   (Etempvar _d tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'5
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _dNk (tarray tdouble 3))
                                            (Etempvar _j__2 tint)
                                            (tptr tdouble)) tdouble))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _dN (tptr tdouble))
                                            (Ebinop Oadd
                                              (Etempvar _k__2 tint)
                                              (Ebinop Omul
                                                (Etempvar _j__2 tint)
                                                (Etempvar _nshape tint) tint)
                                              tint) (tptr tdouble)) tdouble)
                                        (Etempvar _t'5 tdouble))))
                                  (Sset _j__2
                                    (Ebinop Oadd (Etempvar _j__2 tint)
                                      (Econst_int (Int.repr 1) tint) tint)))))))
                        (Sset _k__2
                          (Ebinop Oadd (Etempvar _k__2 tint)
                            (Econst_int (Int.repr 1) tint) tint)))))))
              Sskip)))))))
|}.

Definition f_mesh_shapes := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_eltid, tint) ::
                (_x, (tptr tdouble)) :: (_N, (tptr tdouble)) ::
                (_dN, (tptr tdouble)) :: nil);
  fn_vars := ((_ipiv, (tarray tint 3)) :: (_J, (tarray tdouble 9)) ::
              (_xout, (tarray tdouble 3)) :: nil);
  fn_temps := ((_d, tint) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _d
    (Efield
      (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
        (Tstruct _mesh_t noattr)) _d tint))
  (Ssequence
    (Scall None
      (Evar _mesh_to_spatial (Tfunction
                               ((tptr (Tstruct _mesh_t noattr)) :: tint ::
                                (tptr tdouble) :: (tptr tdouble) ::
                                (tptr tint) :: (tptr tdouble) ::
                                (tptr tdouble) :: (tptr tdouble) :: nil)
                               tvoid cc_default))
      ((Etempvar _mesh (tptr (Tstruct _mesh_t noattr))) ::
       (Etempvar _eltid tint) :: (Etempvar _x (tptr tdouble)) ::
       (Evar _xout (tarray tdouble 3)) :: (Evar _ipiv (tarray tint 3)) ::
       (Evar _J (tarray tdouble 9)) :: (Etempvar _N (tptr tdouble)) ::
       (Etempvar _dN (tptr tdouble)) :: nil))
    (Ssequence
      (Scall None
        (Evar _memcpy (Tfunction
                        ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                        (tptr tvoid) cc_default))
        ((Etempvar _x (tptr tdouble)) :: (Evar _xout (tarray tdouble 3)) ::
         (Ebinop Omul (Etempvar _d tint) (Esizeof tdouble tulong) tulong) ::
         nil))
      (Ssequence
        (Sifthenelse (Etempvar _dN (tptr tdouble))
          (Ssequence
            (Scall (Some _t'2)
              (Evar _densematn_lujac (Tfunction
                                       ((tptr tint) :: (tptr tdouble) ::
                                        tint :: nil) tdouble cc_default))
              ((Evar _ipiv (tarray tint 3)) ::
               (Evar _J (tarray tdouble 9)) :: (Etempvar _d tint) :: nil))
            (Sset _t'1 (Ecast (Etempvar _t'2 tdouble) tdouble)))
          (Sset _t'1
            (Ecast (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
              tdouble)))
        (Sreturn (Some (Etempvar _t'1 tdouble)))))))
|}.

Definition f_mesh_print_nodes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tint) :: (_i, tint) :: (_Xi, (tptr tdouble)) ::
               (_j__1, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (tptr tdouble)) :: (_t'2, tint) ::
               (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_4 (tarray tschar 19)) :: nil))
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_5 (tarray tschar 7)) :: nil))
    (Ssequence
      (Ssequence
        (Sset _j (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                    (Tstruct _mesh_t noattr)) _d tint))
              (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                             (Etempvar _t'6 tint) tint)
                Sskip
                Sbreak))
            (Scall None
              (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_6 (tarray tschar 9)) ::
               (Etempvar _j tint) :: nil)))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_7 (tarray tschar 2)) :: nil))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                      (Tstruct _mesh_t noattr)) _numnp tint))
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _t'5 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_8 (tarray tschar 7)) ::
                   (Etempvar _i tint) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                          (Tstruct _mesh_t noattr)) _X (tptr tdouble)))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                            (Tstruct _mesh_t noattr)) _d tint))
                      (Sset _Xi
                        (Ebinop Oadd (Etempvar _t'3 (tptr tdouble))
                          (Ebinop Omul (Etempvar _t'4 tint)
                            (Etempvar _i tint) tint) (tptr tdouble)))))
                  (Ssequence
                    (Ssequence
                      (Sset _j__1 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Sset _t'2
                              (Efield
                                (Ederef
                                  (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                                  (Tstruct _mesh_t noattr)) _d tint))
                            (Sifthenelse (Ebinop Olt (Etempvar _j__1 tint)
                                           (Etempvar _t'2 tint) tint)
                              Sskip
                              Sbreak))
                          (Ssequence
                            (Sset _t'1
                              (Ederef
                                (Ebinop Oadd (Etempvar _Xi (tptr tdouble))
                                  (Etempvar _j__1 tint) (tptr tdouble))
                                tdouble))
                            (Scall None
                              (Evar _printf (Tfunction ((tptr tschar) :: nil)
                                              tint
                                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                              ((Evar ___stringlit_9 (tarray tschar 7)) ::
                               (Etempvar _t'1 tdouble) :: nil))))
                        (Sset _j__1
                          (Ebinop Oadd (Etempvar _j__1 tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Scall None
                      (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                      ((Evar ___stringlit_7 (tarray tschar 2)) :: nil))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_mesh_print_elt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_10 (tarray tschar 24)) :: nil))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _numelt tint))
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _t'5 tint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Scall None
            (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_11 (tarray tschar 7)) ::
             (Etempvar _i tint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _j (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield
                        (Ederef
                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                          (Tstruct _mesh_t noattr)) _nen tint))
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Etempvar _t'4 tint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sset _t'1
                      (Efield
                        (Ederef
                          (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                          (Tstruct _mesh_t noattr)) _elt (tptr tint)))
                    (Ssequence
                      (Sset _t'2
                        (Efield
                          (Ederef
                            (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
                            (Tstruct _mesh_t noattr)) _nen tint))
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                              (Ebinop Oadd (Etempvar _j tint)
                                (Ebinop Omul (Etempvar _i tint)
                                  (Etempvar _t'2 tint) tint) tint)
                              (tptr tint)) tint))
                        (Scall None
                          (Evar _printf (Tfunction ((tptr tschar) :: nil)
                                          tint
                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_12 (tarray tschar 7)) ::
                           (Etempvar _t'3 tint) :: nil))))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Scall None
              (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_7 (tarray tschar 2)) :: nil)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_mesh_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _mesh_print_nodes (Tfunction
                              ((tptr (Tstruct _mesh_t noattr)) :: nil) tvoid
                              cc_default))
    ((Etempvar _mesh (tptr (Tstruct _mesh_t noattr))) :: nil))
  (Scall None
    (Evar _mesh_print_elt (Tfunction ((tptr (Tstruct _mesh_t noattr)) :: nil)
                            tvoid cc_default))
    ((Etempvar _mesh (tptr (Tstruct _mesh_t noattr))) :: nil)))
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
     cc_default)) :: (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
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
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_double_calloc,
   Gfun(External (EF_external "double_calloc"
                   (mksignature (AST.Xint :: nil) AST.Xptr cc_default))
     (tint :: nil) (tptr tdouble) cc_default)) ::
 (_int_calloc,
   Gfun(External (EF_external "int_calloc"
                   (mksignature (AST.Xint :: nil) AST.Xptr cc_default))
     (tint :: nil) (tptr tint) cc_default)) ::
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
 (_densematn_lufactor,
   Gfun(External (EF_external "densematn_lufactor"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tint) :: (tptr tdouble) :: tint :: nil) tvoid cc_default)) ::
 (_densematn_lusolveT,
   Gfun(External (EF_external "densematn_lusolveT"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tint) :: (tptr tdouble) :: (tptr tdouble) :: tint :: nil) tvoid
     cc_default)) ::
 (_densematn_lujac,
   Gfun(External (EF_external "densematn_lujac"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xfloat cc_default))
     ((tptr tint) :: (tptr tdouble) :: tint :: nil) tdouble cc_default)) ::
 (_shapes1dP1,
   Gfun(External (EF_external "shapes1dP1"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_shapes1dP2,
   Gfun(External (EF_external "shapes1dP2"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
 (_shapes1dP3,
   Gfun(External (EF_external "shapes1dP3"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tdouble) :: (tptr tdouble) :: (tptr tdouble) :: nil) tint
     cc_default)) ::
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
     cc_default)) :: (_mesh_malloc, Gfun(Internal f_mesh_malloc)) ::
 (_mesh_free, Gfun(Internal f_mesh_free)) ::
 (_mesh_create1d, Gfun(Internal f_mesh_create1d)) ::
 (_mesh_block2d_P1, Gfun(Internal f_mesh_block2d_P1)) ::
 (_mesh_block2d_P2, Gfun(Internal f_mesh_block2d_P2)) ::
 (_mesh_block2d_S2, Gfun(Internal f_mesh_block2d_S2)) ::
 (_mesh_block2d_T1, Gfun(Internal f_mesh_block2d_T1)) ::
 (_mesh_to_spatial, Gfun(Internal f_mesh_to_spatial)) ::
 (_mesh_shapes, Gfun(Internal f_mesh_shapes)) ::
 (_mesh_print_nodes, Gfun(Internal f_mesh_print_nodes)) ::
 (_mesh_print_elt, Gfun(Internal f_mesh_print_elt)) ::
 (_mesh_print, Gfun(Internal f_mesh_print)) :: nil).

Definition public_idents : list ident :=
(_mesh_print :: _mesh_print_elt :: _mesh_print_nodes :: _mesh_shapes ::
 _mesh_to_spatial :: _mesh_block2d_T1 :: _mesh_block2d_S2 ::
 _mesh_block2d_P2 :: _mesh_block2d_P1 :: _mesh_create1d :: _mesh_free ::
 _mesh_malloc :: _shapes2dT1 :: _shapes2dS2 :: _shapes2dP2 :: _shapes2dP1 ::
 _shapes1dP3 :: _shapes1dP2 :: _shapes1dP1 :: _densematn_lujac ::
 _densematn_lusolveT :: _densematn_lufactor :: _densematn_clear ::
 _double_clear :: _int_calloc :: _double_calloc :: _surely_malloc ::
 _memcpy :: _abort :: _free :: _printf :: ___builtin_debug ::
 ___builtin_fmin :: ___builtin_fmax :: ___builtin_fnmsub ::
 ___builtin_fnmadd :: ___builtin_fmsub :: ___builtin_fmadd ::
 ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
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


