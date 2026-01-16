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
  Definition source_file := "../src/fem.c".
  Definition normalized := true.
End Info.

Definition _F : ident := $"F".
Definition _K : ident := $"K".
Definition _Ke : ident := $"Ke".
Definition _Kmatrix : ident := $"Kmatrix".
Definition _R : ident := $"R".
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
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition _add : ident := $"add".
Definition _assemble_matrix : ident := $"assemble_matrix".
Definition _assemble_vector : ident := $"assemble_vector".
Definition _b : ident := $"b".
Definition _bandmat_t : ident := $"bandmat_t".
Definition _clear : ident := $"clear".
Definition _d : ident := $"d".
Definition _dR : ident := $"dR".
Definition _data : ident := $"data".
Definition _densemat_t : ident := $"densemat_t".
Definition _densematn_get : ident := $"densematn_get".
Definition _double_calloc : ident := $"double_calloc".
Definition _du_red : ident := $"du_red".
Definition _element_dR : ident := $"element_dR".
Definition _element_t : ident := $"element_t".
Definition _elt : ident := $"elt".
Definition _emat : ident := $"emat".
Definition _etype : ident := $"etype".
Definition _f : ident := $"f".
Definition _fe : ident := $"fe".
Definition _fem_assemble : ident := $"fem_assemble".
Definition _fem_assemble_band : ident := $"fem_assemble_band".
Definition _fem_assemble_dense : ident := $"fem_assemble_dense".
Definition _fem_assign_ids : ident := $"fem_assign_ids".
Definition _fem_free : ident := $"fem_free".
Definition _fem_malloc : ident := $"fem_malloc".
Definition _fem_print : ident := $"fem_print".
Definition _fem_set_load : ident := $"fem_set_load".
Definition _fem_t : ident := $"fem_t".
Definition _fem_update_U : ident := $"fem_update_U".
Definition _free : ident := $"free".
Definition _i : ident := $"i".
Definition _id : ident := $"id".
Definition _ids : ident := $"ids".
Definition _ie : ident := $"ie".
Definition _init_matrix_band : ident := $"init_matrix_band".
Definition _init_matrix_dense : ident := $"init_matrix_dense".
Definition _int_calloc : ident := $"int_calloc".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _j__2 : ident := $"j__2".
Definition _j__3 : ident := $"j__3".
Definition _j__4 : ident := $"j__4".
Definition _j__5 : ident := $"j__5".
Definition _je : ident := $"je".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _matrix_add : ident := $"matrix_add".
Definition _matrix_clear : ident := $"matrix_clear".
Definition _matrix_data_t : ident := $"matrix_data_t".
Definition _matrix_t : ident := $"matrix_t".
Definition _memset : ident := $"memset".
Definition _mesh : ident := $"mesh".
Definition _mesh_free : ident := $"mesh_free".
Definition _mesh_print_elt : ident := $"mesh_print_elt".
Definition _mesh_t : ident := $"mesh_t".
Definition _n : ident := $"n".
Definition _nactive : ident := $"nactive".
Definition _ndof : ident := $"ndof".
Definition _ne : ident := $"ne".
Definition _nen : ident := $"nen".
Definition _next_id : ident := $"next_id".
Definition _norm2 : ident := $"norm2".
Definition _numelt : ident := $"numelt".
Definition _numnp : ident := $"numnp".
Definition _p : ident := $"p".
Definition _print : ident := $"print".
Definition _printf : ident := $"printf".
Definition _shape : ident := $"shape".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _v : ident := $"v".
Definition _ve : ident := $"ve".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 12);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fem_malloc := {|
  fn_return := (tptr (Tstruct _fem_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_mesh, (tptr (Tstruct _mesh_t noattr))) :: (_ndof, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_numnp, tint) :: (_fe, (tptr (Tstruct _fem_t noattr))) ::
               (_t'4, (tptr tint)) :: (_t'3, (tptr tdouble)) ::
               (_t'2, (tptr tdouble)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _numnp
    (Efield
      (Ederef (Etempvar _mesh (tptr (Tstruct _mesh_t noattr)))
        (Tstruct _mesh_t noattr)) _numnp tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _fem_t noattr) tulong) :: nil))
      (Sset _fe (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr)))
        (Etempvar _mesh (tptr (Tstruct _mesh_t noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
              (Tstruct _fem_t noattr)) _etype
            (tptr (Tstruct _element_t noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _ndof tint) (Etempvar _ndof tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                  (Tstruct _fem_t noattr)) _nactive tint)
              (Ebinop Omul (Etempvar _numnp tint) (Etempvar _ndof tint) tint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _double_calloc (Tfunction (tint :: nil)
                                         (tptr tdouble) cc_default))
                  ((Ebinop Omul (Etempvar _ndof tint) (Etempvar _numnp tint)
                     tint) :: nil))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                      (Tstruct _fem_t noattr)) _U (tptr tdouble))
                  (Etempvar _t'2 (tptr tdouble))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _double_calloc (Tfunction (tint :: nil)
                                           (tptr tdouble) cc_default))
                    ((Ebinop Omul (Etempvar _ndof tint)
                       (Etempvar _numnp tint) tint) :: nil))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                        (Tstruct _fem_t noattr)) _F (tptr tdouble))
                    (Etempvar _t'3 (tptr tdouble))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _int_calloc (Tfunction (tint :: nil) (tptr tint)
                                          cc_default))
                      ((Ebinop Omul (Etempvar _ndof tint)
                         (Etempvar _numnp tint) tint) :: nil))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                          (Tstruct _fem_t noattr)) _id (tptr tint))
                      (Etempvar _t'4 (tptr tint))))
                  (Sreturn (Some (Etempvar _fe (tptr (Tstruct _fem_t noattr))))))))))))))
|}.

Definition f_fem_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, (tptr tint)) :: (_t'3, (tptr tdouble)) ::
               (_t'2, (tptr tdouble)) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _id (tptr tint)))
    (Scall None
      (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _t'4 (tptr tint)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _F (tptr tdouble)))
      (Scall None
        (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _t'3 (tptr tdouble)) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
              (Tstruct _fem_t noattr)) _U (tptr tdouble)))
        (Scall None
          (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _t'2 (tptr tdouble)) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _mesh
              (tptr (Tstruct _mesh_t noattr))))
          (Scall None
            (Evar _mesh_free (Tfunction
                               ((tptr (Tstruct _mesh_t noattr)) :: nil) tvoid
                               cc_default))
            ((Etempvar _t'1 (tptr (Tstruct _mesh_t noattr))) :: nil)))
        (Scall None
          (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _fe (tptr (Tstruct _fem_t noattr))) :: nil))))))
|}.

Definition f_fem_assign_ids := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_numnp, tint) :: (_ndof, tint) :: (_id, (tptr tint)) ::
               (_next_id, tint) :: (_i, tint) :: (_j, tint) ::
               (_t'1, tint) :: (_t'3, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
    (Sset _numnp
      (Efield
        (Ederef (Etempvar _t'3 (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _numnp tint)))
  (Ssequence
    (Sset _ndof
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _ndof tint))
    (Ssequence
      (Sset _id
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _id (tptr tint)))
      (Ssequence
        (Sset _next_id (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _numnp tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                     (Etempvar _ndof tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'2
                          (Ederef
                            (Ebinop Oadd (Etempvar _id (tptr tint))
                              (Ebinop Oadd (Etempvar _j tint)
                                (Ebinop Omul (Etempvar _i tint)
                                  (Etempvar _ndof tint) tint) tint)
                              (tptr tint)) tint))
                        (Sifthenelse (Ebinop Oge (Etempvar _t'2 tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'1 (Etempvar _next_id tint))
                              (Sset _next_id
                                (Ebinop Oadd (Etempvar _t'1 tint)
                                  (Econst_int (Int.repr 1) tint) tint)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _id (tptr tint))
                                  (Ebinop Oadd (Etempvar _j tint)
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _ndof tint) tint) tint)
                                  (tptr tint)) tint) (Etempvar _t'1 tint)))
                          Sskip)))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                  (Tstruct _fem_t noattr)) _nactive tint)
              (Etempvar _next_id tint))
            (Sreturn (Some (Etempvar _next_id tint)))))))))
|}.

Definition f_fem_update_U := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) ::
                (_du_red, (tptr tdouble)) :: nil);
  fn_vars := nil;
  fn_temps := ((_U, (tptr tdouble)) :: (_id, (tptr tint)) :: (_ndof, tint) ::
               (_numnp, tint) :: (_i, tint) :: (_j, tint) ::
               (_t'5, (tptr (Tstruct _mesh_t noattr))) :: (_t'4, tdouble) ::
               (_t'3, tint) :: (_t'2, tdouble) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _U
    (Efield
      (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
        (Tstruct _fem_t noattr)) _U (tptr tdouble)))
  (Ssequence
    (Sset _id
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _id (tptr tint)))
    (Ssequence
      (Sset _ndof
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _ndof tint))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _mesh
              (tptr (Tstruct _mesh_t noattr))))
          (Sset _numnp
            (Efield
              (Ederef (Etempvar _t'5 (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _numnp tint)))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _numnp tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _j (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Etempvar _ndof tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'1
                        (Ederef
                          (Ebinop Oadd (Etempvar _id (tptr tint))
                            (Ebinop Oadd (Etempvar _j tint)
                              (Ebinop Omul (Etempvar _i tint)
                                (Etempvar _ndof tint) tint) tint)
                            (tptr tint)) tint))
                      (Sifthenelse (Ebinop Oge (Etempvar _t'1 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                          (Sset _t'2
                            (Ederef
                              (Ebinop Oadd (Etempvar _U (tptr tdouble))
                                (Ebinop Oadd (Etempvar _j tint)
                                  (Ebinop Omul (Etempvar _i tint)
                                    (Etempvar _ndof tint) tint) tint)
                                (tptr tdouble)) tdouble))
                          (Ssequence
                            (Sset _t'3
                              (Ederef
                                (Ebinop Oadd (Etempvar _id (tptr tint))
                                  (Ebinop Oadd (Etempvar _j tint)
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _ndof tint) tint) tint)
                                  (tptr tint)) tint))
                            (Ssequence
                              (Sset _t'4
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _du_red (tptr tdouble))
                                    (Etempvar _t'3 tint) (tptr tdouble))
                                  tdouble))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Etempvar _U (tptr tdouble))
                                    (Ebinop Oadd (Etempvar _j tint)
                                      (Ebinop Omul (Etempvar _i tint)
                                        (Etempvar _ndof tint) tint) tint)
                                    (tptr tdouble)) tdouble)
                                (Ebinop Osub (Etempvar _t'2 tdouble)
                                  (Etempvar _t'4 tdouble) tdouble)))))
                        Sskip)))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_fem_set_load := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) ::
                (_f,
                 (tptr (Tfunction ((tptr tdouble) :: (tptr tdouble) :: nil)
                         tvoid cc_default))) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: (_numnp, tint) :: (_ndof, tint) ::
               (_X, (tptr tdouble)) :: (_F, (tptr tdouble)) :: (_i, tint) ::
               (_t'3, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'2, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
    (Sset _d
      (Efield
        (Ederef (Etempvar _t'3 (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _d tint)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
      (Sset _numnp
        (Efield
          (Ederef (Etempvar _t'2 (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _numnp tint)))
    (Ssequence
      (Sset _ndof
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _ndof tint))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _mesh
              (tptr (Tstruct _mesh_t noattr))))
          (Sset _X
            (Efield
              (Ederef (Etempvar _t'1 (tptr (Tstruct _mesh_t noattr)))
                (Tstruct _mesh_t noattr)) _X (tptr tdouble))))
        (Ssequence
          (Sset _F
            (Efield
              (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                (Tstruct _fem_t noattr)) _F (tptr tdouble)))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _numnp tint) tint)
                  Sskip
                  Sbreak)
                (Scall None
                  (Ederef
                    (Etempvar _f (tptr (Tfunction
                                         ((tptr tdouble) :: (tptr tdouble) ::
                                          nil) tvoid cc_default)))
                    (Tfunction ((tptr tdouble) :: (tptr tdouble) :: nil)
                      tvoid cc_default))
                  ((Ebinop Oadd (Etempvar _X (tptr tdouble))
                     (Ebinop Omul (Etempvar _i tint) (Etempvar _d tint) tint)
                     (tptr tdouble)) ::
                   (Ebinop Oadd (Etempvar _F (tptr tdouble))
                     (Ebinop Omul (Etempvar _i tint) (Etempvar _ndof tint)
                       tint) (tptr tdouble)) :: nil)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)))))))))
|}.

Definition f_assemble_matrix := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_K, (tptr (Tstruct _matrix_t noattr))) ::
                (_emat, (tptr tdouble)) :: (_ids, (tptr tint)) ::
                (_ne, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_je, tint) :: (_j, tint) :: (_ie, tint) :: (_i, tint) ::
               (_t'2, tint) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _je (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _je tint) (Etempvar _ne tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _j
          (Ederef
            (Ebinop Oadd (Etempvar _ids (tptr tint)) (Etempvar _je tint)
              (tptr tint)) tint))
        (Ssequence
          (Sset _ie (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _ie tint)
                             (Etempvar _je tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _i
                  (Ederef
                    (Ebinop Oadd (Etempvar _ids (tptr tint))
                      (Etempvar _ie tint) (tptr tint)) tint))
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sset _t'2
                      (Ecast
                        (Ebinop Oge (Etempvar _j tint) (Etempvar _i tint)
                          tint) tbool))
                    (Sset _t'2 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'2 tint)
                    (Ssequence
                      (Scall (Some _t'1)
                        (Evar _densematn_get (Tfunction
                                               ((tptr tdouble) :: tint ::
                                                tint :: tint :: nil) tdouble
                                               cc_default))
                        ((Etempvar _emat (tptr tdouble)) ::
                         (Etempvar _ne tint) :: (Etempvar _ie tint) ::
                         (Etempvar _je tint) :: nil))
                      (Scall None
                        (Evar _matrix_add (Tfunction
                                            ((tptr (Tstruct _matrix_t noattr)) ::
                                             tint :: tint :: tdouble :: nil)
                                            tvoid cc_default))
                        ((Etempvar _K (tptr (Tstruct _matrix_t noattr))) ::
                         (Etempvar _i tint) :: (Etempvar _j tint) ::
                         (Etempvar _t'1 tdouble) :: nil)))
                    Sskip))))
            (Sset _ie
              (Ebinop Oadd (Etempvar _ie tint) (Econst_int (Int.repr 1) tint)
                tint))))))
    (Sset _je
      (Ebinop Oadd (Etempvar _je tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_assemble_vector := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr tdouble)) :: (_ve, (tptr tdouble)) ::
                (_ids, (tptr tint)) :: (_ne, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ie, tint) :: (_i, tint) :: (_t'2, tdouble) ::
               (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _ie (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _ie tint) (Etempvar _ne tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _i
          (Ederef
            (Ebinop Oadd (Etempvar _ids (tptr tint)) (Etempvar _ie tint)
              (tptr tint)) tint))
        (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _v (tptr tdouble)) (Etempvar _i tint)
                  (tptr tdouble)) tdouble))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _ve (tptr tdouble))
                    (Etempvar _ie tint) (tptr tdouble)) tdouble))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _v (tptr tdouble))
                    (Etempvar _i tint) (tptr tdouble)) tdouble)
                (Ebinop Oadd (Etempvar _t'1 tdouble) (Etempvar _t'2 tdouble)
                  tdouble))))
          Sskip)))
    (Sset _ie
      (Ebinop Oadd (Etempvar _ie tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_fem_assemble := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) ::
                (_R, (tptr tdouble)) ::
                (_K, (tptr (Tstruct _matrix_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_numelt, tint) :: (_nen, tint) ::
               (_etype, (tptr (Tstruct _element_t noattr))) ::
               (_ids, (tptr tint)) :: (_Re, (tptr tdouble)) ::
               (_Ke, (tptr tdouble)) :: (_i, tint) :: (_elt, (tptr tint)) ::
               (_j, tint) :: (_t'5, (tptr tdouble)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tdouble)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tint)) ::
               (_t'13, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'12, (tptr (Tstruct _mesh_t noattr))) :: (_t'11, tint) ::
               (_t'10, (tptr tint)) ::
               (_t'9, (tptr (Tstruct _mesh_t noattr))) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'13
      (Efield
        (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
          (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
    (Sset _numelt
      (Efield
        (Ederef (Etempvar _t'13 (tptr (Tstruct _mesh_t noattr)))
          (Tstruct _mesh_t noattr)) _numelt tint)))
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _mesh (tptr (Tstruct _mesh_t noattr))))
      (Sset _nen
        (Efield
          (Ederef (Etempvar _t'12 (tptr (Tstruct _mesh_t noattr)))
            (Tstruct _mesh_t noattr)) _nen tint)))
    (Ssequence
      (Sset _etype
        (Efield
          (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
            (Tstruct _fem_t noattr)) _etype
          (tptr (Tstruct _element_t noattr))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _int_calloc (Tfunction (tint :: nil) (tptr tint)
                                cc_default)) ((Etempvar _nen tint) :: nil))
          (Sset _ids (Etempvar _t'1 (tptr tint))))
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _R (tptr tdouble))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _double_calloc (Tfunction (tint :: nil)
                                         (tptr tdouble) cc_default))
                  ((Etempvar _nen tint) :: nil))
                (Sset _t'2
                  (Ecast (Etempvar _t'3 (tptr tdouble)) (tptr tvoid))))
              (Sset _t'2
                (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                  (tptr tvoid))))
            (Sset _Re (Etempvar _t'2 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _K (tptr (Tstruct _matrix_t noattr)))
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _double_calloc (Tfunction (tint :: nil)
                                           (tptr tdouble) cc_default))
                    ((Ebinop Omul (Etempvar _nen tint) (Etempvar _nen tint)
                       tint) :: nil))
                  (Sset _t'4
                    (Ecast (Etempvar _t'5 (tptr tdouble)) (tptr tvoid))))
                (Sset _t'4
                  (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                    (tptr tvoid))))
              (Sset _Ke (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Sifthenelse (Etempvar _R (tptr tdouble))
                (Ssequence
                  (Sset _t'11
                    (Efield
                      (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                        (Tstruct _fem_t noattr)) _nactive tint))
                  (Scall None
                    (Evar _memset (Tfunction
                                    ((tptr tvoid) :: tint :: tulong :: nil)
                                    (tptr tvoid) cc_default))
                    ((Etempvar _R (tptr tdouble)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _t'11 tint)
                       (Esizeof tdouble tulong) tulong) :: nil)))
                Sskip)
              (Ssequence
                (Sifthenelse (Etempvar _K (tptr (Tstruct _matrix_t noattr)))
                  (Scall None
                    (Evar _matrix_clear (Tfunction
                                          ((tptr (Tstruct _matrix_t noattr)) ::
                                           nil) tvoid cc_default))
                    ((Etempvar _K (tptr (Tstruct _matrix_t noattr))) :: nil))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Etempvar _numelt tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Scall None
                            (Evar _element_dR (Tfunction
                                                ((tptr (Tstruct _element_t noattr)) ::
                                                 (tptr (Tstruct _fem_t noattr)) ::
                                                 tint :: (tptr tdouble) ::
                                                 (tptr tdouble) :: nil) tvoid
                                                cc_default))
                            ((Etempvar _etype (tptr (Tstruct _element_t noattr))) ::
                             (Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
                             (Etempvar _i tint) ::
                             (Etempvar _Re (tptr tdouble)) ::
                             (Etempvar _Ke (tptr tdouble)) :: nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                    (Tstruct _fem_t noattr)) _mesh
                                  (tptr (Tstruct _mesh_t noattr))))
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'9 (tptr (Tstruct _mesh_t noattr)))
                                      (Tstruct _mesh_t noattr)) _elt
                                    (tptr tint)))
                                (Sset _elt
                                  (Ebinop Oadd (Etempvar _t'10 (tptr tint))
                                    (Ebinop Omul (Etempvar _i tint)
                                      (Etempvar _nen tint) tint) (tptr tint)))))
                            (Ssequence
                              (Ssequence
                                (Sset _j (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j tint)
                                                   (Etempvar _nen tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'6
                                        (Efield
                                          (Ederef
                                            (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                            (Tstruct _fem_t noattr)) _id
                                          (tptr tint)))
                                      (Ssequence
                                        (Sset _t'7
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _elt (tptr tint))
                                              (Etempvar _j tint) (tptr tint))
                                            tint))
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'6 (tptr tint))
                                                (Etempvar _t'7 tint)
                                                (tptr tint)) tint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _ids (tptr tint))
                                                (Etempvar _j tint)
                                                (tptr tint)) tint)
                                            (Etempvar _t'8 tint))))))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Sifthenelse (Etempvar _R (tptr tdouble))
                                  (Scall None
                                    (Evar _assemble_vector (Tfunction
                                                             ((tptr tdouble) ::
                                                              (tptr tdouble) ::
                                                              (tptr tint) ::
                                                              tint :: nil)
                                                             tvoid
                                                             cc_default))
                                    ((Etempvar _R (tptr tdouble)) ::
                                     (Etempvar _Re (tptr tdouble)) ::
                                     (Etempvar _ids (tptr tint)) ::
                                     (Etempvar _nen tint) :: nil))
                                  Sskip)
                                (Sifthenelse (Etempvar _K (tptr (Tstruct _matrix_t noattr)))
                                  (Scall None
                                    (Evar _assemble_matrix (Tfunction
                                                             ((tptr (Tstruct _matrix_t noattr)) ::
                                                              (tptr tdouble) ::
                                                              (tptr tint) ::
                                                              tint :: nil)
                                                             tvoid
                                                             cc_default))
                                    ((Etempvar _K (tptr (Tstruct _matrix_t noattr))) ::
                                     (Etempvar _Ke (tptr tdouble)) ::
                                     (Etempvar _ids (tptr tint)) ::
                                     (Etempvar _nen tint) :: nil))
                                  Sskip))))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Sifthenelse (Etempvar _Ke (tptr tdouble))
                      (Scall None
                        (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid
                                      cc_default))
                        ((Etempvar _Ke (tptr tdouble)) :: nil))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Etempvar _Re (tptr tdouble))
                        (Scall None
                          (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid
                                        cc_default))
                          ((Etempvar _Re (tptr tdouble)) :: nil))
                        Sskip)
                      (Scall None
                        (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid
                                      cc_default))
                        ((Etempvar _ids (tptr tint)) :: nil)))))))))))))
|}.

Definition f_fem_assemble_band := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) ::
                (_R, (tptr tdouble)) ::
                (_K, (tptr (Tstruct _bandmat_t noattr))) :: nil);
  fn_vars := ((_Kmatrix, (Tstruct _matrix_t noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Etempvar _K (tptr (Tstruct _bandmat_t noattr)))
  (Ssequence
    (Scall None
      (Evar _init_matrix_band (Tfunction
                                ((tptr (Tstruct _matrix_t noattr)) ::
                                 (tptr (Tstruct _bandmat_t noattr)) :: nil)
                                tvoid cc_default))
      ((Eaddrof (Evar _Kmatrix (Tstruct _matrix_t noattr))
         (tptr (Tstruct _matrix_t noattr))) ::
       (Etempvar _K (tptr (Tstruct _bandmat_t noattr))) :: nil))
    (Scall None
      (Evar _fem_assemble (Tfunction
                            ((tptr (Tstruct _fem_t noattr)) ::
                             (tptr tdouble) ::
                             (tptr (Tstruct _matrix_t noattr)) :: nil) tvoid
                            cc_default))
      ((Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
       (Etempvar _R (tptr tdouble)) ::
       (Eaddrof (Evar _Kmatrix (Tstruct _matrix_t noattr))
         (tptr (Tstruct _matrix_t noattr))) :: nil)))
  (Scall None
    (Evar _fem_assemble (Tfunction
                          ((tptr (Tstruct _fem_t noattr)) ::
                           (tptr tdouble) ::
                           (tptr (Tstruct _matrix_t noattr)) :: nil) tvoid
                          cc_default))
    ((Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
     (Etempvar _R (tptr tdouble)) ::
     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil)))
|}.

Definition f_fem_assemble_dense := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) ::
                (_R, (tptr tdouble)) ::
                (_K, (tptr (Tstruct _densemat_t noattr))) :: nil);
  fn_vars := ((_Kmatrix, (Tstruct _matrix_t noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Etempvar _K (tptr (Tstruct _densemat_t noattr)))
  (Ssequence
    (Scall None
      (Evar _init_matrix_dense (Tfunction
                                 ((tptr (Tstruct _matrix_t noattr)) ::
                                  (tptr (Tstruct _densemat_t noattr)) :: nil)
                                 tvoid cc_default))
      ((Eaddrof (Evar _Kmatrix (Tstruct _matrix_t noattr))
         (tptr (Tstruct _matrix_t noattr))) ::
       (Etempvar _K (tptr (Tstruct _densemat_t noattr))) :: nil))
    (Scall None
      (Evar _fem_assemble (Tfunction
                            ((tptr (Tstruct _fem_t noattr)) ::
                             (tptr tdouble) ::
                             (tptr (Tstruct _matrix_t noattr)) :: nil) tvoid
                            cc_default))
      ((Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
       (Etempvar _R (tptr tdouble)) ::
       (Eaddrof (Evar _Kmatrix (Tstruct _matrix_t noattr))
         (tptr (Tstruct _matrix_t noattr))) :: nil)))
  (Scall None
    (Evar _fem_assemble (Tfunction
                          ((tptr (Tstruct _fem_t noattr)) ::
                           (tptr tdouble) ::
                           (tptr (Tstruct _matrix_t noattr)) :: nil) tvoid
                          cc_default))
    ((Etempvar _fe (tptr (Tstruct _fem_t noattr))) ::
     (Etempvar _R (tptr tdouble)) ::
     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil)))
|}.

Definition f_fem_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fe, (tptr (Tstruct _fem_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tint) :: (_j__1, tint) :: (_j__2, tint) :: (_i, tint) ::
               (_j__3, tint) :: (_j__4, tint) :: (_j__5, tint) ::
               (_t'24, tint) :: (_t'23, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'22, tint) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, (tptr (Tstruct _mesh_t noattr))) :: (_t'18, tint) ::
               (_t'17, (tptr tint)) :: (_t'16, tint) ::
               (_t'15, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'14, tdouble) :: (_t'13, tint) ::
               (_t'12, (tptr (Tstruct _mesh_t noattr))) ::
               (_t'11, (tptr tdouble)) ::
               (_t'10, (tptr (Tstruct _mesh_t noattr))) :: (_t'9, tint) ::
               (_t'8, tdouble) :: (_t'7, tint) :: (_t'6, (tptr tdouble)) ::
               (_t'5, tint) :: (_t'4, tdouble) :: (_t'3, tint) ::
               (_t'2, (tptr tdouble)) ::
               (_t'1, (tptr (Tstruct _mesh_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_1 (tarray tschar 21)) :: nil))
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_2 (tarray tschar 11)) :: nil))
    (Ssequence
      (Ssequence
        (Sset _j (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'23
                (Efield
                  (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                    (Tstruct _fem_t noattr)) _mesh
                  (tptr (Tstruct _mesh_t noattr))))
              (Ssequence
                (Sset _t'24
                  (Efield
                    (Ederef (Etempvar _t'23 (tptr (Tstruct _mesh_t noattr)))
                      (Tstruct _mesh_t noattr)) _d tint))
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Etempvar _t'24 tint) tint)
                  Sskip
                  Sbreak)))
            (Scall None
              (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_3 (tarray tschar 9)) ::
               (Etempvar _j tint) :: nil)))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _j__1 (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'22
                  (Efield
                    (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                      (Tstruct _fem_t noattr)) _ndof tint))
                (Sifthenelse (Ebinop Olt (Etempvar _j__1 tint)
                               (Etempvar _t'22 tint) tint)
                  Sskip
                  Sbreak))
              (Scall None
                (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_4 (tarray tschar 9)) ::
                 (Etempvar _j__1 tint) :: nil)))
            (Sset _j__1
              (Ebinop Oadd (Etempvar _j__1 tint)
                (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Ssequence
            (Sset _j__2 (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                        (Tstruct _fem_t noattr)) _ndof tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _j__2 tint)
                                 (Etempvar _t'21 tint) tint)
                    Sskip
                    Sbreak))
                (Scall None
                  (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_5 (tarray tschar 9)) ::
                   (Etempvar _j__2 tint) :: nil)))
              (Sset _j__2
                (Ebinop Oadd (Etempvar _j__2 tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_6 (tarray tschar 2)) :: nil))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'19
                        (Efield
                          (Ederef
                            (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                            (Tstruct _fem_t noattr)) _mesh
                          (tptr (Tstruct _mesh_t noattr))))
                      (Ssequence
                        (Sset _t'20
                          (Efield
                            (Ederef
                              (Etempvar _t'19 (tptr (Tstruct _mesh_t noattr)))
                              (Tstruct _mesh_t noattr)) _numnp tint))
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Etempvar _t'20 tint) tint)
                          Sskip
                          Sbreak)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'17
                          (Efield
                            (Ederef
                              (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                              (Tstruct _fem_t noattr)) _id (tptr tint)))
                        (Ssequence
                          (Sset _t'18
                            (Ederef
                              (Ebinop Oadd (Etempvar _t'17 (tptr tint))
                                (Etempvar _i tint) (tptr tint)) tint))
                          (Scall None
                            (Evar _printf (Tfunction ((tptr tschar) :: nil)
                                            tint
                                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                            ((Evar ___stringlit_7 (tarray tschar 12)) ::
                             (Etempvar _i tint) :: (Etempvar _t'18 tint) ::
                             nil))))
                      (Ssequence
                        (Ssequence
                          (Sset _j__3 (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                      (Tstruct _fem_t noattr)) _mesh
                                    (tptr (Tstruct _mesh_t noattr))))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'15 (tptr (Tstruct _mesh_t noattr)))
                                        (Tstruct _mesh_t noattr)) _d tint))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _j__3 tint)
                                                 (Etempvar _t'16 tint) tint)
                                    Sskip
                                    Sbreak)))
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                      (Tstruct _fem_t noattr)) _mesh
                                    (tptr (Tstruct _mesh_t noattr))))
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'10 (tptr (Tstruct _mesh_t noattr)))
                                        (Tstruct _mesh_t noattr)) _X
                                      (tptr tdouble)))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                          (Tstruct _fem_t noattr)) _mesh
                                        (tptr (Tstruct _mesh_t noattr))))
                                    (Ssequence
                                      (Sset _t'13
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'12 (tptr (Tstruct _mesh_t noattr)))
                                            (Tstruct _mesh_t noattr)) _d
                                          tint))
                                      (Ssequence
                                        (Sset _t'14
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'11 (tptr tdouble))
                                              (Ebinop Oadd
                                                (Etempvar _j__3 tint)
                                                (Ebinop Omul
                                                  (Etempvar _t'13 tint)
                                                  (Etempvar _i tint) tint)
                                                tint) (tptr tdouble))
                                            tdouble))
                                        (Scall None
                                          (Evar _printf (Tfunction
                                                          ((tptr tschar) ::
                                                           nil) tint
                                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                          ((Evar ___stringlit_8 (tarray tschar 7)) ::
                                           (Etempvar _t'14 tdouble) :: nil))))))))
                            (Sset _j__3
                              (Ebinop Oadd (Etempvar _j__3 tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _j__4 (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sset _t'9
                                    (Efield
                                      (Ederef
                                        (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                        (Tstruct _fem_t noattr)) _ndof tint))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _j__4 tint)
                                                 (Etempvar _t'9 tint) tint)
                                    Sskip
                                    Sbreak))
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Ederef
                                        (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                        (Tstruct _fem_t noattr)) _U
                                      (tptr tdouble)))
                                  (Ssequence
                                    (Sset _t'7
                                      (Efield
                                        (Ederef
                                          (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                          (Tstruct _fem_t noattr)) _ndof
                                        tint))
                                    (Ssequence
                                      (Sset _t'8
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'6 (tptr tdouble))
                                            (Ebinop Oadd
                                              (Etempvar _j__4 tint)
                                              (Ebinop Omul
                                                (Etempvar _t'7 tint)
                                                (Etempvar _i tint) tint)
                                              tint) (tptr tdouble)) tdouble))
                                      (Scall None
                                        (Evar _printf (Tfunction
                                                        ((tptr tschar) ::
                                                         nil) tint
                                                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                        ((Evar ___stringlit_9 (tarray tschar 8)) ::
                                         (Etempvar _t'8 tdouble) :: nil))))))
                              (Sset _j__4
                                (Ebinop Oadd (Etempvar _j__4 tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Ssequence
                              (Sset _j__5 (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'5
                                      (Efield
                                        (Ederef
                                          (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                          (Tstruct _fem_t noattr)) _ndof
                                        tint))
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j__5 tint)
                                                   (Etempvar _t'5 tint) tint)
                                      Sskip
                                      Sbreak))
                                  (Ssequence
                                    (Sset _t'2
                                      (Efield
                                        (Ederef
                                          (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                          (Tstruct _fem_t noattr)) _F
                                        (tptr tdouble)))
                                    (Ssequence
                                      (Sset _t'3
                                        (Efield
                                          (Ederef
                                            (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                                            (Tstruct _fem_t noattr)) _ndof
                                          tint))
                                      (Ssequence
                                        (Sset _t'4
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'2 (tptr tdouble))
                                              (Ebinop Oadd
                                                (Etempvar _j__5 tint)
                                                (Ebinop Omul
                                                  (Etempvar _t'3 tint)
                                                  (Etempvar _i tint) tint)
                                                tint) (tptr tdouble))
                                            tdouble))
                                        (Scall None
                                          (Evar _printf (Tfunction
                                                          ((tptr tschar) ::
                                                           nil) tint
                                                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                          ((Evar ___stringlit_9 (tarray tschar 8)) ::
                                           (Etempvar _t'4 tdouble) :: nil))))))
                                (Sset _j__5
                                  (Ebinop Oadd (Etempvar _j__5 tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Scall None
                              (Evar _printf (Tfunction ((tptr tschar) :: nil)
                                              tint
                                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                              ((Evar ___stringlit_6 (tarray tschar 2)) ::
                               nil)))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef (Etempvar _fe (tptr (Tstruct _fem_t noattr)))
                      (Tstruct _fem_t noattr)) _mesh
                    (tptr (Tstruct _mesh_t noattr))))
                (Scall None
                  (Evar _mesh_print_elt (Tfunction
                                          ((tptr (Tstruct _mesh_t noattr)) ::
                                           nil) tvoid cc_default))
                  ((Etempvar _t'1 (tptr (Tstruct _mesh_t noattr))) :: nil))))))))))
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
 Composite _matrix_t Struct
   (Member_plain _p (tptr (Tstruct _matrix_data_t noattr)) ::
    Member_plain _add
      (tptr (Tfunction
              ((tptr (Tstruct _matrix_data_t noattr)) :: tint :: tint ::
               tdouble :: nil) tvoid cc_default)) ::
    Member_plain _clear
      (tptr (Tfunction ((tptr (Tstruct _matrix_data_t noattr)) :: nil) tvoid
              cc_default)) ::
    Member_plain _norm2
      (tptr (Tfunction ((tptr (Tstruct _matrix_data_t noattr)) :: nil)
              tdouble cc_default)) ::
    Member_plain _print
      (tptr (Tfunction ((tptr (Tstruct _matrix_data_t noattr)) :: nil) tvoid
              cc_default)) :: nil)
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
 Composite _mesh_t Struct
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
     cc_default)) :: (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Xptr :: nil) AST.Xint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_free, Gfun(External EF_free ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
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
 (_densematn_get,
   Gfun(External (EF_external "densematn_get"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xint :: nil)
                     AST.Xfloat cc_default))
     ((tptr tdouble) :: tint :: tint :: tint :: nil) tdouble cc_default)) ::
 (_matrix_add,
   Gfun(External (EF_external "matrix_add"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xfloat :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _matrix_t noattr)) :: tint :: tint :: tdouble :: nil)
     tvoid cc_default)) ::
 (_matrix_clear,
   Gfun(External (EF_external "matrix_clear"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _matrix_t noattr)) :: nil) tvoid cc_default)) ::
 (_init_matrix_dense,
   Gfun(External (EF_external "init_matrix_dense"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _matrix_t noattr)) ::
      (tptr (Tstruct _densemat_t noattr)) :: nil) tvoid cc_default)) ::
 (_init_matrix_band,
   Gfun(External (EF_external "init_matrix_band"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _matrix_t noattr)) ::
      (tptr (Tstruct _bandmat_t noattr)) :: nil) tvoid cc_default)) ::
 (_element_dR,
   Gfun(External (EF_external "element_dR"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xint :: AST.Xptr ::
                      AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _element_t noattr)) :: (tptr (Tstruct _fem_t noattr)) ::
      tint :: (tptr tdouble) :: (tptr tdouble) :: nil) tvoid cc_default)) ::
 (_mesh_free,
   Gfun(External (EF_external "mesh_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _mesh_t noattr)) :: nil) tvoid cc_default)) ::
 (_mesh_print_elt,
   Gfun(External (EF_external "mesh_print_elt"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _mesh_t noattr)) :: nil) tvoid cc_default)) ::
 (_fem_malloc, Gfun(Internal f_fem_malloc)) ::
 (_fem_free, Gfun(Internal f_fem_free)) ::
 (_fem_assign_ids, Gfun(Internal f_fem_assign_ids)) ::
 (_fem_update_U, Gfun(Internal f_fem_update_U)) ::
 (_fem_set_load, Gfun(Internal f_fem_set_load)) ::
 (_assemble_matrix, Gfun(Internal f_assemble_matrix)) ::
 (_assemble_vector, Gfun(Internal f_assemble_vector)) ::
 (_fem_assemble, Gfun(Internal f_fem_assemble)) ::
 (_fem_assemble_band, Gfun(Internal f_fem_assemble_band)) ::
 (_fem_assemble_dense, Gfun(Internal f_fem_assemble_dense)) ::
 (_fem_print, Gfun(Internal f_fem_print)) :: nil).

Definition public_idents : list ident :=
(_fem_print :: _fem_assemble_dense :: _fem_assemble_band :: _fem_assemble ::
 _assemble_vector :: _assemble_matrix :: _fem_set_load :: _fem_update_U ::
 _fem_assign_ids :: _fem_free :: _fem_malloc :: _mesh_print_elt ::
 _mesh_free :: _element_dR :: _init_matrix_band :: _init_matrix_dense ::
 _matrix_clear :: _matrix_add :: _densematn_get :: _int_calloc ::
 _double_calloc :: _surely_malloc :: _memset :: _free :: _printf ::
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


