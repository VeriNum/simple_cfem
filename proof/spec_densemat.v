Require Import VST.floyd.proofauto.
From CFEM Require Import densemat spec_alloc floatlib.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition densemat_t := Tstruct _densemat_t noattr.

Definition densemat_data_offset := 
  ltac:(let x := constr:(nested_field_offset densemat_t (DOT _data))
        in let y := eval compute in x in exact y).

Lemma check_densemat_layout:
  forall sh m n (x: list val) p, 
    data_at sh (Tstruct _densemat_t noattr) (Vint m,(Vint n,x)) p 
  |-- field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint m) p *
    field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint n) p.
(* This lemma could fail if there's padding between the fields. *)
Proof.
intros.
unfold_data_at (data_at _ _ _ _).
cancel.
entailer!.
rewrite value_fits_eq in H0. simpl in H0. destruct H0 as [? _].
change (unfold_reptype _) with x in H0.
destruct x; [ | list_solve].
unfold field_at. simpl.
entailer!!.
unfold data_at_rec. simpl.
unfold at_offset.
change (unfold_reptype _) with (@nil val).
rewrite array_pred_len_0; auto.
Qed.

Local Lemma Test_transpose:
  forall f: Z -> ftype Tdouble,
   let A := map (map f) [[1;2;3];[4;5;6]]
   in let B := map (map f) [[1;4];[2;5];[3;6]]
   in matrix_transpose A = B.
Proof. reflexivity. Qed.

Local Lemma Test_faster_transpose:
   let A :=  [[1;2;3];[4;5;6]]
   in let B :=  [[1;4];[2;5];[3;6]]
   in faster_matrix_transpose A = B.
Proof. reflexivity. Qed.

Definition mklist {T} (n: nat) (f: nat -> T) : list T :=
 map f (seq 0 n).

Definition column_major {T} (rows cols: Z) (f: Z -> Z -> T) :=
 concat (mklist (Z.to_nat cols) (fun j => mklist (Z.to_nat rows) (fun i => f (Z.of_nat i) (Z.of_nat j)))).

Definition val_of_optfloat (x: option float) :=
 match x with 
 | Some f => Vfloat f
 | None => Vundef
 end.

Definition densemat (sh: share) (m n: Z) (data: Z -> Z -> option float) (p: val) : mpred :=
 !! (0 <= m <= Int.max_signed /\ 0 <= n <= Int.max_signed /\ m*n <= Int.max_signed)
 && (field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint (Int.repr m)) p
   * field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint (Int.repr n)) p
   * data_at sh (tarray tdouble (m*n)) (map val_of_optfloat (column_major m n data))
         (offset_val densemat_data_offset p)
   * malloc_token' sh (densemat_data_offset + sizeof (tarray tdouble (m*n))) p).

Definition densemat_local_facts: forall sh m n data p,
  densemat sh m n data p |-- 
      !! (0 <= m <= Int.max_signed /\ 0 <= n <= Int.max_signed
          /\ m*n <= Int.max_signed /\ 
           malloc_compatible (densemat_data_offset + sizeof (tarray tdouble (m * n))) p).
Proof.
intros.
unfold densemat.
entailer!.
Qed.

#[export] Hint Resolve densemat_local_facts : saturate_local.

Lemma densemat_valid_pointer:
  forall sh m n data p,
   densemat sh m n data p |-- valid_pointer p.
Proof.
 intros.
 unfold densemat. entailer!.
Qed.

#[export] Hint Resolve densemat_valid_pointer : valid_pointer.


Definition densemat_malloc_spec :=
  DECLARE _densemat_malloc
  WITH m: Z, n: Z, gv: globals
  PRE [ tint, tint ]
    PROP(0 <= m <= Int.max_signed; 0 <= n <= Int.max_signed; m*n <= Int.max_signed)
    PARAMS (Vint (Int.repr m); Vint (Int.repr n) ) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr densemat_t ]
   EX p: val,
    PROP () 
    RETURN (p) 
    SEP(densemat Ews m n (fun _ _ => None) p; mem_mgr gv).


Definition densemat_free_spec :=
  DECLARE _densemat_free
  WITH m: Z, n: Z, v: Z -> Z -> option float, p: val, gv: globals
  PRE [ tptr densemat_t ]
    PROP() 
    PARAMS ( p ) GLOBALS (gv)
    SEP(densemat Ews m n v p; mem_mgr gv)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP( mem_mgr gv ).

Definition densematn_clear_spec :=
  DECLARE _densematn_clear
  WITH m: Z, n: Z, v: Z -> Z -> option float, p: val, sh: share
  PRE [ tptr tdouble, tint, tint ]
    PROP(writable_share sh) 
    PARAMS (field_address densemat_t (DOT _data) p; Vint (Int.repr m); Vint (Int.repr n) )
    SEP(densemat sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densemat sh m n (fun _ _ => Some Float.zero) p).

Definition densemat_clear_spec :=
  DECLARE _densemat_clear
  WITH m: Z, n: Z, v: Z -> Z -> option float, p: val, sh: share
  PRE [ tptr densemat_t ]
    PROP(writable_share sh) 
    PARAMS (p)
    SEP(densemat sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densemat sh m n (fun _ _ => Some Float.zero) p).

Definition data_norm_spec  : ident*funspec := 
 (_data_norm, vacuous_funspec (Internal f_data_norm)).
Definition data_norm2_spec : ident*funspec := 
 (_data_norm2, vacuous_funspec (Internal f_data_norm2)).
Definition densemat_norm_spec : ident*funspec := 
 (_densemat_norm, vacuous_funspec (Internal f_densemat_norm)).
Definition densemat_norm2_spec : ident*funspec := 
 (_densemat_norm2, vacuous_funspec (Internal f_densemat_norm2)).
Definition densemat_lujac_spec : ident*funspec := 
 (_densemat_lujac, vacuous_funspec (Internal f_densemat_lujac)).
Definition densematn_lujac_spec : ident*funspec := 
 (_densematn_lujac, vacuous_funspec (Internal f_densematn_lujac)).
Definition densematn_print_spec : ident*funspec := 
 (_densematn_print, vacuous_funspec (Internal f_densematn_print)).
Definition densemat_print_spec : ident*funspec := 
 (_densemat_print, vacuous_funspec (Internal f_densemat_print)).
Definition densemat_lusolve_spec : ident*funspec := 
 (_densemat_lusolve, vacuous_funspec (Internal f_densemat_lusolve)).
Definition densematn_lusolve_spec : ident*funspec := 
 (_densematn_lusolve, vacuous_funspec (Internal f_densematn_lusolve)).
Definition densemat_lufactor_spec : ident*funspec := 
 (_densemat_lufactor, vacuous_funspec (Internal f_densemat_lufactor)).
Definition densematn_lufactor_spec : ident*funspec := 
 (_densematn_lufactor, vacuous_funspec (Internal f_densematn_lufactor)).
Definition densemat_csolve_spec : ident*funspec := 
 (_densemat_csolve, vacuous_funspec (Internal f_densemat_csolve)).
Definition densematn_csolve_spec : ident*funspec := 
 (_densematn_csolve, vacuous_funspec (Internal f_densematn_csolve)).
Definition densematn_cfactor_spec : ident*funspec := 
 (_densematn_cfactor, vacuous_funspec (Internal f_densematn_cfactor)).
Definition densemat_cfactor_spec : ident*funspec := 
 (_densemat_cfactor, vacuous_funspec (Internal f_densemat_cfactor)).
Definition densematn_lusolveT_spec : ident*funspec := 
 (_densematn_lusolveT, vacuous_funspec (Internal f_densematn_lusolveT)).
Definition densemat_lusolveT_spec : ident*funspec := 
 (_densemat_lusolveT, vacuous_funspec (Internal f_densemat_lusolveT)).



Definition densematASI : funspecs := [ 
   densemat_malloc_spec; densemat_free_spec; densematn_clear_spec; densemat_clear_spec;
   data_norm_spec; data_norm2_spec;
   densemat_norm_spec; densemat_norm2_spec;
   densemat_lujac_spec; densematn_lujac_spec;
   densemat_print_spec; densematn_print_spec;
   densemat_lusolve_spec; densematn_lusolve_spec;
   densemat_lufactor_spec; densematn_lufactor_spec;
   densemat_csolve_spec; densematn_csolve_spec;
   densemat_cfactor_spec; densematn_cfactor_spec;
   densemat_lusolveT_spec; densematn_lusolveT_spec
    ].


