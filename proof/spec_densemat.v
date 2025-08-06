Require Import VST.floyd.proofauto.
From CFEM Require Import densemat spec_alloc.
(* From vcfloat Require Import vcfloat.FPStdCompCert vcfloat.FPStdLib. *)
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


(* @Hierarchy.matrix (option float) (Z.to_nat m) (Z.to_nat n)) *)
Definition densemat (sh: share) (m n: Z) (data: list (list val)) (p: val) : mpred :=
 !! (Zlength data = n /\ Forall (fun l => Zlength l = m) data)
 && (field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint (Int.repr m)) p
     * data_at sh (tarray tdouble (m*n)) (concat data) (offset_val densemat_data_offset p)).

Definition densemat_malloc_spec :=
  DECLARE _densemat_malloc
  WITH m: Z, n: Z, gv: globals
  PRE [ tint, tint ]
    PROP(0 <= m <= Int.max_signed; 0 <= n <= Int.max_signed) 
    PARAMS (Vint (Int.repr m); Vint (Int.repr n) ) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr densemat_t ]
   EX p: val,
    PROP () 
    RETURN (p) 
    SEP(densemat Ews m n (Zrepeat (Zrepeat Vundef m) n) p; mem_mgr gv).

Definition densematASI : funspecs := [ 
   densemat_malloc_spec ].
