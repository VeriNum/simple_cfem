Require Import VST.floyd.proofauto.
From CFEM.C Require Import shapes.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.accuracy_proofs Require Import solve_model.
From LAProof.C Require Import VSU_densemat spec_alloc floatlib matrix_model.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import CFEM.C.nonexpansive.
Import spec_densemat.

Open Scope logic.

Require Import CFEM.shapefloat.

Definition ifptr (p: val) (A: mpred) : mpred :=
 match p with Vptr _ _ => A | _ => emp end.

Lemma ifptr_valid_pointer: forall p (A: val -> mpred), 
    is_pointer_or_null p ->
     (A p |-- valid_pointer p) -> 
    ifptr p (A p) |-- valid_pointer p.
Proof.
intros.
unfold ifptr;
destruct p; try contradiction; auto with valid_pointer.
unfold valid_pointer, valid_pointer'.
red in H.
destruct Archi.ptr64; try contradiction.
change (emp |-- !! (i = Int64.zero)).
apply prop_right.
auto.
Qed.

Hint Resolve ifptr_valid_pointer: valid_pointer.

Definition shape_spec (shape: @FShape.shape the_type) : funspec :=
   let '({| FShape.d := d; FShape.nsh := nsh; FShape.θ := θ; FShape.dθ := dθ |}) := shape in  
  WITH shN: share, shxx:share, pN : val, pdN: val, x: 'rV[ftype the_type]_d, pxx: val
  PRE [ tptr the_ctype, tptr the_ctype, tptr the_ctype ]
    PROP(writable_share shN; readable_share shxx; is_pointer_or_null pN; is_pointer_or_null pdN)
    PARAMS( pN; pdN; pxx)
    SEP(ifptr pN (densematn shN (@const_mx (option(ftype the_type)) 1 nsh None) pN);
             ifptr pdN (densematn shN (@const_mx (option(ftype the_type)) nsh d None) pdN);
             densematn shxx (map_mx Some x) pxx)
  POST[ tint ]
    PROP()
    RETURN (Vint (Int.repr nsh))
    SEP(ifptr pN (densematn shN (map_mx Some (θ x)) pN);
             ifptr pdN (densematn shN (map_mx Some (dθ x)) pdN);
             densematn shxx (map_mx Some x) pxx).

Definition shapes1dP1_spec := DECLARE _shapes1dP1 (shape_spec shapes1dP1F).
Definition shapes1dP2_spec := DECLARE _shapes1dP2 (shape_spec shapes1dP2F).
Definition shapes1dP3_spec := DECLARE _shapes1dP3 (shape_spec shapes1dP3F).
Definition shapes2dP1_spec := DECLARE _shapes2dP1 (shape_spec shapes2dP1F).
Definition shapes2dP2_spec := DECLARE _shapes2dP2 (shape_spec shapes2dP2F).
Definition shapes2dS2_spec := DECLARE _shapes2dS2 (shape_spec shapes2dS2F).
Definition shapes2dT1_spec := DECLARE _shapes2dT1 (shape_spec shapes2dT1F).

Definition shapes_ASI: funspecs :=
 [ shapes1dP1_spec; shapes1dP2_spec; shapes1dP3_spec; 
   shapes2dP1_spec; shapes2dP2_spec; shapes2dS2_spec;
   shapes2dT1_spec].





