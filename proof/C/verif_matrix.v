Require Import VST.floyd.proofauto.
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

From CFEM.C Require Import matrix spec_matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Open Scope logic.

Section import_densemat.
Import spec_densemat.
Definition matrix_imported_specs := 
  [densemat_addto_spec; densemat_clear_spec; densemat_norm2_spec; densemat_print_spec;
   sqrt_spec ].
End import_densemat.

Definition matrix_E : funspecs := [].
Definition matrix_internal_specs : funspecs := matrix_ASI.

Definition Gprog := matrix_imported_specs ++ matrix_internal_specs.

Ltac destruct_it B ::= (* remove this if/when VST 2.17 incorporates it. *)
 match B with
 | ?C _ => destruct_it C
 | let '(x,y) := ?A in _ => destruct A as [x y]
 | match ?A with _ => _ end =>
    match type of A with ?tA => let uA := eval hnf in tA in 
     match uA with
     | @sigT _ (fun x => _) => destruct A as [x A] 
     end end
 end.

Ltac densemat_lemmas.destruct_it B ::= (* remove this when LAProof is updated for VST 2.16 *)
 match B with 
 | ?C _ => destruct_it C
 | let '(x,y) := ?A in _ => destruct A as [x y]
 | match ?A with _ => _ end =>
    match type of A with ?tA => let uA := eval hnf in tA in 
     match uA with
     | @sigT _ (fun x => _) => destruct A as [x A] 
     end end
 end.


Lemma body_matrix_add: semax_body Vprog Gprog f_matrix_add matrix_add_spec.
Proof.
start_function.
unfold matrix_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) (A,(i,j)) : {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
forward_call (p,sh,X,y,x).
unfold matrix_obj.
entailer!!.
Exists p add clear norm2 print.
entailer!!.
Qed.

Lemma body_casted_densemat_add: semax_body Vprog Gprog f_casted_densemat_add casted_densemat_add_spec.
Proof.
start_function.
pose (X := existT _ (m,n) (A,(i,j)) : {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
forward_call (X,p,sh,y,x).
unfold dense_matrix_rep.
simpl. cancel.
entailer!!.
Qed.

Lemma body_matrix_clear: semax_body Vprog Gprog f_matrix_clear matrix_clear_spec.
Proof.
start_function.
rename X into A.
unfold matrix_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
unfold matrix_obj.
entailer!!.
Exists p add clear norm2 print.
entailer!!.
Qed.

Lemma body_casted_densemat_clear: semax_body Vprog Gprog f_casted_densemat_clear casted_densemat_clear_spec.
Proof.
start_function.
rename X into A.
pose (X := existT _ (m,n) A : {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type).
forward_call (X,p,sh).
unfold dense_matrix_rep.
simpl. cancel.
entailer!!.
Qed.

Lemma body_matrix_norm2: semax_body Vprog Gprog f_matrix_norm2 matrix_norm2_spec.
Proof.
start_function.
rename X into A.
unfold matrix_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
forward.
unfold matrix_obj.
Exists p add clear norm2 print.
entailer!!.
Qed.

Lemma body_matrix_norm: semax_body Vprog Gprog f_matrix_norm matrix_norm_spec.
Proof.
start_function.
rename X into A.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (obj, sho, sh, X, inst).
forward_call.
Locate sqrt_ff.
forward.
entailer!!.
change (val_of_float ?A) with (Vfloat A).
f_equal.
unfold BSQRT, UNOP. f_equal.
replace (FPCore.fprec_gt_one FPCore.Tdouble) with (fprec_gt_one the_type) by (apply proof_irr).
reflexivity.
Qed.

Lemma body_casted_densemat_norm2: semax_body Vprog Gprog f_casted_densemat_norm2 casted_densemat_norm2_spec.
Proof.
start_function.
rename X into A.
pose (X := existT _ (m,n) A : {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (sh,X,p).
unfold dense_matrix_rep.
simpl. cancel.
forward.
Qed.

Lemma body_matrix_print: semax_body Vprog Gprog f_matrix_print matrix_print_spec.
Proof.
start_function.
rename X into A.
unfold matrix_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
unfold matrix_obj.
entailer!!.
Exists p add clear norm2 print.
entailer!!.
Qed.

Lemma body_casted_densemat_print: semax_body Vprog Gprog f_casted_densemat_print casted_densemat_print_spec.
Proof.
start_function.
rename X into A.
pose (X := existT _ (m,n) A : {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (X,p,sh).
unfold dense_matrix_rep; simpl; cancel.
entailer!!.
Qed.

Lemma body_init_matrix_dense: semax_body Vprog Gprog f_init_matrix_dense init_matrix_dense_spec.
Proof.
start_function.
assert_PROP (isptr p). {
  unfold spec_densemat.densemat. entailer!.
  destruct H0 as [H0 _]; auto.
}
make_func_ptr _casted_densemat_add.
make_func_ptr _casted_densemat_clear.
make_func_ptr _casted_densemat_norm2.
make_func_ptr _casted_densemat_print.
forward.
forward.
forward.
forward.
forward.
entailer!!.
unfold matrix_obj.
Exists p  (gv _casted_densemat_add)  (gv _casted_densemat_clear)  (gv _casted_densemat_norm2)  (gv _casted_densemat_print).
entailer!!.
Qed.


Require Import VST.floyd.VSU.

Definition matrixVSU: @VSU NullExtension.Espec
         matrix_E matrix_imported_specs 
         ltac:(QPprog prog) matrix_ASI (fun _ => TT).
  Proof.
    mkVSU prog matrix_internal_specs.
    - solve_SF_internal body_matrix_add.
    - solve_SF_internal body_casted_densemat_add.
    - solve_SF_internal body_matrix_clear.
    - solve_SF_internal body_casted_densemat_clear.
    - solve_SF_internal body_matrix_norm2.
    - solve_SF_internal body_casted_densemat_norm2.
    - solve_SF_internal body_matrix_norm.
    - solve_SF_internal body_matrix_print.
    - solve_SF_internal body_casted_densemat_print.
    - solve_SF_internal body_init_matrix_dense.
Qed.


