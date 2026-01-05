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

From CFEM.C Require Import assemble spec_assemble.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Open Scope logic.

Definition Gprog := assemble_ASI ++ spec_densemat.densematASI.

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


Lemma body_assemble_add: semax_body Vprog Gprog f_assemble_add assemble_add_spec.
Proof.
start_function.
unfold assemble_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) (A,(i,j)) : {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
forward_call (p,sh,X,y,x).
unfold assemble_obj.
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

Lemma body_assemble_clear: semax_body Vprog Gprog f_assemble_clear assemble_clear_spec.
Proof.
start_function.
rename X into A.
unfold assemble_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
unfold assemble_obj.
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

Lemma body_assemble_norm2: semax_body Vprog Gprog f_assemble_norm2 assemble_norm2_spec.
Proof.
start_function.
rename X into A.
unfold assemble_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
forward.
unfold assemble_obj.
Exists p add clear norm2 print.
entailer!!.
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

Lemma body_assemble_print: semax_body Vprog Gprog f_assemble_print assemble_print_spec.
Proof.
start_function.
rename X into A.
unfold assemble_obj.
Intros p add clear norm2 print.
forward.
forward.
change spec_densemat.the_type with the_type in *.
pose (X := existT _ (m,n) A :  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type).
forward_call (p,sh,X).
unfold assemble_obj.
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

Lemma body_init_assemble_dense: semax_body Vprog Gprog f_init_assemble_dense init_assemble_dense_spec.
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
unfold assemble_obj.
Exists p  (gv _casted_densemat_add)  (gv _casted_densemat_clear)  (gv _casted_densemat_norm2)  (gv _casted_densemat_print).
entailer!!.
Qed.




