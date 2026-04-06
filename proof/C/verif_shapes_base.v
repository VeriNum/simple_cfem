Require Export VST.floyd.proofauto.
From vcfloat Require Export FPStdCompCert FPStdLib.
From VSTlib Require Export spec_math spec_malloc.
From LAProof.accuracy_proofs Require Export solve_model.
From LAProof.C Require Export VSU_densemat spec_alloc floatlib matrix_model.
From Stdlib Require Export Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Export ssrZ zify.
Export fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Require Import CFEM.C.nonexpansive.
Export spec_densemat densemat_lemmas.

Open Scope logic.

Require Export CFEM.shapefloat CFEM.C.spec_shapes.
Export shapes.


Section import_densemat.
Import spec_densemat.
Definition shapes_imported_specs : funspecs := 
  [ densematn_get_spec; densematn_set_spec ].
End import_densemat.

Definition shapes_E : funspecs := [].
Definition shapes_internal_specs : funspecs := shapes_ASI.

Definition Gprog := shapes_imported_specs ++ shapes_internal_specs.


Lemma ifptr_true: forall (p: val) (A: mpred), isptr p -> ifptr p A = A.
Proof.
intros.
destruct p; try contradiction; auto.
Qed.

Lemma ifptr_false: forall A, ifptr nullval A = emp.
Proof.
intros.
reflexivity.
Qed.


Lemma Float_mul_congr: forall x y x' y', x = x' -> y = y' -> Float.mul x y = Float.mul x' y'.
Proof. intros; subst; auto. Qed.
Lemma Float_add_congr: forall x y x' y', x = x' -> y = y' -> Float.add x y = Float.add x' y'.
Proof. intros; subst; auto. Qed.
Lemma Float_sub_congr: forall x y x' y', x = x' -> y = y' -> Float.sub x y = Float.sub x' y'.
Proof. intros; subst; auto. Qed.

Lemma Float_of_int_repr: forall i, 
  Int.min_signed <= i <= Int.max_signed ->
  Float.of_int (Int.repr i) = lib.IEEE754_extra.BofZ 53 1024 eq_refl eq_refl i.
Proof.
intros.
Transparent Float.of_int.
unfold Float.of_int.
Opaque Float.of_int.
rewrite Int.signed_repr by auto; auto.
Qed.

Lemma Float_of_bits_repr: 
  forall i, 0 <= i <= Int64.max_unsigned ->
   Float.of_bits (Int64.repr i) = Bits.b64_of_bits i. 
Proof.
intros.
Transparent Float.of_bits.
unfold Float.of_bits.
Opaque Float.of_bits.
rewrite Int64.unsigned_repr; auto.
Qed.


Ltac prove_float_exprs_same :=
 change BMULT with Float.mul; change BPLUS with Float.add; change BMINUS with Float.sub;
  rewrite ?Float_of_int_repr, ?Float_of_bits_repr by rep_lia;
 repeat 
 first [ apply f_equal_Some
        | apply Float_mul_congr
        | apply Float_add_congr
        | apply Float_sub_congr
        |  with_strategy transparent [Float.neg] apply B754_finite_ext
        | with_strategy transparent [Float.neg] reflexivity
       ].

Ltac prove_matrices_same := 
 unfold  update_mx; simpl; unfold map_mx, row_mx, col_mx, const_mx; simpl;
 apply matrixP; intros [i Hi] [j Hj]; simpl;
 rewrite !mxE;
 repeat destruct (Nat.eq_dec _ _); simpl in *; subst; try discriminate; unfold split;
 repeat (destruct (ssrnat.ltnP _ _); simpl in *; try lia; rewrite !mxE);
 prove_float_exprs_same.

Ltac forward_densematn_set_special_aux pvar p stride i j :=
    match goal with |- semax _ ?Pre _ _ => match Pre with context [densematn ?sh ?M p] =>
     match type of M with @matrix _ ?m ?n =>
      let i' := constr:(@Ordinal m (Z.to_nat i) (eq_refl _)) in
      let j' := constr:(@Ordinal n (Z.to_nat j) (eq_refl _)) in
        densemat_lemmas.forward_densematn_get M i'  j' p sh (optfloat_to_float (M i' j'))
    end end end;
    [ try (unfold map_mx; rewrite !mxE; reflexivity) | ].

Ltac forward_densematn_get_special :=
 match goal with
 | |- context [Scall (Some _) (Evar _densematn_get _)
                                             [Etempvar ?pvar _; Econst_int (Int.repr ?stride) _; 
                                              Econst_int (Int.repr ?i) _; Econst_int (Int.repr ?j) _]] =>
      match goal with |- context [temp pvar ?p] =>
            forward_densematn_set_special_aux pvar p stride i j 
       end
 | |- context [Scall (Some _) (Evar _densematn_get _)
                                             [Evar ?pvar _; Econst_int (Int.repr ?stride) _; 
                                              Econst_int (Int.repr ?i) _; Econst_int (Int.repr ?j) _]] =>
   match goal with |- context [lvar pvar _ ?p] =>
            forward_densematn_set_special_aux pvar p stride i j 
   end
end.

Ltac forward_densematn_set_special :=
 match goal with |- context [Scall None (Evar _densematn_set _)
                                             [Etempvar ?pvar _; Econst_int (Int.repr ?stride) _; 
                                              Econst_int (Int.repr ?i) _; Econst_int (Int.repr ?j) _;
                                               _]] =>
   match goal with |- context [temp pvar ?p] =>
    match goal with |- semax _ ?Pre _ _ => match Pre with context [densematn ?sh ?M p] =>
     match type of M with @matrix _ ?m ?n =>
     let y := fresh "y" in 
      evar (y: ftype Tdouble);
        densemat_lemmas.forward_densematn_set M
        (@Ordinal m (Z.to_nat i) (eq_refl _))  (@Ordinal n (Z.to_nat j) (eq_refl _)) p sh y; subst y
    end end end
   end 
end; [entailer!! | ].

(** [begin_densematn_in_frame] is used when you already have an array of floats/doubles
   that you want to treat as a dense matrix.  That is, you don't want to call [densemat_alloc].
   Typical example is a stack-allocated (local-variable) array. 
   There is a tactic [begin_densemat_in_frame] for automatically applying this lemma. *)
Lemma begin_densematn_in_frame:
  forall compspecs sh ij i j p,
   ij = Z.mul (Z.of_nat i) (Z.of_nat j) -> 
   0 < Z.of_nat i <= Int.max_signed ->
    0 < Z.of_nat j <= Int.max_signed ->
    Z.of_nat i * Z.of_nat j <= Int.max_signed ->
   @data_at_ compspecs sh (tarray tdouble ij) p |--
   densematn sh (@const_mx (option (ftype Tdouble)) i j None) p.
Proof.
intros.
unfold densematn.
entailer!!.
change (ctype_of_type _) with tdouble.
rewrite densemat_lemmas.column_major_const.
simpl.
rewrite data_at__eq.
apply derives_refl'.
set (ij := Z.mul (Z.of_nat _) (Z.of_nat _)).
unfold default_val. simpl.
unfold reptype_ftype; simpl.
unfold data_at.
unfold field_at, field_compatible.
f_equal.
f_equal.
f_equal.
f_equal.
f_equal.
f_equal.
unfold align_compatible.
destruct p; auto.
set (c1 := @cenv_cs _); clearbody c1.
set (c2 := @cenv_cs _); clearbody c2.
clearbody ij.
clear.
apply prop_ext.
split; intro H; inv H; try inv H0; constructor; intros; simpl; econstructor; try reflexivity; simpl;
apply H4 in H; inv H; inv H0; auto.
Qed.


(** [end_densematn_in_frame] is used at the end of a scope, where you want to turn the 
   dense matrix (created by [begin_densemat_in_frame]) back into an array, so it can be deallocated. *)
Lemma end_densematn_in_frame:
  forall compspecs sh i j M p,
   @densematn Tdouble sh i j M p |--
   @data_at_ compspecs sh (tarray tdouble (Z.mul (Z.of_nat i) (Z.of_nat j))) p.
Proof.
intros.
unfold densematn.
entailer!!.
change (ctype_of_type _) with tdouble.
rewrite data_at__eq.
unfold default_val. simpl.
unfold reptype_ftype; simpl.
apply derives_trans with (@data_at spec_densemat.CompSpecs sh (tarray tdouble (i * j)) (@Zrepeat val Vundef (i * j)) p
).
apply data_at_data_at_.
unfold data_at.
unfold field_at, field_compatible.
apply andp_derives.
apply prop_derives. intros [? [? [? [? ?]]]]. split3; auto.
split3; auto.
clear - H5.
hnf in H5|-*. destruct p; simpl in H5|-*; auto.
inv H5. inv H. constructor. intros. specialize (H3 _ H). simpl in H3.
inv H3. econstructor; try eassumption.
apply derives_refl.
Qed.

(** [begin_densematn_in_frame] is used when you already have an array of floats/doubles
   that you want to treat as a dense matrix.  That is, you don't want to call [densemat_alloc].
   Typical example is a stack-allocated (local-variable) array.  This tactic looks for an entailment
   with an uninitialized array of doubles at address p in the precondition, and a matching 
   uninitialized dense matrix at address p in the postcondition, and automatically applies the lemma. *)
Ltac begin_densematn_in_frame := 
lazymatch goal with |- ?A |-- ?B =>
 match A with context [@data_at_ ?compspecs ?sh (tarray tdouble ?n) ?p] =>
  match B with context [densematn sh  (@const_mx _ ?i ?j None)  p ] =>
    tryif unify (Z.of_nat (i*j)) n 
    then sep_apply (begin_densematn_in_frame compspecs sh n i j p); try rep_lia
    else fail 2 "begin_densematn_in_frame requires n in [data_at _ (tarray tdouble n)" p "] to match product of matrix dimensions of [densematn _" p 
                 "] but you have " n " and "i"*"j
end end end.

(** [end_densemat_in_frame] automatically converts a dense matrix back into an uninitialized array.
   It looks for an entailment with a densematn at address p in the precondition, and a matching
    uninitialized array at address p in the postcondition. *)
Ltac end_densematn_in_frame := 
lazymatch goal with |- ?A |-- ?B =>
 match B with context [@data_at_ ?compspecs ?sh (tarray tdouble ?n) ?p] =>
  match A with context [@densematn _ sh ?i ?j ?m p] =>
    tryif unify (Z.of_nat (i*j)) n 
    then sep_apply (end_densematn_in_frame compspecs sh i j m p)
    else fail 2 "begin_densematn_in_frame requires n in [data_at _ (tarray tdouble n)" p "] to match product of matrix dimensions of [densematn _" p 
                 "] but you have " n " and "i"*"j
end end end.
