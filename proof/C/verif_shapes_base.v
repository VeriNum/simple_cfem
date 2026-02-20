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

