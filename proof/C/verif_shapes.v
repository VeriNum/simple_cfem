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

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Require Import CFEM.C.nonexpansive.
Import spec_densemat.

Open Scope logic.

Require Import CFEM.shapefloat CFEM.C.spec_shapes.
Import shapes.


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

(*
Ltac forward_densematn_get_special :=
 match goal with |- context [Scall (Some _) (Evar _densematn_get _)
                                             [Etempvar ?pvar _; Econst_int (Int.repr ?stride) _; 
                                              Econst_int (Int.repr ?i) _; Econst_int (Int.repr ?j) _]] =>

   match goal with |- context [temp pvar ?p] =>
    match goal with |- semax _ ?Pre _ _ => match Pre with context [densematn ?sh ?M p] =>
     match type of M with @matrix _ ?m ?n =>
      let i' := constr:(@Ordinal m (Z.to_nat i) (eq_refl _)) in
      let j' := constr:(@Ordinal n (Z.to_nat j) (eq_refl _)) in
        densemat_lemmas.forward_densematn_get M i'  j' p sh (optfloat_to_float (M i' j'))
    end end end end;
    [ try (unfold map_mx; rewrite !mxE; reflexivity) | ]
end.
*)

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


Ltac prove_matrices_same := 
 unfold  update_mx; simpl; unfold map_mx, row_mx, col_mx, const_mx; simpl;
 apply matrixP; intros [i Hi] [j Hj]; simpl;
 rewrite !mxE;
 repeat destruct (Nat.eq_dec _ _); simpl in *; subst; try discriminate; unfold split;
 repeat (destruct (ssrnat.ltnP _ _); simpl in *; try lia; rewrite !mxE);
 prove_float_exprs_same.

Lemma body_shapes1dP1: semax_body Vprog Gprog f_shapes1dP1 shapes1dP1_spec.
Proof.
unfold shapes1dP1_spec, shape_spec, shapes1dP1F.
start_function.
forward_densematn_get_special.
unfold map_mx at 1. rewrite mxE. simpl optfloat_to_float.
set (x00 := x _ _).
freeze PDN := (ifptr pdN _).
forward_if 
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx;
   ifptr pN (densematn shN (map_mx Some (shapes1dP1_float x)) pN);
   FRZL PDN)).
-
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
unfold shapes1dP1_float.
replace (x _ _) with x00 by (subst x00; f_equal; apply ord_inj; reflexivity).
prove_matrices_same.
-
forward.
subst pN. rewrite !ifptr_false.
entailer!!.
-
thaw PDN.
freeze PN := (ifptr pN _).
forward_if
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx; FRZL PN;
   ifptr pdN (densematn shN (map_mx Some (shapes1dP1_fderiv x)) pdN))).
+
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pdN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes1dP1_fderiv.
prove_matrices_same.
+
forward.
subst pdN.
rewrite !ifptr_false.
thaw PN.
entailer!!.
+
thaw PN.
forward.
cancel.
Qed.

Lemma body_shapes1dP2: semax_body Vprog Gprog f_shapes1dP2 shapes1dP2_spec.
Proof.
unfold shapes1dP2_spec, shape_spec, shapes1dP2F.
start_function.
forward_densematn_get_special.
unfold map_mx at 1. rewrite mxE. simpl optfloat_to_float.
set (x00 := x _ _).
freeze PDN := (ifptr pdN _).
forward_if 
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx;
   ifptr pN (densematn shN (map_mx Some (shapes1dP2_float x)) pN); 
   FRZL PDN)).
-
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
unfold shapes1dP2_float.
replace (x _ _) with x00 by (subst x00; f_equal; apply ord_inj; reflexivity).
prove_matrices_same.
-
forward.
subst pN. rewrite !ifptr_false.
entailer!!.
-
thaw PDN.
freeze PN := (ifptr pN _).
forward_if
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx; FRZL PN;
   ifptr pdN (densematn shN (map_mx Some (shapes1dP2_fderiv x)) pdN))).
+
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pdN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes1dP2_fderiv.
replace (x _ _) with x00 by (subst x00; f_equal; apply ord_inj; reflexivity).
prove_matrices_same.
+
forward.
subst pdN.
rewrite !ifptr_false.
thaw PN.
entailer!!.
+
thaw PN.
forward.
cancel.
Qed.

Lemma body_shapes1dP3: semax_body Vprog Gprog f_shapes1dP3 shapes1dP3_spec.
Proof.
unfold shapes1dP3_spec, shape_spec, shapes1dP3F.
start_function.
forward_densematn_get_special.
unfold map_mx at 1. rewrite mxE. simpl optfloat_to_float.
set (x00 := x _ _).
freeze PDN := (ifptr pdN _).
forward_if 
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx;
   ifptr pN (densematn shN (map_mx Some (shapes1dP3_float x)) pN); 
   FRZL PDN)).
-
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
unfold shapes1dP3_float.
replace (x _ _) with x00 by (subst x00; f_equal; apply ord_inj; reflexivity).
prove_matrices_same.
-
forward.
subst pN. rewrite !ifptr_false.
entailer!!.
-
thaw PDN.
freeze PN := (ifptr pN _).
forward_if
  (PROP ( )
   LOCAL (temp _x (val_of_float x00); 
   temp _N pN; temp _dN pdN; temp _xx pxx)
   SEP (densematn shxx (map_mx Some x) pxx; FRZL PN;
   ifptr pdN (densematn shN (map_mx Some (shapes1dP3_fderiv x)) pdN))).
+
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pdN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes1dP3_fderiv.
replace (x _ _) with x00 by (subst x00; f_equal; apply ord_inj; reflexivity).
prove_matrices_same.
+
forward.
subst pdN.
rewrite !ifptr_false.
thaw PN.
entailer!!.
+
thaw PN.
forward.
cancel.
Qed.

Lemma uninitialized_densematn:
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

Lemma densematn_uninitialized:
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

Lemma sublist_column_major_left: 
  forall m n1 n2 (A: 'M[option (ftype the_type)]_(m,n1)) (B: 'M[option (ftype the_type)]_(m,n2)),
   0 < n1 -> 0 < n2 -> 
   sublist 0 (Z.of_nat m * Z.of_nat n1) (column_major (row_mx A B)) = column_major A.
Admitted.

Lemma sublist_column_major_right: 
  forall m n1 n2 (A: 'M[option (ftype the_type)]_(m,n1)) (B: 'M[option (ftype the_type)]_(m,n2)),
   0 < n1 -> 0 < n2 -> 
   sublist (Z.of_nat m * Z.of_nat n1) (Z.of_nat m * Z.of_nat (n1+n2)) (column_major (row_mx A B)) = column_major B.
Admitted.

Lemma split_matrix_cols1: 
  forall sh m n1 n2 (A: 'M[option (ftype the_type)]_(m,n1)) (B: 'M[option (ftype the_type)]_(m,n2)) p,
   0 < n1 -> 0 < n2 -> 
   densematn sh (row_mx A B) p |-- 
   densematn sh A p * densematn sh B (@field_address  spec_densemat.CompSpecs (tarray the_ctype (m*(n1+n2))) (SUB (m*n1)) p).
Proof.
intros.
unfold densematn.
change (ssrnat.addn n1 n2) with (n1+n2)%nat.
repeat change (reptype_ftype _ ?A) with A.
Intros.
entailer!.
rewrite <- (sublist_same 0 (Z.of_nat m * Z.of_nat (n1+n2)) (column_major (row_mx _ _)));
  auto.
2: rewrite densemat_lemmas.Zlength_column_major; lia.
rewrite (sublist_split 0 (Z.of_nat m *Z.of_nat n1))
  by (rewrite ?densemat_lemmas.Zlength_column_major; lia).
rewrite map_app.
rewrite (split2_data_at_Tarray_app (Z.of_nat m * Z.of_nat n1)).
2,3: autorewrite with sublist; rewrite Zlength_sublist;
 rewrite ?densemat_lemmas.Zlength_column_major; list_solve.
rewrite sublist_column_major_left; auto.
rewrite sublist_column_major_right; auto.
cancel.
apply derives_refl'.
replace  (Z.of_nat m * Z.of_nat (n1 + n2) - Z.of_nat m * Z.of_nat n1)
  with (Z.of_nat m * Z.of_nat n2)%Z by lia.
f_equal.
rewrite field_address_offset by auto with field_compatible.
rewrite field_address0_offset by auto with field_compatible.
reflexivity.
Qed.


Lemma split_matrix_cols: 
  forall sh m n1 n2 (A: 'M[option (ftype the_type)]_(m,n1)) (B: 'M[option (ftype the_type)]_(m,n2)) p,
   0 < n1 -> 0 < n2 -> 
   @field_compatible spec_densemat.CompSpecs (tarray the_ctype (Z.of_nat m * Z.of_nat (n1+n2))) [] p ->
   densematn sh (row_mx A B) p = 
   densematn sh A p * densematn sh B (@field_address  spec_densemat.CompSpecs (tarray the_ctype (m*(n1+n2))) (SUB (m*n1)) p).
Proof.
intros.
apply pred_ext.
apply split_matrix_cols1; auto.
Admitted.  (* Should be OK *)

Lemma body_shapes2dP1: semax_body Vprog Gprog f_shapes2dP1 shapes2dP1_spec.
Proof.
unfold shapes2dP1_spec, shape_spec, shapes2dP1F.
start_function.
assert_PROP (isptr pxx /\ headptr v_dNx /\ headptr v_Nx /\ headptr v_dNy /\ headptr v_Ny). 
    (* why doesn't [isptr pxx] work automatically? *)
{ set (mm := map_mx Some x).
   sep_apply (densematn_local_facts shxx _ _ mm pxx).
   Intros. entailer!. destruct H4; auto.
}
assert_PROP (@field_compatible spec_densemat.CompSpecs (tarray (ctype_of_type the_type) (Z.of_nat 1 * Z.of_nat 2)) [] pxx)
  by entailer!.
decompose [and] H1; clear H1.
replace x with (row_mx (col (@Ordinal 2 0 (eq_refl _)) x) (col (@Ordinal 2 1 (eq_refl _)) x)).
2:{ apply matrixP. intros i j.
    unfold row_mx. rewrite ord1. clear i. rewrite mxE. unfold split. destruct (ssrnat.ltnP _ _).
   unfold col.
 rewrite mxE. f_equal. destruct j; try discriminate. apply ord_inj; auto.
       simpl in i. destruct m; try discriminate. simpl. auto.
   unfold col.
 rewrite mxE. f_equal. destruct j; try discriminate. apply ord_inj; auto.
       simpl in i. destruct m; try discriminate. simpl. destruct m; try discriminate; auto.
}
set (x' := @map_mx (ftype the_type) (option (ftype the_type)) (@Some (ftype the_type)) 1 2 _).
change 2%nat with (ssrnat.addn 1 1)%nat in x'.
revert x'.
rewrite map_row_mx.
cbv zeta.
rewrite (split_matrix_cols shxx 1 1 1); try lia; auto.
Intros.
forward_call (Tsh, shxx, v_Nx, v_dNx, col (ord0: 'I_2) x, pxx). {
  rewrite (ifptr_true v_Nx) by auto.
  rewrite (ifptr_true v_dNx) by auto.
  sep_apply (uninitialized_densematn CompSpecs Tsh 2 1 2 v_Nx); try rep_lia.
  sep_apply (uninitialized_densematn CompSpecs Tsh 2 2 1 v_dNx); try rep_lia.
  sep_apply (uninitialized_densematn CompSpecs Tsh 2 1 2 v_Ny); try rep_lia.
  sep_apply (uninitialized_densematn CompSpecs Tsh 2 2 1 v_dNy); try rep_lia.
  change Tdouble with the_type.
  replace ord0 with (@Ordinal 2 0 (eq_refl _)) by (apply ord_inj; reflexivity).
  cancel.
}
simpl field_address.
simpl in H2. change (ctype_of_type _) with the_ctype in H2.
forward_call(Tsh, shxx, v_Ny, v_dNy, col (@Ordinal 2 1 (eq_refl _)) x, 
    @field_address spec_densemat.CompSpecs (tarray the_ctype 2) (SUB 1) pxx). {
 rewrite !ifptr_true by auto.
 rewrite (ifptr_true v_Ny) by auto.
 rewrite (ifptr_true v_dNy) by auto.
 cancel.
}
rewrite ifptr_true by auto.
rewrite ifptr_true by auto.
freeze FRZ1 := -(ifptr pN _) (densematn _ _ v_Nx) (densematn _ _ v_Ny).
match goal with |- semax _ ?Pre _ _ =>
  match Pre with context C [ifptr pN ?B] =>
       let jj := context C [ifptr pN (densematn shN (map_mx Some (shapes2dP1_float x)) pN)] in
      forward_if jj
 end end.
+
rewrite (ifptr_true pN) by auto.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
rewrite (ifptr_true pN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes2dP1_float.
simpl map_mx. unfold map_mx; rewrite !mxE.
prove_matrices_same;
repeat (f_equal; try (apply ord_inj; reflexivity)).
+
forward.
entailer!!.
+
thaw FRZ1.
freeze FRZ2 := -(ifptr pdN _) (densematn _ _ v_Nx) (densematn _ _ v_Ny) (densematn _ _ v_dNx) (densematn _ _ v_dNy).
match goal with |- semax _ ?Pre _ _ =>
  match Pre with context C [ifptr pdN ?B] =>
       let jj := context C [ifptr pdN (densematn shN (map_mx Some (shapes2dP1_fderiv x)) pdN)] in
      forward_if jj
 end end.
*
rewrite (ifptr_true pdN) by auto.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
rewrite (ifptr_true pdN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes2dP1_fderiv.
simpl map_mx. unfold map_mx; rewrite !mxE.
prove_matrices_same;
repeat (f_equal; try (apply ord_inj; reflexivity)).
*
forward.
entailer!!.
*
thaw FRZ2.
forward.
match goal with |- context [densematn _ ?M v_Nx] => 
   sep_apply (densematn_uninitialized _ Tsh _ _ M v_Nx)
end.
match goal with |- context [densematn _ ?M v_Ny] => 
   sep_apply (densematn_uninitialized _ Tsh _ _ M v_Ny)
end.
match goal with |- context [densematn _ ?M v_dNx] => 
   sep_apply (densematn_uninitialized _ Tsh _ _ M v_dNx)
end.
match goal with |- context [densematn _ ?M v_dNy] => 
   sep_apply (densematn_uninitialized _ Tsh _ _ M v_dNy)
end.
cancel.
rewrite sepcon_comm.
rewrite <-(split_matrix_cols shxx 1 1 1); try lia; auto.
rewrite <- map_row_mx.
apply derives_refl'.
f_equal.
f_equal.
clear.
apply matrixP; intros i j.
unfold row_mx, col; rewrite mxE.
unfold split.
destruct (ssrnat.ltnP _ _).
destruct j as [j Hj]. destruct j; try discriminate. simpl in *. rewrite ord1.
rewrite !mxE. f_equal.  apply ord_inj; auto.
destruct j as [j Hj]. destruct j; try discriminate. simpl in *. destruct j; try discriminate. rewrite ord1.
rewrite !mxE. f_equal.  apply ord_inj; auto.
Qed.



