(** * CFEM.C.verif_shapes2d:  VST correctness proofs for 2-dimensional shape functions *)
(** except that 2dP2 is in another file *)

Require Import CFEM.C.verif_shapes_base.

Lemma split_matrix_rows :
forall (sh : share) (n1 n2 : nat) (A : 'M[option (ftype the_type)]_(n1,1)) (B : 'M[option (ftype the_type)]_(n2,1)) (p : val),
(0 < n1)%nat ->
(0 < n2)%nat ->
Z.of_nat (n1 + n2) <= Int.max_signed ->
@field_compatible spec_densemat.CompSpecs (tarray the_ctype (Z.of_nat (n1 + n2))) [] p ->
densematn sh (col_mx A B) p =
densematn sh A p *
densematn sh B (@field_address spec_densemat.CompSpecs (tarray the_ctype (Z.of_nat n1 + Z.of_nat n2)) (SUB (Z.of_nat n1)) p).
Admitted.

(** #<a id=2dP1># *)
Lemma body_shapes2dP1: semax_body Vprog Gprog f_shapes2dP1 shapes2dP1_spec.
(* begin details *)
Proof.
unfold shapes2dP1_spec, shape_spec, shapes2dP1F.
start_function.
assert_PROP (isptr pxx /\ headptr v_dNx /\ headptr v_Nx /\ headptr v_dNy /\ headptr v_Ny). 
    (* why doesn't [isptr pxx] work automatically? *)
{ set (mm := map_mx Some x).
   sep_apply (densematn_local_facts shxx _ _ mm pxx).
   Intros. entailer!. destruct H4; auto.
}
assert_PROP (@field_compatible spec_densemat.CompSpecs (tarray the_ctype (Z.of_nat 2)) [] pxx)
  by entailer!.
decompose [and] H1; clear H1.
assert (Hrow_x: col_mx (row (@Ordinal 2 0 (eq_refl _)) x) (row (@Ordinal 2 1 (eq_refl _)) x) = x). {
clear.
etransitivity; [ | apply vsubmxK].
f_equal;
apply matrixP; intros i j; unfold row, usubmx, dsubmx, lshift, rshift; rewrite !mxE; rewrite !ord1; f_equal; apply ord_inj; simpl; rewrite ord1; auto.
}
rewrite <-Hrow_x.
set (x' := @map_mx (ftype the_type) (option (ftype the_type)) (@Some (ftype the_type)) 2 1 _).
change 2%nat with (ssrnat.addn 1 1)%nat in x'.
revert x'.
rewrite map_col_mx.
cbv zeta.
rewrite (split_matrix_rows shxx 1 1); try rep_lia; auto.
Intros.
forward_call (Tsh, shxx, v_Nx, v_dNx, row (ord0: 'I_2) x, pxx). {
  rewrite (ifptr_true v_Nx) by auto.
  rewrite (ifptr_true v_dNx) by auto.
begin_densematn_in_frame.
begin_densematn_in_frame.
  change Tdouble with the_type.
  replace ord0 with (@Ordinal 2 0 (eq_refl _)) by (apply ord_inj; reflexivity).
  cancel.
}
simpl field_address.
simpl in H2. change (ctype_of_type _) with the_ctype in H2.
forward_call(Tsh, shxx, v_Ny, v_dNy, row (@Ordinal 2 1 (eq_refl _)) x, 
    @field_address spec_densemat.CompSpecs (tarray the_ctype 2) (SUB 1) pxx). {
 rewrite !ifptr_true by auto.
 rewrite (ifptr_true v_Ny) by auto.
 rewrite (ifptr_true v_dNy) by auto.
begin_densematn_in_frame.
begin_densematn_in_frame.
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
unfold matrix_util.mx_of_list. simpl. 
prove_matrices_same;
repeat (f_equal; try (apply ord_inj; reflexivity)).
*
forward.
entailer!!.
*
thaw FRZ2.
forward.
repeat end_densematn_in_frame.
cancel.
rewrite sepcon_comm.
rewrite <-(split_matrix_rows shxx 1 1); try lia; auto.
rewrite <- map_col_mx.
clear - Hrow_x.
replace (@ord0 1) with (@Ordinal 2 0 (eq_refl _)) by (apply ord_inj; reflexivity).
rewrite Hrow_x.
apply derives_refl.
Qed.
(* end details *)

Lemma body_shapes2dS2: semax_body Vprog Gprog f_shapes2dS2 shapes2dS2_spec.
(* begin details *)
Proof.
unfold shapes2dS2_spec, shape_spec, shapes2dS2F.
start_function.
assert_PROP (isptr pxx /\ headptr v_dNx /\ headptr v_Nx /\ headptr v_dNy /\ headptr v_Ny). 
    (* why doesn't [isptr pxx] work automatically? *)
{ set (mm := map_mx Some x).
   sep_apply (densematn_local_facts shxx _ _ mm pxx).
   Intros. entailer!. destruct H4; auto.
}
assert_PROP (@field_compatible spec_densemat.CompSpecs (tarray the_ctype (Z.of_nat 1 * Z.of_nat 2)) [] pxx)
  by entailer!.
decompose [and] H1; clear H1.
assert (Hrow_x: col_mx (row (@Ordinal 2 0 (eq_refl _)) x) (row (@Ordinal 2 1 (eq_refl _)) x) = x). {
clear.
etransitivity; [ | apply vsubmxK].
f_equal;
apply matrixP; intros i j; unfold row, usubmx, dsubmx, lshift, rshift; rewrite !mxE; rewrite !ord1; f_equal; apply ord_inj; simpl; rewrite ord1; auto.
}
rewrite <-Hrow_x.
set (x' := @map_mx (ftype the_type) (option (ftype the_type)) (@Some (ftype the_type)) 2 1 _).
change 2%nat with (ssrnat.addn 1 1)%nat in x'.
revert x'.
rewrite map_col_mx.
cbv zeta.
rewrite (split_matrix_rows shxx 1 1); try rep_lia; auto.
Intros.
forward_call (Tsh, shxx, v_Nx, v_dNx, row (ord0: 'I_2) x, pxx). {
  rewrite (ifptr_true v_Nx) by auto.
  rewrite (ifptr_true v_dNx) by auto.
begin_densematn_in_frame.
begin_densematn_in_frame.
  change Tdouble with the_type.
  replace ord0 with (@Ordinal 2 0 (eq_refl _)) by (apply ord_inj; reflexivity).
  cancel.
}
simpl field_address.
simpl in H2. change (ctype_of_type _) with the_ctype in H2.
forward_call(Tsh, shxx, v_Ny, v_dNy, row (@Ordinal 2 1 (eq_refl _)) x, 
    @field_address spec_densemat.CompSpecs (tarray the_ctype 2) (SUB 1) pxx). {
 rewrite !ifptr_true by auto.
 rewrite (ifptr_true v_Ny) by auto.
 rewrite (ifptr_true v_dNy) by auto.
begin_densematn_in_frame.
begin_densematn_in_frame.
 cancel.
}
rewrite ifptr_true by auto.
rewrite ifptr_true by auto.
freeze FRZ1 := -(ifptr pN _) (densematn _ _ v_Nx) (densematn _ _ v_Ny).
match goal with |- semax _ ?Pre _ _ =>
  match Pre with context C [ifptr pN ?B] =>
       let jj := context C [ifptr pN (densematn shN (map_mx Some (shapes2dS2_float x)) pN)] in
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
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
deadvars!.
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
abstract (
  unfold shapes2dS2_float;
  simpl map_mx; unfold map_mx; rewrite !mxE;
  prove_matrices_same;
  repeat (f_equal; try (apply ord_inj; reflexivity))).
+
forward.
entailer!!.
+
thaw FRZ1.
freeze FRZ2 := -(ifptr pdN _) (densematn _ _ v_Nx) (densematn _ _ v_Ny) (densematn _ _ v_dNx) (densematn _ _ v_dNy).
match goal with |- semax _ ?Pre _ _ =>
  match Pre with context C [ifptr pdN ?B] =>
       let jj := context C [ifptr pdN (densematn shN (map_mx Some (shapes2dS2_fderiv x)) pdN)] in
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
deadvars!.
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
abstract (
  unfold shapes2dS2_fderiv;
  simpl map_mx; unfold map_mx; rewrite !mxE;
  unfold matrix_util.mx_of_list; simpl;
  prove_matrices_same;
  repeat (f_equal; try (apply ord_inj; reflexivity))).
*
forward.
entailer!!.
*
thaw FRZ2.
forward.
repeat end_densematn_in_frame.
cancel.
rewrite sepcon_comm.
rewrite <-(split_matrix_rows shxx 1 1); try lia; auto.
rewrite <- map_col_mx.
clear - Hrow_x.
replace (@ord0 1) with (@Ordinal 2 0 (eq_refl _)) by (apply ord_inj; reflexivity).
rewrite Hrow_x.
apply derives_refl.
Qed.
(* end details *)

Lemma body_shapes2dT1: semax_body Vprog Gprog f_shapes2dT1 shapes2dT1_spec.
(* begin details *)
Proof.
unfold shapes2dT1_spec, shape_spec, shapes2dT1F.
start_function.
freeze PDN := (ifptr pdN _).
forward_if 
  (PROP ( )
   LOCAL (temp _N pN; temp _dN pdN; temp _x pxx)
   SEP (FRZL PDN; ifptr pN (densematn shN (map_mx Some (shapes2dT1_float x)) pN);
   densematn shxx (map_mx Some x) pxx)).
-
rewrite ifptr_true by auto.
forward_densematn_get_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_set_special.
forward_densematn_get_special.
forward_densematn_set_special.
rewrite (ifptr_true pN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
unfold shapes2dT1_float.
prove_matrices_same;
f_equal; apply ord_inj; reflexivity.
-
forward.
subst pN. rewrite !ifptr_false.
entailer!!.
-
thaw PDN.
freeze PN := (ifptr pN _).
forward_if
  (PROP ( )
   LOCAL (temp _N pN; temp _dN pdN; temp _x pxx)
   SEP (FRZL PN; ifptr pdN (densematn shN (map_mx Some (shapes2dT1_fderiv x)) pdN);
   densematn shxx (map_mx Some x) pxx)).
+
rewrite ifptr_true by auto.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
forward_densematn_set_special.
rewrite (ifptr_true pdN) by auto.
entailer!!.
apply derives_refl'.
f_equal.
clear.
unfold shapes2dT1_fderiv.
unfold matrix_util.mx_of_list; simpl;
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
Qed.
(* end details *)

