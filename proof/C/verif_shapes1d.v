Require Import CFEM.C.verif_shapes_base.

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