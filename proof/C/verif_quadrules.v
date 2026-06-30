Require Export VST.floyd.proofauto.
From vcfloat Require Export FPStdCompCert FPStdLib.
From LAProof.accuracy_proofs Require Export solve_model.
From LAProof.C Require Export floatlib.
From Stdlib Require Export Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Export ssrZ zify.
Export fintype matrix.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

From CFEM.C Require Import quadrules.
Require Export CFEM.C.spec_quadrules.


Definition quadrules_E : funspecs := [].
Definition quadrules_internal_specs : funspecs := quadrules_ASI.
Definition quadrules_imported_specs : funspecs := [].
Definition quadrules_globals gv : mpred:= gauss_pts_pred gv.

Definition Gprog := quadrules_imported_specs ++ quadrules_internal_specs.


Definition Fle [t: type] (x y: ftype t) : bool := BCMP Gt false x y.


Lemma Fle_Rle [t: type] (x y: ftype t):
  Binary.is_finite x = true -> Binary.is_finite y = true -> 
  Fle x y = Rle_bool (FT2R x) (FT2R y).
Proof.
intros.
unfold Fle, BCMP, extend_comp.
rewrite Binary.Bcompare_correct; auto.
Qed.

Lemma Fle_Rle' [t: type] (x y: ftype t):
  Binary.is_finite x = true -> Binary.is_finite y = true -> 
  Fle x y = true ->
  Rdefinitions.Rle (FT2R x) (FT2R y).
Proof.
intros.
rewrite Fle_Rle in H1; auto.
destruct (Rle_bool_spec (FT2R x) (FT2R y)); auto; discriminate.
Qed.

Lemma divs_repr: forall i j, 
  Int.min_signed <= i <= Int.max_signed ->
  Int.min_signed <= j <= Int.max_signed -> 
  Int.divs (Int.repr i) (Int.repr j) = Int.repr (i ÷ j).
Proof.
intros.
unfold Int.divs.
f_equal. f_equal; apply Int.signed_repr; auto.
Qed.

Lemma body_gauss_point: semax_body Vprog Gprog f_gauss_point gauss_point_spec_lowlevel.
Proof.
start_function.
unfold gauss_pts_pred.
assert (0 <= npts * (npts-1) <= 90) by nia.
assert (0 <= npts * (npts - 1) ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr (npts * (npts - 1))) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_pts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
split.
rewrite divs_repr; try rep_lia.
rewrite Int.signed_repr; try rep_lia.
intros [? ?]. inv H5.
-
change (Zlength _) with 55 in H3.
rewrite divs_repr in H3|-*; try rep_lia.
rewrite add_repr in H3|-*.
rewrite Int.signed_repr in H3|-*; try rep_lia.
rewrite Znth_map by auto.
forward.
clear - H0 H.
apply prop_right. 
f_equal. f_equal. f_equal. 
apply Zquot.Zquot_Zdiv_pos; nia.
Qed.

Lemma body_gauss_weight: semax_body Vprog Gprog f_gauss_weight gauss_weight_spec_lowlevel.
Proof.
start_function.
unfold gauss_wts_pred.
assert (0 <= npts * (npts-1) <= 90) by nia.
assert (0 <= npts * (npts - 1) ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr (npts * (npts - 1))) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_wts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
split.
rewrite divs_repr; try rep_lia.
rewrite Int.signed_repr; try rep_lia.
intros [? ?]. inv H5.
-
change (Zlength _) with 55 in H3.
rewrite divs_repr in H3|-*; try rep_lia.
rewrite add_repr in H3|-*.
rewrite Int.signed_repr in H3|-*; try rep_lia.
rewrite Znth_map by auto.
forward.
clear - H0 H.
apply prop_right. 
f_equal. f_equal. f_equal. 
apply Zquot.Zquot_Zdiv_pos; nia.
Qed.

