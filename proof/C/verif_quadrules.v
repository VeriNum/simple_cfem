Require Export VST.floyd.proofauto.
From vcfloat Require Export FPStdCompCert FPStdLib.
From LAProof.accuracy_proofs Require Export solve_model.
From LAProof.C Require Export floatlib.
From Stdlib Require Export Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Export ssrZ zify.
Import fintype matrix.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

From CFEM.C Require Import quadrules spec_quadrules spec_quadrules_highlevel.
(*From CFEM Require g_max_deriv.*)

Import quadmodel.Quadmodel_F64.

Definition quadrules_E : funspecs := [].
Definition quadrules_internal_specs : funspecs := quadrules_ASI.
Definition quadrules_imported_specs : funspecs := [].
Definition quadrules_globals gv : mpred:= gauss_pts_pred gv.

Definition Gprog := quadrules_imported_specs ++ quadrules_internal_specs.

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
assert (0 <= (npts+1) * npts <= 90) by nia.
assert (0 <= (npts+1) * npts ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr ((npts+1) * npts)) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_pts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward; rewrite ?Z.add_simpl_r.
- entailer!!.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
rewrite ?Z.add_simpl_r.
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
assert (0 <= (npts+1) * npts <= 90) by nia.
assert (0 <= (npts+1) * npts ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr ((npts+1) * npts)) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_wts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward; rewrite ?Z.add_simpl_r.
- entailer!!.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
rewrite ?Z.add_simpl_r.
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

Lemma body_gauss2d_npoint1d: semax_body Vprog Gprog f_gauss2d_npoint1d gauss2d_npoint1d_spec.
Proof.
start_function.
assert (repable_signed (s*s)).  (* See https://github.com/PrincetonUniversity/VST/issues/858  *)
  unfold repable_signed, Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, Int.wordsize.
  simpl. nia. 
forward_if False.
1-5: forward; entailer!!; f_equal; f_equal; nia.
rewrite !Int.unsigned_repr in NE,NE0,NE1,NE2,NE3 by rep_lia.
exfalso.
destruct s; try nia.
destruct p; try nia.
Qed.

Lemma body_gauss2d_point: semax_body Vprog Gprog f_gauss2d_point gauss2d_point_spec.
Proof.
start_function.
change (ssrnat.addn ?A ?B) with (A + B)%nat.
change (ssrnat.muln ?A ?B) with (A*B)%nat.
set (i := Z.of_nat _).
set (n1 := Z.pos _).
forward_call (Z.of_nat (S n)).
entailer!!. simpl. f_equal. f_equal. f_equal. lia.
destruct n as [n Hn]; simpl.
pose proof (@ssrnat.ltP n 4). rewrite Hn in H. inv H.
destruct x as [x Hx]. simpl in Hx.
pose proof (@ssrnat.ltP x (S n)). rewrite Hx in H. inv H. lia.
destruct n as [n Hn].
pose proof (@ssrnat.ltP n 4). rewrite Hn in H. inv H.
destruct x as [x Hx].
pose proof (@ssrnat.ltP x (S n)). simpl in Hx; rewrite Hx in H. inv H.
destruct y as [y Hy].
pose proof (@ssrnat.ltP y (S n)). simpl in Hy; rewrite Hy in H. inv H.
assert (H3: 0 <= Z.of_nat (y * (S n) + x) <= 25) by nia.
simpl  nat_of_ord in i, n1.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
simpl nat_of_ord.
rewrite divs_repr; try rep_lia.
rewrite mods_repr; try rep_lia.
pose (X := existT (fun n => 'I_(S (nat_of_ord n))) (Ordinal  Hn) (Ordinal Hx)).
forward_call sub_gauss_point (X, gv); clear X.
entailer!!.
change (firstn _ ?A) with A. change (eval_cast _ _ ?A) with A. simpl nat_of_ord.
subst i.
f_equal. f_equal. f_equal.
rewrite <- Nat2Z.inj_mod. f_equal.
rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod, Nat.Div0.mod_same, Nat.mul_0_r, Nat.Div0.mod_0_l, Nat.add_0_l.
rewrite Nat.Div0.mod_mod, Nat.mod_small; try lia.
Intros x'.
forward.
pose (X := existT (fun n => 'I_(S (nat_of_ord n))) (Ordinal  Hn) (Ordinal Hy)).
forward_call sub_gauss_point (X,gv); clear X.
entailer!!.
change (firstn _ ?L) with L.
f_equal.
change (eval_cast _ _ ?A) with A.  f_equal. f_equal.
subst i.
simpl nat_of_ord.
rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
Intros y'.
forward.
Exists x' y'.
entailer!!.
Qed.

Lemma body_gauss2d_weight: semax_body Vprog Gprog f_gauss2d_weight gauss2d_weight_spec.
Proof.
start_function.
change (ssrnat.addn ?A ?B) with (A + B)%nat.
change (ssrnat.muln ?A ?B) with (A*B)%nat.
set (i' := Z.of_nat _).
set (n1 := Z.pos _).
forward_call (Z.of_nat (S n)).
entailer!!. simpl. f_equal. f_equal. f_equal. lia.
destruct n as [n Hn]; simpl.
pose proof (@ssrnat.ltP n 4). rewrite Hn in H. inv H. lia.
destruct i as [i Hi]. destruct j as [j Hj]. destruct n as [n Hn]. simpl nat_of_ord in *.
assert (H3: 0 <= Z.of_nat (j * (S n) + i) <= 25) by nia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
simpl nat_of_ord.
rewrite divs_repr; try rep_lia.
rewrite mods_repr; try rep_lia.
pose (X := existT (fun n => 'I_(S (nat_of_ord n))) (Ordinal  Hn) (Ordinal Hi)).
forward_call sub_gauss_weight (X, gv); clear X.
entailer!!.
change (firstn _ ?A) with A. change (eval_cast _ _ ?A) with A. simpl nat_of_ord.
f_equal. f_equal. f_equal.
subst i'.
rewrite <- Nat2Z.inj_mod. f_equal.
rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod, Nat.Div0.mod_same, Nat.mul_0_r, Nat.Div0.mod_0_l, Nat.add_0_l.
rewrite Nat.Div0.mod_mod, Nat.mod_small; try lia.
Intros x'.
pose (X := existT (fun n => 'I_(S (nat_of_ord n))) (Ordinal  Hn) (Ordinal Hj)).
forward_call sub_gauss_weight (X,gv); clear X.
entailer!!.
change (firstn _ ?L) with L.
f_equal.
change (eval_cast _ _ ?A) with A.  f_equal. f_equal.
subst i'.
simpl nat_of_ord.
rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
Intros y'.
forward.
Exists x' y'.
entailer!!.
Qed.

Lemma body_hughes_point: semax_body Vprog Gprog f_hughes_point hughes_point_spec.
Proof.
start_function.
destruct i as [i Hi]. simpl.
forward_if False.
1,2,3:
forward; forward; forward;
do 2 EExists; entailer!!; [ | apply derives_refl]; simpl nat_of_ord; rewrite E; unfold Znth; simpl; f_equal;
unfold FT2R;
with_strategy transparent [Float.of_bits] simpl; compute; Lra.lra.
rewrite !Int.unsigned_repr in *; try rep_lia.
Qed.


Import Rdefinitions Rbasic_fun.

Lemma body_hughes_weight: semax_body Vprog Gprog f_hughes_weight hughes_weight_spec.
Proof.
start_function.
forward.
EExists.
entailer!!.
red. 
change Float.div with (@BDIV _ Tdouble).
with_strategy transparent [Float.of_bits] unfold Float.of_bits.
rewrite !Int64.unsigned_repr by rep_lia.
set (d := common.default_rel); hnf in d; simpl in d; subst d.
set (x := (_ / _)%F64).
unfold Bits.b64_of_bits, Bits.binary_float_of_bits, Binary.FF2B in x.
simpl in x.
hnf in x.
revert x.
set (H := proj1 _). clearbody H. simpl in H.
simpl.
unfold Defs.F2R, Defs.Fnum, Defs.Fexp.
unfold hughes_weight.
rewrite (Rabs_right (_ * _)%R).
2: compute; Lra.nra.
rewrite Rabs_left; compute; Lra.lra.
Qed.

Import quadmodel. Import Quadmodel_F64.
Import mv_mathcomp.

Definition integrate_upto (f: ftype Tdouble -> ftype Tdouble) (n: 'I_4) (i: Z) :=
    seq.foldl (fun s i => BPLUS s (BMULT (gauss_weight_f n i) (f (gauss_point_f n i)))) common.pos_zero 
           (sublist 0 i (ord_enum (S n))).


Lemma integrate_upto_n: forall f n,
  integrate_upto f n (Z.of_nat (S n)) = 
   integrate_model_f Tdouble _ n (gauss_point_f n) (gauss_weight_f n) f.
Proof.
intros.
unfold integrate_upto.
rewrite sublist_same; try lia; auto.
rewrite Zlength_correct. change @Datatypes.length with @seq.size.
rewrite size_ord_enum; auto.
Qed.

Lemma body_integrate: semax_body Vprog Gprog f_integrate integrate_spec_lowlevel.
Proof.
start_function.
forward.
forward_for_simple_bound (Z.of_nat (S n))
  (EX i: Z, PROP() 
  LOCAL (temp _s (Vfloat (integrate_upto f n i));
                 gvars gv; temp _f p; temp _n (Vint (Int.repr (Z.of_nat (S (nat_of_ord n))))))
   SEP (gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p)).
- destruct n as [n Hn]. simpl. clear - Hn. rep_lia.
- entailer!!.
- destruct n as [n Hn]. simpl nat_of_ord in H|-*.
  assert  (H0 := @ssrnat.ltP n 4). rewrite Hn in H0. inv H0.
  rewrite inj_S.
  forward_call (Z.of_nat n, i, gv). 
  forward_call (Z.of_nat n, i, gv).
  set (pt := Znth _ gauss_pts_list).
  set (wt := Znth _ gauss_wts_list).
  assert (Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) (S n))).
  destruct (@ssrnat.leP (S (Z.to_nat i))  (S n) ); try reflexivity; try lia. rename H0 into Hi.
  pose (i' := Ordinal Hi).
  replace pt with (gauss_point_f (Ordinal Hn) i').
2:{ unfold pt, gauss_point_f. f_equal; f_equal. simpl nat_of_ord. f_equal. f_equal. simpl. lia. simpl. lia. }
  replace wt with (gauss_weight_f (Ordinal Hn) i').
2:{ unfold wt, gauss_weight_f. f_equal; f_equal. simpl nat_of_ord. f_equal. f_equal. simpl. lia. simpl. lia. }
  clear pt wt.
  forward_call.
  forward.
  entailer!!.
  f_equal. simpl nat_of_ord. rewrite inj_S. split; auto. f_equal.
  unfold integrate_upto. simpl nat_of_ord.

  assert (Zlength (ord_enum (S n)) = Z.of_nat (S n)). {
    rewrite Zlength_correct. change @Datatypes.length with @seq.size.
   rewrite size_ord_enum; auto.
 }
  rewrite (sublist_split 0 i (i+1)) by lia.
  simpl.
  assert (Inh: Inhabitant 'I_(S n)) by  apply i'.
  rewrite sublist_len_1 by lia.
  replace (Znth i _) with i'. 
    2:{ unfold Znth. rewrite if_false by lia. rewrite <- nth_List_nth.
         replace (Z.to_nat i) with (nat_of_ord i') by (simpl; lia).
          rewrite nth_ord_enum'. auto.
    }
 rewrite seq.foldl_cat.
 reflexivity.
-
  forward.
 rewrite integrate_upto_n.
 entailer!!.
Qed.

Import quadrature quadrature2 Legendre quadmodel_accuracy.

Require Import Interval.Tactic.
Lemma f_i_cond: finite_integrate_condition Tdouble n testfun_fb testfun_d testfun_f_acc.
Proof.
red.
unfold testfun_fb, testfun_f_acc; simpl.
unfold maxwf, common.g, common.default_rel, common.default_abs, common.fmax.
interval.
Qed.

Lemma body_integrate_testfun: semax_body Vprog Gprog f_integrate_testfun integrate_testfun_spec.
Proof.
start_function.
make_func_ptr _testfun.
forward_call sub_integrate (testfun_f, testfun_r, testfun_fb, testfun_f_acc, testfun_d, gv _testfun, n, testfun_b, gv).
repeat apply conj.
apply testfun_quadrature_error_bound.
apply testfun_fbound.
apply testfun_deriv_bound.
apply testfun_function_accuracy.
apply testfun_parameter_limits.
apply f_i_cond.
Intros y.
forward.
Exists y.
entailer!!; [ | apply func_ptr'_emp].
eapply RIneq.Rle_trans; [apply H | ].
unfold integrate_model_acc, maxwf, testfun_fb, testfun_b, testfun_d, testfun_f_acc,
  common.default_rel, common.default_abs.
simpl.
clear.
prepare_for_interval.
interval.
Qed.

