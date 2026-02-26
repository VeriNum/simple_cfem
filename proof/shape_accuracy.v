From CFEM Require Import shape shapefloat.
From mathcomp Require Import Rstruct.

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
From LAProof Require Import matrix_model.


Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Definition _x : ident := 1%positive.  (* Variable name for position *)

Existing Instance FPCompCert.nans.

Definition x_vmap_list (x : ftype Tdouble) :=
   [(1%positive, existT ftype _ x)].

Definition x_vmap (x : ftype Tdouble) : valmap :=
 ltac:(make_valmap_of_list (x_vmap_list x)).

(*
Ltac make_vmap_of_list_float xs :=
   make_valmap_of_list (map (fun ix => (fst ix, existT ftype _ (snd ix))) (seq.zip (vars (length xs)) xs)).

Definition x_vmap (x: ftype Tdouble) :=
  ltac:(let z := make_vmap_of_list_float [x] in exact z).

Definition x_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (cuboid_bound [_x])) in exact z).

*)

Definition cuboid_bounds (vars: list ident) : list varinfo := map (fun i => Build_varinfo Tdouble i (-1) 1) vars.
Definition simplex_bounds (vars: list ident) : list varinfo := map (fun i => Build_varinfo Tdouble i 0 1) vars.

Import matrix matrix_util fintype.

Ltac changeStdLibToCore f :=
 lazymatch f with 
 | @FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble => constr:(@BMULT FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble => constr:(@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble => constr:(@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble => constr:(@BOPP FPCompCert.nans Tdouble is_standard_Tdouble)
 | ?A ?B => let a := changeStdLibToCore A in let b := changeStdLibToCore B in constr:(a b)
 | _ => constr:(f)
 end.

Ltac red_to_rowmx f := 
match f with rowmx_of_list _ => f
 | _ => let g := eval red in f in red_to_rowmx g
end.

Ltac nthtac n L :=
 match n with
 | O => match L with ?A :: _ => A end
 | S ?n' => match L with _ :: ?A => nthtac n' A end
 end.

Ltac matrix_expression shape x i j := 
let f := constr:(shape (const_mx x)) in
let f := red_to_rowmx f in
let f := eval cbv zeta in f in 
let f := changeStdLibToCore f in 
match f with rowmx_of_list ?A =>
 let An := nthtac j A in  
 match An with context C [fun_of_matrix (const_mx x) _ ?k] =>
  unify (nat_of_ord k) i;
 let g := context C [x] in 
  exact g
end end.

Lemma ord_enum_cases: forall [n] (P: 'I_n -> Prop),
  Forall P (ord_enum n) ->
  forall i, P i.
Proof.
intros.
rewrite Forall_forall in H.
apply H.
clear.
pose proof @nth_ord_enum' n i i.
rewrite mv_mathcomp.nth_List_nth in H.
rewrite <- H.
apply nth_In.
rewrite size_ord_enum.
pose proof (ltn_ord i); lia.
Qed. 

Ltac is_ground_nat x := lazymatch x with O => idtac | S ?k => is_ground_nat k end.

Ltac compute_ord_enum n := 
  (is_ground_nat n + fail "compute_ord_enum: Need a ground term natural number, but got" n); 
  pattern (ord_enum n); 
  match goal with |- ?F _ => 
    let f := fresh "f" in set (f:=F);
      let c := constr:(ord_enum n) in let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with (eq_refl true) by apply proof_irr; clear e | try (contradiction e; reflexivity)]);
     subst f
  end.

Ltac ord_enum_cases j :=
 lazymatch type of j with ordinal ?n => 
  pattern j; 
  apply ord_enum_cases;
  compute_ord_enum n;
  repeat apply Forall_cons; try apply Forall_nil
 end.

Ltac realify := 
change (@nmodule.Algebra.add _) with Rplus;
change (@nmodule.Algebra.opp _) with Ropp;
change (@ssralg.GRing.mul _) with Rmult;
change (@ssralg.GRing.inv _) with Rinv;
change (ssralg.GRing.one _) with 1;
repeat change (nmodule.Algebra.natmul _ ?i) with (INR i).


Definition cuboid1_bmap : boundsmap := 
 ltac:(let z := compute_PTree (boundsmap_of_list (cuboid_bounds [_x])) in exact z).


Definition f_1dP1_0 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression shapes1dP1_float x 0%nat 0%nat).

Definition f_1dP1_1 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (FShape.θ shapes1dP1F) x 0%nat 1%nat).

Definition r_1dP1_0 := ltac:(let e' :=
  HO_reify_float_expr constr:([_x]) f_1dP1_0 in exact e').

Definition r_1dP1_1 := ltac:(let e' :=
  HO_reify_float_expr constr:([_x]) f_1dP1_1 in exact e').

Definition acc_1dP1 : R := 12 / IZR (Z.pow_pos 10 17).

Lemma prove_roundoff_bound_1dP1_0:  
    forall vmap,  prove_roundoff_bound cuboid1_bmap vmap r_1dP1_0 acc_1dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_1dP1_1:  
    forall vmap,  prove_roundoff_bound cuboid1_bmap vmap r_1dP1_1 acc_1dP1.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Derive acc_1dP1_0
 in  (forall vmap,  prove_roundoff_bound cuboid1_bmap vmap r_1dP1_0 acc_1dP1_0)
 as derive_roundoff_bound_1dP1_0.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_1dP1_0).

Lemma roundoff_bound_1dP1 : forall (x: 'rV[ftype Tdouble]_1) (j: 'I_2),
       FPCore.is_finite (x ord0 ord0) = true ->
       -1 <= FT2R (x ord0 ord0) <= 1 ->
       @FPCore.is_finite Tdouble (FShape.θ shapes1dP1F x ord0 j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (FShape.θ shapes1dP1F x)) 
                    (oppmx (Shape.θ shapes1dP1 (map_mx FT2R x)))
                      ord0 j) <= acc_1dP1.
Proof.
intros.
set (x00 := x ord0 ord0) in *.
assert (boundsmap_denote cuboid1_bmap (x_vmap x00)). {
 apply boundsmap_denote_i; simpl; auto.
 eexists. split; [  |split]; auto. reflexivity. split; auto.
}
ord_enum_cases j; clear j.
-
destruct (prove_roundoff_bound_1dP1_0 (x_vmap x00) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
set (fx := FShape.θ _ _ _ _); change (FShape.θ _ _ _ _) with fx.
assert (fx = fval (env_ (x_vmap x00)) r_1dP1_0). {
 subst fx. simpl. unfold shapes1dP1_float. unfold rowmx_of_list; row_col_matrix_tac. reflexivity.
}
rewrite H4; clear H4 fx.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
f_equal.
unfold r_1dP1_0.
simpl.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
change (x _ _) with x00.
change (env_ _ _ _ _x) with x00.
unfold Defs.F2R; simpl; nra.
-
destruct (prove_roundoff_bound_1dP1_1 (x_vmap x00) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
set (fx := FShape.θ _ _ _ _); change (FShape.θ _ _ _ _) with fx.
assert (fx = fval (env_ (x_vmap x00)) r_1dP1_1). {
 subst fx. simpl. unfold shapes1dP1_float. unfold rowmx_of_list; row_col_matrix_tac. reflexivity.
}
rewrite H4; clear H4 fx.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
f_equal.
unfold r_1dP1_1.
simpl.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
change (x _ _) with x00.
change (env_ _ _ _ _x) with x00.
unfold Defs.F2R; simpl; nra.
Qed.


