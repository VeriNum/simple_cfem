From CFEM Require Import shape shapefloat.
From mathcomp Require Import Rstruct.

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.


Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Definition _x : ident := 1%positive.  (* Variable name for position *)

Existing Instance FPCompCert.nans.

Definition x_vmap_list (x : ftype Tdouble) :=
   [(_x, existT ftype _ x)].

Definition x_vmap (x : ftype Tdouble) : valmap :=
 ltac:(make_valmap_of_list (x_vmap_list x)).


Check (0.5)%F64 : ftype Tdouble.

(* Definition xbound : R := FT2R((1000)%F64: ftype Tdouble).*)
Definition xbound : R := 3/4.

Definition x_bmap_list : list varinfo :=
  [ Build_varinfo Tdouble _x (-xbound) xbound].

Definition x_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list x_bmap_list) in exact z).

(*Definition f_1dP1_0 := ltac:(let e' :=
  HO_reify_float_expr constr:([_x]) (fun x: ftype Tdouble => Norm(0.5 * (1-x)))%F64 in exact e').
*)
Import matrix matrix_util fintype.

Ltac changeStdLibToCore f :=
let f := eval pattern (@FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble) in f in 
match f with ?A _ => let f := constr:(A (@BMULT FPCompCert.nans Tdouble is_standard_Tdouble)) in 
let f := eval pattern (@FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble) in f in 
match f with ?A _ => let f := constr:(A (@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble)) in 
let f := eval pattern (@FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble) in f in 
match f with ?A _ => let f := constr:(A (@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble)) in 
let f := eval pattern (@FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble) in f in 
match f with ?A _ => let f := constr:(A (@BOPP FPCompCert.nans Tdouble is_standard_Tdouble)) in 
let f := eval cbv beta in f in 
f
end end end end.

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
 let g := constr:(Norm g) in 
  exact g
end end.

Definition f_1dP1_0 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (FShape.θ shapes1dP1F) x 0%nat 0%nat).

Definition f_1dP1_1 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (FShape.θ shapes1dP1F) x 0%nat 1%nat).


Definition r_1dP1_0 := ltac:(let e' :=
  HO_reify_float_expr constr:([_x]) f_1dP1_0 in exact e').


Definition r_1dP1_1 := ltac:(let e' :=
  HO_reify_float_expr constr:([_x]) f_1dP1_1 in exact e').


Definition acc_1dP1 : R := 2 / IZR (Z.pow_pos 10 16).

Lemma prove_roundoff_bound_1dP1_0:  
    forall vmap,  prove_roundoff_bound x_bmap vmap r_1dP1_0 acc_1dP1.
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
    forall vmap,  prove_roundoff_bound x_bmap vmap r_1dP1_1 acc_1dP1.
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
 in  (forall vmap,  prove_roundoff_bound x_bmap vmap r_1dP1_0 acc_1dP1_0)
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

Lemma ord_enum_cases: forall [n] (P: 'I_n -> Prop),
  Forall P (ord_enum n) ->
  forall i, P i.
Proof.
intros.
rewrite Forall_forall in H.
apply H.
clear.
Admitted.

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
 match type of j with ordinal ?n => 
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

Lemma roundoff_bound_1dP1 : forall (x: 'rV[ftype Tdouble]_1) (j: 'I_2),
       FPCore.is_finite (x ord0 ord0) = true ->
       Rabs (FT2R (x ord0 ord0)) <= xbound ->
       @FPCore.is_finite Tdouble (FShape.θ shapes1dP1F x ord0 j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (FShape.θ shapes1dP1F x)) 
                    (oppmx (Shape.θ shapes1dP1 (map_mx FT2R x)))
                      ord0 j) <= acc_1dP1.
Proof.
intros.
set (x00 := x ord0 ord0) in *.
assert (boundsmap_denote x_bmap (x_vmap x00)). {
 apply boundsmap_denote_i; simpl; auto.
 eexists. split; [  |split]; auto. reflexivity. split; auto.
 apply Stdlib.Rabs_def2_le; auto.
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


