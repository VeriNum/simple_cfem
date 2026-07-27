(** * CFEM.quadrature2:  Computation of quadrature error bounds *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
Locate Ltac lra.
Import classical_sets.
Import numFieldNormedType.Exports.
From Stdlib Require Import FunctionalExtensionality.
From CFEM Require Import quadrature.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Legendre.
Require Import Interval.Tactic.
From mathcomp Require Import Rstruct.
Import trigo.

Notation R := (RbaseSymbolsImpl_R__canonical__reals_Real).

 Notation "∫" := intgal.

(* Because [derivable] is not locked, many simple kinds of proofs will tend to blow up.
  See this: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/very.20slow.20unification.20failure.2C.20derivable_sin.2C.20derivable_cos/with/612359969
  So at (* this line *) below, we must explicitly [apply H] instead of doing [assumption] or [auto].
  And also, Hint Resolve databases won't work.
*)


Lemma derive1M (f g: R -> R) (x: R) :
  derivable f x 1 ->
  derivable g x 1 ->
  (f  \* g)^`()%classic x = f x * g^`()%classic x + f^`()%classic x * g x.
Proof.
intros.
progress simpl.
rewrite ?derive1E.
rewrite deriveM.
-
f_equal.
rewrite mulrC.
rewrite /scale //.
-
apply H.  (* this line *)   (* see comment above *)
-
apply H0.
Qed.

Definition everywhere_derivable (f: R -> R) := forall x, derivable f x 1.

Lemma derive1M_ (f g: R -> R) :
  everywhere_derivable f ->
  everywhere_derivable g ->
  (mul_fun f g)^`()%classic = add_fun (mul_fun f (g^`()%classic)) (mul_fun (f^`()%classic) g).
Proof.
intros.
extensionality x.
rewrite derive1M; auto.
Qed.

Notation d1 := (@derive1 R (Real_sort__canonical__normed_module_NormedModule RbaseSymbolsImpl_R__canonical__reals_Real)).

Lemma derive1_cst': forall [V : normedModType R] (k : V) (t : R), 
   (fun=> k)^`()%classic t = 0.
Proof. intros; apply derive1_cst. Qed.

Lemma derive1_cos: d1 cos = opp_fun sin.
Proof.
extensionality x.
rewrite derive1E.
destruct (mathcomp.analysis.trigo.is_derive_cos x).
auto.
Qed.

Lemma derive1_sin: d1 sin = cos.
Proof.
extensionality x.
rewrite derive1E.
destruct (mathcomp.analysis.trigo.is_derive_sin x).
auto.
Qed.

Lemma derive1_add: forall (f g : R -> R), 
  everywhere_derivable f ->
  everywhere_derivable g ->
  d1 (f \+ g) = (d1 f \+ d1 g).
Proof.
intros.
extensionality x.
rewrite /= ?derive1E.
rewrite deriveD.
auto.
apply H.
apply H0.
Qed.

Lemma derive1_opp: forall (f : R -> R), 
  everywhere_derivable f->
  d1 (\- f) = \- (d1 f).
Proof.
intros.
extensionality x.
rewrite /= ?derive1E.
rewrite deriveN //.
Qed.

Lemma opp_funK: forall f: R -> R, opp_fun (opp_fun f) = f.
Proof.
intros.
extensionality x.
simpl.
rewrite opprK //.
Qed.

Lemma ev_deriv_cos: everywhere_derivable cos.
Proof.
intro.
apply derivable_cos.
Qed.

Lemma ev_deriv_sin:  everywhere_derivable sin.
Proof.
intro.
apply derivable_sin.
Qed.

Lemma range_Rabs: forall x, is_true (-1 <= x <= 1) -> Rdefinitions.Rle (Rbasic_fun.Rabs x) 1.
Proof.
intros.
apply Stdlib.Rabs_def1_le; apply /RleP.
lra.
change (is_true (- 1 <= x)). lra.
Qed.

Lemma derivE_rev :
forall (p : {poly Num_RealField__to__GRing_NzSemiRing R}),
 (horner p)^`()%classic = horner p^`().
Proof. intros. symmetry. apply derivE. Qed.

Lemma ev_deriv_horner: forall p: {poly R}, everywhere_derivable (horner p).
Proof.
intros. intro. apply derivable_horner.
Qed.

Lemma ev_derivD: forall  (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \+ g).
Proof.
intros. intro. apply (@derivableD _ _ _ f g); auto.
Qed.

Lemma ev_derivB: forall  (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \- g).
Proof.
intros. intro. apply (@derivableB _ _ _ f g); auto.
Qed.

Lemma ev_derivN: forall (f : R -> R),
    everywhere_derivable f -> everywhere_derivable (\- f).
Proof.
intros. intro. apply derivableN; auto.
Qed.

Lemma ev_derivM: forall (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \* g).
Proof.
intros. intro. apply derivableM; auto.
Qed.

Lemma ev_deriv_cst: forall (c: R),
    everywhere_derivable (functions.cst c).
Proof.
intros. intro. apply derivable_cst.
Qed.

Ltac derivable := 
  with_strategy opaque [derive.derivable]  
  solve [repeat first
    [ simple apply ev_deriv_cos
    | simple apply ev_deriv_sin
    | simple apply ev_deriv_horner
    | simple apply ev_derivD
    | simple apply ev_derivB
    | simple apply ev_derivN 
    | simple apply ev_derivM 
    | simple apply ev_deriv_cst 
   ]].


Definition r_deriv := (@deriv0, @derivMn, @derivZ, @derivMz, @deriv_mulC, @derivXn, @derivX, @derivC, @derivXsubC, @derivMXaddC, @derivMNn, @derivM, @derivD, @derivB, @derivN, @deriv_exp).

Definition r_derive1 := (derive1_cos, derive1_sin, derivE_rev, derivMXaddC, derivC,
         @horner0_ext R).

Import Rewriting. 

Ltac rewrite_derive1_bottom_up := 
 match goal with
  |  |- context [derive1 (mul_fun ?f ?g)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         lazymatch g with context [derive1] => fail | _ => idtac end;
         rewrite (derive1M_ f g); [ | derivable ..]
  |  |- context [derive1 (add_fun ?f ?g)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         lazymatch g with context [derive1] => fail | _ => idtac end;
         rewrite (derive1_add f g); [ | derivable ..]
  |  |- context [derive1 (opp_fun ?f)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         rewrite (derive1_opp f); [ | derivable ..]
 end.

Ltac rewrite_derive := 
  time "rewrite_derive"
  repeat (
  simpl;
  first [rewrite !(r_derive1, r_ring, r_lift, opp_funK)
         | rewrite_derive1_bottom_up
         ]).

Lemma true_andb_e1: forall [A B],
 is_true (andb A B) -> is_true A.
Proof.
intros. red in H. rewrite Bool.andb_true_iff in H. apply H.
Qed.

Lemma true_andb_e2: forall [A B],
 is_true (andb A B) -> is_true B.
Proof.
intros. red in H. rewrite Bool.andb_true_iff in H. apply H.
Qed.

Lemma conj': forall A B C, (A /\ B -> C) -> (A -> B -> C).
Proof. tauto. Qed.

Ltac massage_constraints := 
repeat match goal with 
|  H: is_true (?A ?B) |- _ => 
   move :(true_andb_e2 H);  first [move /RltbP | move /RlebP];
   move :(true_andb_e1 H);  first [move /RltbP | move /RlebP];
   apply conj'; clear H; move => H
end.

Lemma trigo_cos_e: (@cos.body RbaseSymbolsImpl_R__canonical__reals_Real) = Rtrigo_def.cos.
(* See: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/relating.20trigo.2Ecos.20to.20Rtrigo_def.2Ecos.2C.20etc.2E/with/612420101 *)
Admitted.

Lemma trigo_sin_e: (@sin.body RbaseSymbolsImpl_R__canonical__reals_Real) = Rtrigo_def.sin.
(* See: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/relating.20trigo.2Ecos.20to.20Rtrigo_def.2Ecos.2C.20etc.2E/with/612420101 *)
Admitted.

Ltac prepare_for_interval := 
rewrite ?trigo_cos_e ?trigo_sin_e; 
try change nmodule.Algebra.zero with (Rdefinitions.IZR 0) in *;
repeat change (ssralg.GRing.mul ?A ?B) with (Rdefinitions.Rmult A B) in *;
repeat change (nmodule.Algebra.opp ?A) with (Rdefinitions.Ropp A) in *;
repeat change (nmodule.Algebra.add ?A ?B) with (Rdefinitions.Rplus A  B) in *;
repeat change (GRing.one _) with (Raxioms.INR 1%nat) in *;
repeat change (GRing.inv ?A) with (Rdefinitions.Rinv A)%R in * ;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?RIneq.Rminus_diag in *;
lazymatch goal with
 |  |- is_true (@Order.lt _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RltbP
 |  |- is_true (@Order.le _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RlebP
 |  |- _ => idtac
end;
massage_constraints.

Definition r_intgal_C := (@intgal_linearN, @r_intgal, @intgal_C, @hornerC').

Ltac gauss_legendre_error_bounder_part2 := 
(* Now focus on the integral *)
let e := fresh "e" in 
match goal with |- _ ?E => set e := E end; cbv beta;
(* Step seven: calculate the integral *)
rewrite ?mul_polyC_polyC -?mulrA;
repeat match goal with |- context [ 'X * polyC ?a ] => rewrite ?(pull_left (polyC a)) end;
repeat match goal with |- context [ 'X * (polyC ?a * 'X)] => rewrite ?(pull_left (polyC a)) end;
rewrite ?hornerD' ?hornerN' ?(hornerM' (polyC _)) ?intgal_linear2 ?r_intgal_C; auto with continuous;
subst e;
(* Now convert from MathComp to plain-old-Rocq *)
prepare_for_interval;
(* Solve the goal using the Interval package *)
interval.


Ltac gauss_legendre_error_bounder := 
(* Step one: expand any [let ... in ... ] *)
cbv zeta;
(* Step two: apply the [legendre_quadrature_error] theorem *)
let H := fresh in let H0 := fresh in let ξ := fresh "ξ" in 
match goal with |- context [Gauss_Legendre_quadrature ?n ?f] => 
destruct (legendre_quadrature_error' n f) as [ξ [H H0]];
rewrite {}H0
end;
(* Step three: some specific computations and simplifications *)
match goal with |- context [factorial ?k] => let j := eval compute in k in change k with j end;
let j := fresh "j" in 
set j := factorial _; compute in j; subst j;
let n := fresh "n" in 
match goal with |- context [legendre ?N] => set n := N; compute in n; rewrite /n end;
(* Step four: compute the polynomial product (legendre _ * legendre _) *)
change (fun x : _ => exprz (horner (legendre ?n) x) 2) with 
  (fun x :R => mul (horner (legendre n) x)  (horner (legendre n) x) );
evar (j : R -> R);
replace (fun x => mul (horner _ _)  _) with  j;
 [ subst j | extensionality x;
     rewrite -hornerM (LR_poly_eq _ (nth_iseq some_legendre_roots (@Ordinal 5 n isT))) /= ?mulrD /j;
     reflexivity];
(* Step five: focus on the k'th derivative of the function *)
match goal with |-  is_true (Order.le (Rbasic_fun.Rabs (mul (?D / _) _ ))  _) => pattern D end;
let G := fresh "G" in 
match goal with |- ?g _ => set G := g end;
(* Step six: now derive the k'th derivative *)
rewrite_derive; (* This takes many seconds *)
rewrite ?r_deriv ?r_ring ?hornerE /= ?r_ring;
cbv delta [G]; clear G;
lazymatch goal with
 | |- context [@derive1] => idtac "Warning: Did not eliminate all derivatives"
 | _ => gauss_legendre_error_bounder_part2 end.

Import BinInt.
Notation IZR := (Rdefinitions.IZR).

(* Our test case is the product of a Lagrange shape function (1/2)*(1-x) with some 
  spatial transformation, in this case cosine. *)

Lemma error_1_0_1:
 (* test function (1/2)*(1-x)*cos(x), degree-1 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 Rbasic_fun.Rabs ( ∫ f - Gauss_Legendre_quadrature 1 f ) <= IZR 2 / IZR 100.
Proof.
time "error_1_0_1" gauss_legendre_error_bounder.  (* 3.444 seconds *)
Qed.

Lemma error_1_0_2:
 (* test function (1/2)*(1-x)*cos(x), degree-2 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 Rbasic_fun.Rabs ( ∫ f - Gauss_Legendre_quadrature 2 f ) <=  IZR 223 / IZR 100000.
Proof.
time "error_1_0_2" gauss_legendre_error_bounder.  (* 31.7 seconds *)
Qed.


