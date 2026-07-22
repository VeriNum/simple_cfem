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
From Stdlib Require Import Reals.

Definition shape (n: 'I_3) (i: 'I_n.+1) : R -> R.
destruct n as[n Hn].
destruct n as [ | [| ]]; try discriminate.
- (* 0th-order *)
   exact (fun x => 1).
- (* 1st-order Lagrange shape functions *)
destruct i as [ [ | [ | ]]  ]; simpl in *; try Lia.lia.
+ (* n=1, i=0 *) exact (fun x => (1/2)*(1-x)).
+ (* n=1, i=1 *) exact (fun x => (1/2)*(1+x)).
- (* 2nd-order Lagrange shape functions *)
destruct i as [ [ | [ | [|] ]]  ]; simpl in *; try Lia.lia. 
+ (* n=2, i=0 *) exact (fun x => -(1/2)*(1-x)*x).
+ (* n=2, i=1 *) exact (fun x => (1-x)*(1+x)).
+ (* n=2, i=1 *) exact (fun x => (1/2)*x*(1+x)).
Defined.

Definition testfun (n: 'I_3) (i: 'I_n.+1) : R -> R := fun x => shape n i x * cos x.

 Notation "∫" := intgal.

Lemma derive1M {R : numFieldType} (f g: R -> R) (x: R) :
  derive.derivable f x 1 ->
  derive.derivable g x 1 ->
  (fun x => f x * g x)^`()%classic x = f x * g^`()%classic x + f^`()%classic x * g x.
Admitted.

Definition everywhere_derivable {R : numFieldType}  (f: R -> R) := forall x, derive.derivable f x 1.

Lemma derive1M_ {R : numFieldType} (f g: R -> R) :
  everywhere_derivable f ->
  everywhere_derivable g ->
  (mul_fun f g)^`()%classic = add_fun (mul_fun f (g^`()%classic)) (mul_fun (f^`()%classic) g).
Proof.
intros.
extensionality x.
apply derive1M; auto.
Qed.

Notation d1 := (@derive1 R (Real_sort__canonical__normed_module_NormedModule RbaseSymbolsImpl_R__canonical__reals_Real)).

Lemma derive1_cst': forall {R : numFieldType} [V : normedModType R] (k : V) (t : R), 
   (fun=> k)^`()%classic t = 0.
Proof. intros; apply derive1_cst. Qed.


Lemma derive1_cos: d1 cos = opp_fun sin.
Admitted.

Lemma derive1_sin: d1 sin = cos.
Admitted.

Lemma derive1_add: forall f g : R -> R, d1 (f \+ g) = d1 f \+ d1 g.
Admitted.

Lemma derive1_opp: forall f : R -> R, d1 (\- f) = \- (d1 f).
Admitted.

Lemma opp_funK: forall f: R -> R, opp_fun (opp_fun f) = f.
Admitted.

Lemma ev_deriv_cos: everywhere_derivable cos.
Admitted.
Lemma ev_deriv_sin:  everywhere_derivable sin.
Admitted.

Lemma range_Rabs: forall x, is_true (-1 <= x <= 1) -> Rle (Rabs x) 1.
Admitted.

Lemma derivE_rev :
forall [R : realFieldType] (p : {poly Num_RealField__to__GRing_NzSemiRing R}),
 (horner p)^`()%classic = horner p^`().
Proof. intros. symmetry. apply derivE. Qed.

Lemma ev_deriv_horner: forall p: {poly R}, everywhere_derivable (horner p).
Proof.
intros. intro. apply derivable_horner.
Qed.

Lemma ev_derivD: forall {R : numFieldType}   (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \+ g).
Proof.
intros. intro. apply derivableD; auto.
Qed.

Lemma ev_derivB: forall {R : numFieldType}   (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \- g).
Proof.
intros. intro. apply derivableB; auto.
Qed.

Lemma ev_derivN: forall {R : numFieldType}   (f : R -> R),
    everywhere_derivable f -> everywhere_derivable (\- f).
Proof.
intros. intro. apply derivableN; auto.
Qed.

Lemma ev_derivM: forall {R : numFieldType}   (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \* g).
Proof.
intros. intro. apply derivableM; auto.
Qed.

Lemma ev_deriv_cst: forall {R : numFieldType}   (c: R),
    everywhere_derivable (functions.cst c).
Proof.
intros. intro. apply derivable_cst.
Qed.

Create HintDb derivable.

Hint Resolve @ev_deriv_cos @ev_deriv_sin @ev_deriv_horner @ev_derivD @ev_derivB @ev_derivN @ev_derivM @ev_deriv_cst : derivable.

Definition r_deriv := (@deriv0, @derivMn, @derivZ, @derivMz, @deriv_mulC, @derivXn, @derivX, @derivC, @derivXsubC, @derivMXaddC, @derivMNn, @derivM, @derivD, @derivB, @derivN, @deriv_exp).

Definition r_derive1 := (derive1_cos, derive1_sin, derivE_rev, derivMXaddC, derivC, derive1_add, derive1_opp, 
    @derive1_cst' R (Real_sort__canonical__normed_module_NormedModule RbaseSymbolsImpl_R__canonical__reals_Real), 
   @derive1_cst R (Real_sort__canonical__normed_module_NormedModule RbaseSymbolsImpl_R__canonical__reals_Real),
         horner0_ext).

Import Rewriting. 

Ltac rewrite_derive := 
 repeat time "rewrite_derive iteration" (
  rewrite /= ?(r_derive1, r_ring, r_lift, opp_funK);
  try (rewrite derive1M_; [ | solve [auto with derivable ] .. ])).

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

Ltac prepare_for_interval := 
try change nmodule.Algebra.zero with 0%R in *;
repeat change (ssralg.GRing.mul ?A ?B) with (A*B)%R in *;
repeat change (nmodule.Algebra.opp ?A) with (- A)%R in *;
repeat change (nmodule.Algebra.add ?A ?B) with (A + B)%R in *;
try change (ssralg.GRing.one _) with 1%R in *;
repeat change (ssralg.GRing.inv ?A) with (/A)%R in * ;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?Rminus_diag in *;
lazymatch goal with
 |  |- is_true (@Order.lt _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RltbP
 |  |- is_true (@Order.le _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RlebP
 |  |- _ => idtac
end;
massage_constraints.

Definition r_intgal_C := (@intgal_linearN, @r_intgal, @intgal_C, @hornerC').

Ltac gauss_legendre_error_bounder := 
(* Step one: expand any [let ... in ... ] *)
cbv zeta;
(* Step two: apply the [legendre_quadrature_error] theorem *)
let H := fresh in let H0 := fresh in let ξ := fresh "ξ" in 
match goal with |- context [Gauss_Legendre_quadrature ?n ?f] => 
destruct (legendre_quadrature_error' n f) as [ξ [H H0]];
 change (add ?A (opp ?B) = ?C) with (Rminus A B = C) in H0; rewrite {}H0
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
match goal with |-  is_true (Order.le (Rabs (mul (?D / _) _ ))  _) => pattern D end;
let G := fresh "G" in 
match goal with |- ?g _ => set G := g end;
(* Step six: now derive the k'th derivative *)
rewrite_derive; (* This takes many seconds *)
rewrite ?r_deriv ?r_ring ?hornerE /= ?r_ring;
lazymatch goal with |- context [@derive1] => idtac "Warning: Did not eliminate all derivatives" | _ => idtac end;
(* Now focus on the integral *)
let e := fresh "e" in 
match goal with |- G ?E => set e := E end; subst G; cbv beta;
(* Step seven: calculate the integral *)
rewrite ?mul_polyC_polyC -?mulrA;
repeat match goal with |- context [ 'X * polyC ?a ] => rewrite ?(pull_left (polyC a)) end;
repeat match goal with |- context [ 'X * (polyC ?a * 'X)] => rewrite ?(pull_left (polyC a)) end;
rewrite ?hornerD' ?hornerN' ?(hornerM' (polyC _)) ?intgal_linear2 ?r_intgal_C;
subst e;
(* Now convert from MathComp to plain-old-Rocq *)
prepare_for_interval;
(* Solve the goal using the Interval package *)
interval.

Lemma error_1_0_1:
 (* test function (1/2)*(1-x)*cos(x), degree-1 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 Rabs ( ∫ f - Gauss_Legendre_quadrature 1 f ) <= (2 / 100)%R.
Proof.
time "error_1_0_1" gauss_legendre_error_bounder.
(* that took 49.847 or 52.862 seconds overall *)
Qed.

Lemma error_1_0_2:
 (* test function (1/2)*(1-x)*cos(x), degree-2 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 Rabs ( ∫ f - Gauss_Legendre_quadrature 2 f ) <= (223 / 100000)%R.
Proof.
time "error_1_0_2" gauss_legendre_error_bounder.
(* 150.098 or 152.842 seconds overall *)
Qed.


