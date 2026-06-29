(** * CFEM.polyroots:   Roots of a floating-point polynomial *)


From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

From vcfloat Require Import  FPStdLib FPStdCompCert.


Require Import Interval.Tactic.
Require  CFEM.quadrature. Import CFEM.quadrature.Legendre.
From mathcomp Require Import Rstruct.
Import fintype ssrbool.


Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Rdefinitions List ListNotations.



Definition legendre := @legendre RbaseSymbolsImpl_R__canonical__reals_Real.

(** ** Method A:  Without knowing the real value of the root, and assuming the function is continuous,
  exhibit values x and kδ such that  f(x-|x|kδ) <= 0 <= f(x+|x|kδ) \/ f(x+|x|kδ) <= 0 <= f(x-|x|kδ),
  where x is a floating point number, k is a small natural number, and δ is the standard relative 
  error bound on primitive floating point numbers (i.e., half an ulp).
*)

Module MethodA.


Definition root_bound_pred (f: R->R) (lohi: R * R) := 
    let (lo, hi) := lohi in
       (lo <= hi /\
        (f lo <= 0 <= f hi \/
        f hi <= 0 <= f lo))%R.

Definition root_bound (f: R -> R) :=
  { lohi: (R * R) | root_bound_pred f lohi }.

Definition root_near_pred (f: R -> R) (t: type) (xk: ftype t * nat) :=
      let '(x,k) := xk in 
      let lo := (FT2R x - FT2R (BABS x) * INR k * FPCore.default_rel (coretype_of_type t))%R in 
      let hi := (FT2R x + FT2R (BABS x) *  INR k * FPCore.default_rel (coretype_of_type t))%R in 
      root_bound_pred f (lo,hi).

Definition root_near (f: R -> R)  (t: type) :=
      { xk: ftype t * nat | root_near_pred f t xk}.

Definition root_near_bound [f: R -> R] [t: type] (rn: root_near f t) : root_bound f :=
  let '(exist _ (x,k) H) := rn in exist (root_bound_pred f) _ H.

Definition legendre_1_0: root_near (legendre 1) Tdouble.
exists (0%F64, 0%nat).
unfold legendre; rewrite Legendre_poly_1.
compute; lra.
Defined.

Definition legendre_2_0: root_near (legendre 2) Tdouble.
exists ((-0.5773502691896257)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_2.
compute; lra.
Defined.

Definition legendre_2_1: root_near (legendre 2) Tdouble.
exists ((0.5773502691896257)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_2.
compute; lra.
Defined.


Definition legendre_3_0: root_near (legendre 3) Tdouble.
exists ((-0.7745966692414834)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_3.
compute; lra.
Defined.

Definition legendre_3_1: root_near (legendre 3) Tdouble.
exists (0%F64, 0%nat).
unfold legendre; rewrite Legendre_poly_3.
abstract (compute; lra).
Defined.

Definition legendre_3_2: root_near (legendre 3) Tdouble.
exists ((0.7745966692414834)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_3.
abstract (compute; lra).
Defined.

Definition legendre_4_0: root_near (legendre 4) Tdouble.
exists ((-0.8611363115940526)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_1: root_near (legendre 4) Tdouble.
exists ((-0.3399810435848563)%F64, 2%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_2: root_near (legendre 4) Tdouble.
exists ((0.3399810435848563)%F64, 2%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_3: root_near (legendre 4) Tdouble.
exists ((0.8611363115940526)%F64, 1%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.


Definition roots_sorted [f: R -> R] [t: type] (al: list (root_near f t)) :=
  path.sorted (fun x y : root_near f t => 
                        Rlt_bool (snd (proj1_sig (root_near_bound x))) (fst (proj1_sig (root_near_bound y)))) al.

Definition roots_bounds_increasing (f: R -> R)  (al: list (root_bound f)) :=
  path.sorted (fun x y : root_bound f => Rlt_bool (snd (proj1_sig x)) (fst (proj1_sig y))) al.

Definition legendre_0_roots:  list (root_near (legendre 0) Tdouble) := [ ].
Lemma legendre_0_roots_increasing: roots_sorted legendre_0_roots = true.
Proof. reflexivity. Qed.

Definition legendre_1_roots := [ legendre_1_0].
Lemma legendre_1_roots_increasing: roots_sorted legendre_1_roots = true.
Proof.
simpl; rewrite ?Bool.andb_true_iff;  repeat split; apply Rlt_bool_true; compute; lra.
Qed.
 
Definition legendre_2_roots := [ legendre_2_0; legendre_2_1].
Lemma legendre_2_roots_increasing: roots_sorted legendre_2_roots = true.
Proof.
simpl; rewrite ?Bool.andb_true_iff;  repeat split; apply Rlt_bool_true; compute; lra.
Qed.
 

Definition legendre_3_roots := [ legendre_3_0; legendre_3_1; legendre_3_2].
Lemma legendre_3_roots_increasing: roots_sorted legendre_3_roots = true.
Proof.
simpl; rewrite ?Bool.andb_true_iff;  repeat split; apply Rlt_bool_true; compute; lra.
Qed.
 
Definition legendre_4_roots := [ legendre_4_0; legendre_4_1; legendre_4_2; legendre_4_3].
Lemma legendre_4_roots_increasing: roots_sorted legendre_4_roots = true.
Proof.
simpl; rewrite ?Bool.andb_true_iff;  repeat split; apply Rlt_bool_true; compute; lra.
Qed.

Record poly_and_roots (t: type) :=  { 
    PR_poly: R -> R; 
    PR_roots: list (root_near PR_poly t); 
   PR_increasing: roots_sorted PR_roots = true
}.
Arguments PR_poly [t].
Arguments PR_roots [t].
Arguments PR_increasing [t].
Arguments Build_poly_and_roots [t].

Definition legendre_roots: list (poly_and_roots Tdouble) :=
  [ Build_poly_and_roots  _ _ legendre_0_roots_increasing;
    Build_poly_and_roots _ _ legendre_1_roots_increasing;
    Build_poly_and_roots _ _ legendre_2_roots_increasing;
    Build_poly_and_roots _ _ legendre_3_roots_increasing;
    Build_poly_and_roots _ _ legendre_4_roots_increasing].


End MethodA.

(** ** Method B: Using a closed-form (or at least, computable) real-valued expression for the root [r],
         exhibit values x and kδ such that f r = 0 /\  |r-x| <= |x|kδ.
*)

Module MethodB.


Definition root_near_pred (f: R -> R) (t: type) (xk: ftype t * nat) :=
      let '(x,k) := xk in 
     exists r:R, (f r = 0 /\ Rabs (FT2R x - r) <= Rabs (FT2R x) * INR k * FPCore.default_rel (coretype_of_type t))%R.

Definition root_near (f: R -> R)  (t: type) :=    { xk: ftype t * nat | root_near_pred f t xk}.

Lemma seq_all_nth: forall {T: Type} (a: pred T) (al: list T),
  seq.all a al -> 
  forall (d: T) (i: nat), 
   (i < seq.size al)%nat -> a (seq.nth d al i).
Proof.
intros.
revert i H0; induction al; intros. simpl in H0; lia.
destruct i; simpl in *; red in H; rewrite Bool.andb_true_iff in H; destruct H; auto.
apply IHal.
auto.
lia.
Qed.


Ltac prove_root_near LRN i prec := 
abstract (
let LR := fresh "LR" in 
pose (LR := LRN RbaseSymbolsImpl_R__canonical__reals_Real);
match type of LR with legendre_roots ?n => 
   exists (tuple.tnth (quadrature.ROOTS_vals _ _ _ _(LR_roots _ LR)) (@Ordinal n i isT))
end;
unfold legendre, quadrature.Legendre.legendre;
split;
[ let H := fresh in assert (H :=  (seq_all_nth _ _ (quadrature.ROOTS_zero _ _ _ _ (LR_roots _ LR)) 0%R i ltac:(simpl; lia)));
  unfold poly.root in H;
 match goal with H: is_true (@eqtype.eq_op ?C ?a ?b) |- _ =>  destruct (@eqtype.eqP  C a b) end; 
  auto; discriminate
|];
cbv [tuple.tnth seq.nth nat_of_ord]; simpl tuple.tval; cbv match;
with_strategy opaque [INR] simpl;
clear LR;
set (z := FPCore.default_rel _); hnf in z; simpl in z; subst z;
try change nmodule.Algebra.zero with 0%R;
repeat change (ssralg.GRing.mul ?A ?B) with (A*B)%R;
repeat change (nmodule.Algebra.opp ?A) with (- A)%R;
repeat change (nmodule.Algebra.add ?A ?B) with (A + B)%R;
try change (ssralg.GRing.one _) with 1%R;
repeat change (ssralg.GRing.inv ?A) with (/A)%R;
rewrite <- ?RsqrtE,  <- ?INRE;
unfold Defs.F2R, Fnum, Fexp;
interval with (i_prec(prec))).

Definition legendre_1_0: root_near (legendre 1) Tdouble.
exists (0%F64, 0%nat).
prove_root_near @legendre_roots_1 0%nat 110%positive.
Defined.

Definition legendre_2_0: root_near (legendre 2) Tdouble.
exists ((-0.5773502691896257)%F64, 1%nat).
prove_root_near @legendre_roots_2 0%nat 110%positive.
Defined.

Definition legendre_2_0': root_near (legendre 2) Tdouble.
exists ((-0.5773502691896257)%F64, 2%nat).
prove_root_near @legendre_roots_2 0%nat 53%positive.
Defined.

Definition legendre_2_1: root_near (legendre 2) Tdouble.
exists ((0.5773502691896257)%F64, 1%nat).
prove_root_near @legendre_roots_2 1%nat 110%positive.
Defined.

Definition legendre_3_0: root_near (legendre 3) Tdouble.
exists ((-0.7745966692414834)%F64, 1%nat).
time prove_root_near @legendre_roots_3 0%nat 110%positive.
Defined.

Definition legendre_3_0': root_near (legendre 3) Tdouble.
exists ((-0.7745966692414834)%F64, 2%nat).
time prove_root_near @legendre_roots_3 0%nat 53%positive.
Defined.

Definition legendre_3_1: root_near (legendre 3) Tdouble.
exists (0%F64, 0%nat).
time prove_root_near @legendre_roots_3 1%nat 110%positive.
Defined.

Definition legendre_3_2: root_near (legendre 3) Tdouble.
exists ((0.7745966692414834)%F64, 1%nat).
time prove_root_near @legendre_roots_3 2%nat 110%positive.
Defined.

Definition legendre_4_0: root_near (legendre 4) Tdouble.
exists ((-0.8611363115940526)%F64, 1%nat).
time prove_root_near @legendre_roots_4 0%nat 110%positive.
Defined.

Definition legendre_4_0': root_near (legendre 4) Tdouble.
exists ((-0.8611363115940526)%F64, 3%nat).
time prove_root_near @legendre_roots_4 0%nat 53%positive.
Defined.

Definition legendre_4_1: root_near (legendre 4) Tdouble.
exists ((-0.33998104358485626)%F64, 1%nat).
time prove_root_near @legendre_roots_4 1%nat 110%positive.
Defined.

Definition legendre_4_1': root_near (legendre 4) Tdouble.
exists ((-0.33998104358485626)%F64, 3%nat).
time prove_root_near @legendre_roots_4 1%nat 53%positive.
Defined.

Definition legendre_4_2: root_near (legendre 4) Tdouble.
exists ((0.33998104358485626)%F64, 1%nat).
time prove_root_near @legendre_roots_4 2%nat 110%positive.
Defined.

Definition legendre_4_3: root_near (legendre 4) Tdouble.
exists ((0.8611363115940526)%F64, 1%nat).
time prove_root_near @legendre_roots_4 3%nat 110%positive.
Defined.

Record poly_and_roots (t: type) :=  { 
    PR_n : nat ;
    PR_roots: list (root_near (legendre PR_n) t); 
    PR_weights: @gauss_weights RbaseSymbolsImpl_R__canonical__reals_Real PR_n
}.
Arguments PR_n [t].
Arguments PR_roots [t].
Arguments PR_weights [t].
Arguments Build_poly_and_roots [t].

Definition legendre_roots: list (poly_and_roots Tdouble) :=
  [ Build_poly_and_roots  0 nil gauss_weights_0;
    Build_poly_and_roots 1 [legendre_1_0]  gauss_weights_1;
    Build_poly_and_roots 2 [legendre_2_0; legendre_2_1]  gauss_weights_2;
    Build_poly_and_roots 3 [legendre_3_0; legendre_3_1; legendre_3_2]  gauss_weights_3;
    Build_poly_and_roots 4 [legendre_4_0; legendre_4_1; legendre_4_2; legendre_4_3]  gauss_weights_4].

End MethodB.

Lemma root_near_pred_BA: forall f t xk,
  MethodB.root_near_pred f t xk -> MethodA.root_near_pred f t xk.
Proof.
(* Not true, unless this is a simple root.  *)
Abort.

Lemma root_near_pred_AB: forall f t xk,
  MethodA.root_near_pred f t xk -> MethodB.root_near_pred f t xk.
Proof.
(* Should be provable if we add a premise that f is continuous *)
Abort.

(** ** Accuracy summary *)
(**  For proving that a floating-point number is close to a root of a Legendre polynomial, we have
  two methods.  In either method, we define δ as one half of the unit-in-last-place (ULP) of 1.0.
  In either method, we present (x,k), where x is the floating point error that's near a root r, and the claim is that |r-x| ≤ kδ|x|.  
 - "Method A" uses [root_near_pred], which says, f(x-kδ|x|)<=0<=f(x+kδ|x|) \/ f(x+kδ|x|)<=0<=f(x-kδ|x|),
    evaluated in the reals (not in floating point).
 - "Method B" uses [root_near_pred'], which exhibits r as a closed-form real formula, and says,
         f r = 0 /\  |r-x| <= kδ|x|.
 Using these methods we are able to prove these bounds (i.e., values of k).
  In each row, [n] is the degree of the Legendre polynomial,  [i] is the index of the root (i.e., in increasing order between -1 and +1),
   [x] is the floating point approximation to the root, k is the believed accuracy of [x],
  kA is the accuracy proved by Method A, kB is the accuracy proved by method B, and kB' is the 
  accuracy proved by method B with internal calculations limited to 53-bit precision.
  These accuracy proofs are limited by what our proof tools (such as the Rocq Interval package) can do.
  <<
   n   i   x                      k   kA   kB   kB'
   1   0    0.000000000000000     0   0    0    0
   2   0   -0.577350269189626     1   3    3    6
   3   0   -0.774596669241483     1   5    5    7
   3   1    0.000000000000000     0   0    0    0
   4   0   -0.861136311594053     1   5    5    6
   4   1   -0.339981043584856     1   8    8    9
  >>
*)

