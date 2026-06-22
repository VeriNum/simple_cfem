(** * CFEM.polyroots:   Roots of a floating-point polynomial *)


From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

From vcfloat Require Import  FPStdLib FPStdCompCert.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Rdefinitions List ListNotations.

Definition Fle [t: type] (x y: ftype t) : bool := BCMP Gt false x y.
Definition Flt [t: type] (x y: ftype t) : bool := BCMP Gt true y x.

Lemma Fle_refl [t: type] (x: ftype t): is_true (Binary.is_finite _ _ x) -> is_true (Fle x x).
Admitted.

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

Definition legendre0 (x: R) : R := 1.
Definition legendre1 (x: R) : R := x.
Definition legendre2 (x: R) : R := x*x - 1/3.
Definition legendre3 (x: R) : R := x*x*x - (3/5)*x.
Definition legendre4 (x: R) : R := x*x*x*x - (30/35)*(x*x) + (3/35).

Require Import Interval.Tactic.
Require  CFEM.quadrature. Import CFEM.quadrature.Legendre.
From mathcomp Require Import Rstruct.
Definition legendre := @legendre RbaseSymbolsImpl_R__canonical__reals_Real.

Definition legendre_1_0: root_near (legendre 1) Tdouble.
exists (0%F64, 0%nat).
unfold legendre; rewrite Legendre_poly_1.
abstract (compute; lra).
Defined.

Definition legendre_2_0: root_near (legendre 2) Tdouble.
exists ((-0.577350269189626)%F64, 3%nat).
unfold legendre; rewrite Legendre_poly_2.
compute; lra.
Defined.

Definition legendre_2_1: root_near (legendre 2) Tdouble.
exists ((0.577350269189626)%F64, 3%nat).
unfold legendre; rewrite Legendre_poly_2.
compute; lra.
Defined.

Definition legendre_3_0: root_near (legendre 3) Tdouble.
exists ((-0.774596669241483)%F64, 5%nat).
unfold legendre; rewrite Legendre_poly_3.
compute; lra.
Defined.

Definition legendre_3_1: root_near (legendre 3) Tdouble.
exists (0%F64, 0%nat).
unfold legendre; rewrite Legendre_poly_3.
abstract (compute; lra).
Defined.

Definition legendre_3_2: root_near (legendre 3) Tdouble.
exists ((0.774596669241483)%F64, 5%nat).
unfold legendre; rewrite Legendre_poly_3.
abstract (compute; lra).
Defined.

Definition legendre_4_0: root_near (legendre 4) Tdouble.
exists ((-0.861136311594053)%F64, 5%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_1: root_near (legendre 4) Tdouble.
exists ((-0.339981043584856)%F64, 8%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_2: root_near (legendre 4) Tdouble.
exists ((0.339981043584856)%F64, 8%nat).
unfold legendre; rewrite Legendre_poly_4.
abstract (compute; lra).
Defined.

Definition legendre_4_3: root_near (legendre 4) Tdouble.
exists ((0.861136311594053)%F64, 5%nat).
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


