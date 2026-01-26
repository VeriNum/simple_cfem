From LAProof.accuracy_proofs Require Import preamble common float_acc_lems mv_mathcomp solve_model.


Section WithNaN.

Variable NAN: FPCore.Nans.
Variable t: type.

Definition ord_enum2 m n : seq ('I_m * 'I_n) :=
  flatten (map (fun i => map (fun j => (i,j)) (ord_enum n)) (ord_enum m)). 

Definition point_mx [T] (zero: T) [m n] (i: 'I_m) (j: 'I_n) (x: T) : 'M[T]_(m,n):=
   \matrix_(i',j') if (i'==i) && (j'==j) then x else zero.

Definition matrix_add_to [n] (A: 'M[ftype t]_n) [ne] (ids: 'I_n ^ ne) (B: 'M[ftype t]_ne) : 
                       'M[ftype t]_n :=
 foldl (@F.addmx _ _ n n) A (map (fun '(i,j) => point_mx (Zconst t 0) (ids i) (ids j) (B i j)) (ord_enum2 ne ne)).

End WithNaN.


Module Shape.
Require Import mathcomp.analysis.derive.
From mathcomp Require Import interval.

Definition scale_fn [T1 T2] (c: R) (f: T1 -> T2 -> R) (i: T1) (j: T2): R := (c * f i j)%Re.
Axiom continuously_differentiable: forall [n], (('I_n->R) -> R) -> Prop.


Record shape : Type := {
  dim : nat;
  nen: nat;
  N: ('I_dim -> R) -> ('I_nen -> R);
  X: 'I_nen -> 'I_dim -> R;
  Ωref := { x : 'I_dim -> R | 
                          exists α: 'I_nen -> {x | x \in  `[ 0 , 1 ]%Re}, \sum_i projT1 (α i) = 1
                           /\ forall j, \sum_i projT1 (α i) * X i j = x j};
   lagrangian: forall i j, N (X i) j = if i==j then 1 else 0;
   diff: forall j: 'I_nen, continuously_differentiable (fun i => N i j)
}.