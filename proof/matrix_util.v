From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
From HB Require Import structures.
Import GRing.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Definition from_'I0_any (T: Type) (i: 'I_0) : T.
destruct i. discriminate.
Qed.

Fixpoint colmx_of_list {T: Type } (al: seq T) : 'cV[T]_(size al) :=
  match al as l return 'cV_(size l) with
  | [::] => \matrix_(i,j)  (from_'I0_any T i)
  | x :: al => col_mx (@const_mx T 1 1 x) (colmx_of_list al)
  end.

Fixpoint rowmx_of_list {T: Type } (al: seq T) : 'rV[T]_(size al) :=
  match al as l return 'rV_(size l) with
  | [::] => \matrix_(i,j)  (from_'I0_any T j)
  | x :: al => row_mx(@const_mx T 1 1 x) (rowmx_of_list al)
  end.

Fixpoint rowmx_of_listn {t: baseAddUMagmaType } [n] (al: seq t) : 'rV[t]_n.
destruct n as [ | n].
apply (const_mx zero).
destruct al as [ | a al].
apply (const_mx zero).
change (n.+1) with (1+n).
apply (row_mx (const_mx a) (@rowmx_of_listn t n al)).
Defined.

Fixpoint mx_of_listn {t: baseAddUMagmaType} [m n: nat] (rl: seq (seq t)) : 'M[t]_(m, n).
destruct m as [ | m].
apply (const_mx zero).
destruct rl as [ | r rl].
apply (const_mx zero).
change (S m) with (addn 1 m).
apply col_mx.
apply (rowmx_of_listn r).
apply mx_of_listn; auto.
Defined.

Ltac compute_size a :=  let x := constr:(size a) in 
   let y := eval compute in x in exact y.

Definition mx_of_list_def  {t: baseAddUMagmaType} (rl: seq (seq t))
 :=  @mx_of_listn t ltac:(compute_size rl) ltac:(compute_size (head nil rl)) rl.

Notation mx_of_list rl := ltac:(let m := constr:(size rl) in let m := eval compute in m
                                     in let n := constr:(size (head nil rl)) in let n := eval compute in n
                                     in let a := constr:(@mx_of_listn _ m n rl)
                                     in let b := eval cbv beta match fix delta [mx_of_listn rowmx_of_listn] in a
                                     in exact b)  (only parsing).

Module Test1.

Definition A := mx_of_list [:: [:: 1; 2; 3];  [:: 4; 5; 6]].
Check A. (* 'M[nat]_(1+1,3) *)
End Test1.


From vcfloat Require Import FPCompCert.
Module Test2.
Import ZArith.

HB.instance Definition _ := hasAdd.Build _ (@BPLUS _ Tdouble _).
HB.instance Definition _ := hasZero.Build _ (Zconst Tdouble 0).


Definition B :=  mx_of_list [:: [:: Zconst Tdouble 1; Zconst Tdouble 2; Zconst Tdouble 3];
                                               [:: Zconst Tdouble 4; Zconst Tdouble 5; Zconst Tdouble 6]].
End Test2.


From mathcomp Require Import  all_reals.

Module Test3.
Open Scope R.
Section S.
Context {R : realType}.
Definition A := mx_of_list [:: [:: 1:R; 2; 3];
                                               [:: 4; 5; 6]].
Check A.
(* A : 'M[R]_(1+1, 3)   *)


Definition U := mx_of_list [:: [:: 1:R ; 2; 3];
                                               [:: 4; 5]].
Check U.
(* U : 'M_(2, 3)   *)

Definition V := mx_of_list [:: [:: 1:R ; 2];
                                               [:: 4; 5; 6]].
Check V.
(* V : 'M_2)   *)

End S.
End Test3.

From Stdlib Require Import ZArith.
Require Import Flocq.IEEE754.BinarySingleNaN.

Module Test4.
Definition float := binary_float 53 1024.
Definition add : float -> float -> float := @Bplus 53 1024 erefl erefl mode_NE.
Definition ofZ n : float := binary_normalize 53 1024 erefl erefl mode_NE n 0 false.

HB.instance Definition _ := hasAdd.Build _ add.
HB.instance Definition _ := hasZero.Build _ (ofZ 0).

Definition B := mx_of_list [:: [:: ofZ 1; ofZ 2; ofZ 3];
                                               [:: ofZ 4; ofZ 5; ofZ 6]].
Check B.
(* B : 'M_(2, 3)   *)

End Test4.


Lemma col_row: forall {t} [m n] (i: 'I_m) (j: 'I_n) A, 
  @col t 1 n j (@row t m n i A) = @row t m 1 i (@col t m n j A).
Proof.
intros.
apply /matrixP.
intros x y.
rewrite !mxE //.
Qed.

Lemma const_mxE: forall {R}{m n: nat} (x: R) i j, @const_mx R m n x i j = x.
Proof. intros; apply mxE. Qed.

Lemma row01: forall {t} [n] (i: 'I_1) (A: 'M[t]_(1,n)), @row t 1 n i A = A.
Proof.
intros.
apply matrixP.
intros i' j; rewrite !mxE. rewrite !ord1. auto.
Qed.


From Stdlib Require Import Lia.


Ltac row_col_matrix_tac :=
repeat
match goal with
 | |- context [@row ?t _ _ (@lshift ?a ?b _) (col_mx _ _)] => rewrite (@rowKu t a b)
 | |- context [@row ?t _ _ (@rshift ?a ?b _) (col_mx _ _)] => rewrite (@rowKd t a b)
 | |- context [col ?j (row ?i (row_mx _ _))] => rewrite (col_row i j)
 | |- context [@col ?t ?a _ (@lshift ?b _ _) (row_mx _ _)] => rewrite (@colKl t  a b) 
 | |- context [@col ?t ?a _ (@rshift ?b _ _) (row_mx _ _)] => rewrite (@colKr t  a b) 
 | |- context [@row ?t _ _ ?c (@col_mx _ ?n1 ?n2 _ _ _)] => 
      lazymatch c with @lshift n1 n2 _ => fail | _ => idtac end;
     replace c with (@lshift n1 n2 (@Ordinal n1 (nat_of_ord c) erefl))
    by (apply ord_inj; reflexivity)
 | |- context [@row ?t _ _ ?c (@col_mx _ ?n1 ?n2 _ _ _)] => 
      lazymatch c with @rshift n1 n2 _ => fail | _ => idtac end;
  replace c with (@rshift n1 n2 (@Ordinal n1 (nat_of_ord c - n1) erefl))
    by (apply ord_inj; reflexivity)
 | |- context [@col ?t _ ?n ?c (@row_mx _ _ ?n1 ?n2 _ _)] => 
      lazymatch c with @lshift n1 n2 _ => fail | _ => idtac end;
     replace c with (@lshift n1 n2 (@Ordinal n1 (nat_of_ord c) erefl))
    by (apply ord_inj; reflexivity)
 | |- context [@col ?t _ ?n ?c (@row_mx _ _ ?n1 ?n2 _ _)] => 
      lazymatch c with @rshift n1 n2 _ => fail | _ => idtac end;
  replace c with (@rshift n1 n2 (@Ordinal n1 (nat_of_ord c - n1) erefl))
    by (apply ord_inj; reflexivity)
 | |- _ => rewrite col_const
 | |- _ => rewrite row_const
 | |- _ => rewrite const_mxE
 | |- _ => rewrite row01
| |- context [fun_of_matrix (@row_mx _ _ ?n1 ?n2 _ _) ?i (@lshift _ _ _)] => rewrite (@row_mxEl _ _ n1 n2)
| |- context [fun_of_matrix (@row_mx _ _ ?n1 ?n2 _ _) ?i (@rshift _ _ _)] => rewrite (@row_mxEr _ _ n1 n2)
| |- context [fun_of_matrix (@row_mx _ _ ?n1 ?n2 _ _) ?i ?j] =>
      lazymatch j with @lshift n1 n2 _ => fail | _ => idtac end;    
    replace j with (@lshift n1 n2 (@Ordinal n1 (nat_of_ord j) erefl))
       by (apply ord_inj; reflexivity; try lia);
    rewrite (@row_mxEl _ _ n1 n2)
| |- context [fun_of_matrix (@row_mx _ _ ?n1 ?n2 _ _) ?i ?j] =>
      lazymatch j with @rshift n1 n2 _ => fail | _ => idtac end;    
    replace j with (@rshift n1 n2 (@Ordinal n2 (nat_of_ord j - n1) erefl))
       by (apply ord_inj; try reflexivity; lia);
    rewrite (@row_mxEr _ _ n1 n2)
| |- context [fun_of_matrix (@col_mx _ ?n1 ?n2 _ _ _) (@lshift _ _ _) ?j] => rewrite (@col_mxEu _ _ n1 n2)
| |- context [fun_of_matrix (@col_mx _ ?n1 ?n2 _ _ _) (@rshift _ _ _) ?j] => rewrite (@col_mxEd _ _ n1 n2)
| |- context [fun_of_matrix (@col_mx _ ?n1 ?n2 _ _ _) ?i ?j] =>
      lazymatch j with @lshift n1 n2 _ => fail | _ => idtac end;    
    replace j with (@lshift n1 n2 (@Ordinal n1 (nat_of_ord j) erefl))
       by (apply ord_inj; try reflexivity; lia);
    rewrite (@col_mxEu _ _ n1 n2)
| |- context [fun_of_matrix (@col_mx _ ?n1 ?n2 _ _ _) ?i ?j] =>
      lazymatch j with @rshift n1 n2 _ => fail | _ => idtac end;    
    replace j with (@rshift n1 n2 (@Ordinal n2 (nat_of_ord j - n1) erefl))
       by (apply ord_inj; try reflexivity; lia);
    rewrite (@col_mxEd _ _ n1 n2)
end.
