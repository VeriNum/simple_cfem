From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
From mathcomp.zify Require Import ssrZ zify.
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

Lemma split_shift1 [m j]: lt j m -> is_true (ssrnat.leq (S j) m).
Proof. lia. Qed.

Lemma split_shift2 [m n] [j: 'I_(m+n)] : not (lt (nat_of_ord j) m) -> is_true (ssrnat.leq (S (nat_of_ord j - m)) n).
Proof. intros. pose proof (ltn_ord j). lia. Qed.

Definition split_shift [m n] (j: 'I_(m+n)) :=
   match Compare_dec.lt_dec j m
   with left H => @lshift m n (@Ordinal _ (nat_of_ord j) (split_shift1 H))
         | right H => @rshift m n (@Ordinal _ (nat_of_ord j - m) (split_shift2 H))
   end.

Lemma split_shift_eq: forall [m n] (j: 'I_(m+n)), j = split_shift j.
Proof.
intros.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); apply ord_inj; simpl; auto.
lia.
Qed.

Lemma row_mxE: forall [T: Type][m n1 n2: nat] (A1: 'M[T]_(m,n1)) (A2: 'M[T]_(m,n2)) (i: 'I_m) (j: 'I_(n1+n2)),
    row_mx A1 A2 i j = 
    match Compare_dec.lt_dec (nat_of_ord j) n1
    with left H => A1 i  (@Ordinal n1 (nat_of_ord j) (split_shift1 H))
         | right H => A2 i (@Ordinal n2 (nat_of_ord j - n1) (split_shift2 H))
     end.
Proof.
intros.
pose proof (split_shift_eq j).
rewrite {1}H.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
apply row_mxEl.
apply row_mxEr.
Qed.

Lemma col_mxE: forall [T: Type][m1 m2 n: nat] (A1: 'M[T]_(m1,n)) (A2: 'M[T]_(m2,n)) (i: 'I_(m1+m2)) (j: 'I_n),
    col_mx A1 A2 i j = 
    match Compare_dec.lt_dec (nat_of_ord i) m1
    with left H => A1 (@Ordinal m1 (nat_of_ord i) (split_shift1 H)) j
         | right H => A2 (@Ordinal m2 (nat_of_ord i - m1) (split_shift2 H)) j
     end.
Proof.
intros.
pose proof (split_shift_eq i).
rewrite {1}H.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
apply col_mxEu.
apply col_mxEd.
Qed.

Lemma row_0_1: forall [T: Type] [n: nat] (A: 'M[T]_(1,n)) i, row i A = A.
Proof.
intros.
rewrite ord1. clear i.
apply matrixP. intros i j.
unfold row.
rewrite mxE.
f_equal.
symmetry; apply ord1.
Qed.

Lemma col_0_1: forall [T: Type] [n: nat] (A: 'M[T]_(n,1)) j, col j A = A.
Proof.
intros.
rewrite ord1.  clear j.
apply matrixP. intros i j.
unfold col.
rewrite mxE.
f_equal.
symmetry; apply ord1.
Qed.

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

Lemma row_col_E: forall [T: Type] [m1 m2 n] (A: 'M[T]_(m1,n)) (B: 'M[T]_(m2,n)) (i: 'I_(m1+m2)),
      row i (col_mx A B) =
    match Compare_dec.lt_dec (nat_of_ord i) m1
    with left H => row (@Ordinal m1 (nat_of_ord i) (split_shift1 H)) A
         | right H => row (@Ordinal m2 (nat_of_ord i - m1) (split_shift2 H)) B
     end.
Proof.
intros.
pose proof (split_shift_eq i).
rewrite {1}H.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
rewrite <- row_usubmx, col_mxKu. auto.
rewrite <- row_dsubmx, col_mxKd. auto.
Qed.

Lemma col_row_E: forall [T: Type] [m n1 n2] (A: 'M[T]_(m,n1)) (B: 'M[T]_(m,n2)) (j: 'I_(n1+n2)),
      col j (row_mx A B) =
    match Compare_dec.lt_dec (nat_of_ord j) n1
    with left H => col (@Ordinal n1 (nat_of_ord j) (split_shift1 H)) A
         | right H => col (@Ordinal n2 (nat_of_ord j - n1) (split_shift2 H)) B
     end.
Proof.
intros.
pose proof (split_shift_eq j).
rewrite {1}H.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
rewrite <- col_lsubmx, row_mxKl. auto.
rewrite <- col_rsubmx, row_mxKr. auto.
Qed.

(* TODO: see if we can unify these two similar tactics, row_col_matrix_tac and rewrite_matrix *)

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

Ltac is_ground_nat n := lazymatch n with O => idtac | S ?n' => is_ground_nat n' end.

Ltac is_const_ordinal i := let j := eval hnf in i in match j with @Ordinal _ ?k _ => 
       let k' := eval hnf in k in is_ground_nat k' end.

Ltac rewrite_matrix := 
repeat
match goal with
  | |- context [fun_of_matrix (@row_mx ?T ?m ?n1 ?n2 _ _) ?i ?j ] => is_const_ordinal j;
             rewrite (@row_mxE T m n1 n2);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) n1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia);
                let ss := fresh "ss" in set (ss := @split_shift1 n1 _ _); rewrite (proof_irr ss isT); clear ss H
              | try (exfalso; clear - H; lia);
                let ss := fresh "ss" in set (ss := @split_shift2 n1 n2 _ _); rewrite (proof_irr ss isT); clear ss H ]
  | |- context [fun_of_matrix (@col_mx ?T ?m1 ?m2 ?n _ _) ?i ?j ] =>  is_const_ordinal i;
             rewrite (@col_mxE T m1 m2 n);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) m1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia);
                let ss := fresh "ss" in set (ss := @split_shift1 m1 _ _); rewrite (proof_irr ss isT); clear ss H
              | try (exfalso; clear - H; lia); 
                let ss := fresh "ss" in set (ss := @split_shift2 m1 m2 _ _); rewrite (proof_irr ss isT); clear ss H] 
   | |- context [@col ?T' ?m' ?n' ?j (@row_mx ?T ?m ?n1 ?n2 ?A ?B)] =>
             change m' with m; change n' with (n1+n2)%nat; change T' with T;
             rewrite (@col_row_E T m n1 n2 A B j);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) n1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia);
                let ss := fresh "ss" in set (ss := @split_shift1 n1 _ _); rewrite (proof_irr ss isT); clear ss H
              | try (exfalso; clear - H; lia); 
                let ss := fresh "ss" in set (ss := @split_shift2 n1 n2 _ _); rewrite (proof_irr ss isT); clear ss H] 
   | |- context [@row ?T' ?m' ?n' ?j (@col_mx ?T ?m1 ?m2 ?n ?A ?B)] => 
             change m' with (m1+m2)%nat; change n' with n; change T' with T;
             rewrite (@row_col_E T m1 m2 n A B j);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) m1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia);
                let ss := fresh "ss" in set (ss := @split_shift1 m1 _ _); rewrite (proof_irr ss isT); clear ss H
              | try (exfalso; clear - H; lia); 
                let ss := fresh "ss" in set (ss := @split_shift2 m1 m2 _ _); rewrite (proof_irr ss isT); clear ss H] 
   | |- context [trmx (@col_mx ?R ?m1 ?m2 ?n ?A ?B)] => rewrite (@tr_col_mx R m1 m2 n A B)
   | |- context [trmx (@row_mx ?R ?m ?n1 ?n2 ?A ?B)] => rewrite (@tr_row_mx R m n1 n2 A B)
 | |- context [@row _ _ _ ?i (@row_mx ?R ?m ?n1 ?n2 ?A1 ?A2)] => rewrite (@row_row_mx R m n1 n2 i A1 A2)
 | |- context [@col _ _ _ ?j (@col_mx ?R ?m1 ?m2 ?n ?A1 ?A2)] => rewrite (@col_col_mx R m1 m2 n j A1 A2)
   | |- _ => progress rewrite ?trmx_const ?const_mxE ?row_0_1 ?col_0_1
                 ?row_col_E ?col_row_E
  | i: 'I_1 |- _ =>  let H := fresh in assert (H := ord1 i); simpl in H; subst i
  | H: 'I__ |- _ => progress simpl in H
  | H: ~(nat_of_ord _ < _)%nat |- _ => simpl in H
  | _ => lia
       end.

Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof.
intros.
pose proof val_ord_enum n.
simpl in H.
transitivity (size (iota 0 n)).
transitivity (size (map (nat_of_ord (n:=n)) (ord_enum n))).
rewrite size_map; auto.
f_equal; auto.
apply size_iota.
Qed.

Lemma nth_ord_enum': forall n (d i: 'I_n), nth d (ord_enum n) i = i.
Proof.
intros.
pose proof (val_ord_enum n).
simpl in H.
apply ord_inj.
pose proof ltn_ord i.
rewrite <- nth_map with (x2:=nat_of_ord d).
rewrite H. rewrite nth_iota. lia. lia.
rewrite size_ord_enum.
auto.
Qed.

Lemma nth_List_nth: forall {A: Type} (d: A) (l: seq.seq A) (n: nat),
  seq.nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma ord_enum_cases: forall [n] (P: 'I_n -> Prop),
  List.Forall P (ord_enum n) ->
  forall i, P i.
Proof.
intros.
rewrite List.Forall_forall in H.
apply H.
clear.
pose proof @nth_ord_enum' n i i.
rewrite nth_List_nth in H.
rewrite <- H.
apply List.nth_In.
change @length with @size.
rewrite size_ord_enum.
pose proof (ltn_ord i); lia.
Qed. 

Ltac compute_ord_enum n := 
  tryif is_ground_nat n then idtac 
      else  fail "compute_ord_enum: Need a ground term natural number, but got" n; 
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
  repeat apply List.Forall_cons; try apply List.Forall_nil
 end.

Ltac simplify_ordinal i := 
   (* If i reduces to a constant ordinal, replace it with the canonical   @Ordinal n i (eq_refl true)  *)
      lazymatch i with @Ordinal _ _ (eq_refl _) => fail | _ => idtac end;
      let j := eval hnf in i in
      let n := constr:(nat_of_ord j) in let n1 := eval hnf in n in 
         is_ground_nat n1; 
         match type of j with ?t => let t' := eval hnf in t in match t' with ordinal ?k => 
             replace i with (@Ordinal k n1 (eq_refl true)) by (apply ord_inj; reflexivity)
        end end.

