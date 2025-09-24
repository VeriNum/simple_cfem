(* Copied from iterative_methods/cholesky/cholesky_model.v, 
   modified a bit, should really unify these libraries somehow *)
Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.


From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


(*Require Import VSTlib.spec_math.*)
(*Import FPCore FPCompCert. *)
(*Require Import Cholesky.cholesky.*)
(*From libValidSDP Require cholesky_infnan.*)


(* BEGIN adapted from iterative_methods/sparse/sparse_model.v *)
Inductive sum_any {t}: forall (v: list (ftype t)) (s: ftype t), Prop :=
| Sum_Any_0: sum_any nil (Zconst t 0)
| Sum_Any_1: forall x y, feq x y -> sum_any [x] y
| Sum_Any_split: forall al bl a b c, sum_any al a -> sum_any bl b -> feq (BPLUS a b) c -> sum_any (al++bl) c
| Sum_Any_perm: forall al bl s, Permutation al bl -> sum_any al s -> sum_any bl s.

(*
Lemma sum_any_accuracy{t}: forall (v: list (ftype t)) (s: ftype t), 
  let mag := fold_left Rmax (map FT2R v) R0 in
  sum_any v s ->
  (Rabs (fold_left Rplus (map FT2R v) R0 - FT2R s) <= common.g t (length v) * (INR (length v) * mag))%R.
(* see Theorem fSUM in LAProof/accuracy_proofs/sum_acc.v *)
Admitted.
*)
(* END copied form iterative_methods/sparse/sparse_model.v *)

(* duplicates floatlib.zerof, so at least keep it local *)
Local Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

(*
Definition Zrangelist (lo hi: Z) : list Z := 
  (*   lo <= i < hi *)
  map (fun i => lo+Z.of_nat i) (seq.iota 0 (Z.to_nat (hi-lo))).

Lemma iota_plus1:
  forall lo n, seq.iota lo (n + 1)%nat = seq.iota lo n ++ [(lo+n)%nat].
Proof.
intros.
revert lo; induction n; simpl; intros; auto.
f_equal; lia.
f_equal.
rewrite IHn.
f_equal.
f_equal.
lia.
Qed.

Definition updij {T} (R: Z -> Z -> T) i j x :=
  fun i' j' => if zeq i i' then if zeq j j' then x else R i' j' else R i' j'.

Lemma iota_range: forall k lo n, In k (seq.iota lo n) -> (lo <= k < lo+n)%nat.
Proof.
intros.
revert k lo H; induction n; intros; try lia.
contradiction H.
replace (S n) with (n+1)%nat in H by lia.
rewrite iota_plus1 in H.
rewrite in_app in H. destruct H.
apply IHn in H; lia.
destruct H; try contradiction. lia.
Qed.

Lemma Zrangelist_range: forall i lo hi, In i (Zrangelist lo hi) -> lo <= i < hi.
Proof.
 unfold Zrangelist.
 intros.
 destruct (list_in_map_inv _ _ _ H) as [x [? ?]]; clear H; subst.
 apply iota_range in H1. lia.
Qed.

Lemma Zrangelist_plus1:
  forall lo hi, lo <= hi -> Zrangelist lo (hi + 1) = Zrangelist lo hi ++ [hi].
Proof.
intros.
unfold Zrangelist.
replace [hi] with (map (fun i => lo + Z.of_nat i) [Z.to_nat (hi-lo)])
 by (simpl; f_equal; lia).
rewrite <- map_app. f_equal.
replace (Z.to_nat (hi+1-lo)) with (Z.to_nat (hi-lo)+1)%nat by lia.
apply iota_plus1.
Qed.

Lemma Zrangelist_minus1:
  forall lo hi, lo < hi -> Zrangelist lo hi = [lo] ++ Zrangelist (lo+1) hi.
Proof.
intros.
unfold Zrangelist.
destruct (Z.to_nat (hi-lo)) eqn:?H.
lia.
simpl.
f_equal.
lia.
replace (Z.to_nat (hi-(lo+1))) with n by lia.
forget O as k.
clear H0 hi H.
revert k; induction n; simpl; intros; f_equal; try lia.
apply IHn.
Qed.

Lemma Forall_Zrangelist :
   forall (P : Z -> Prop) (lo hi : Z),
     (forall i, (lo <= i < hi)%Z -> P i) -> Forall P (Zrangelist lo hi).
Proof.
intros.
unfold Zrangelist.
apply Forall_map.
apply Forall_seq.
intros.
apply H.
lia.
Qed.

Lemma Zrangelist_split: 
 forall lo mid hi,  
  lo <= mid <= hi -> Zrangelist lo hi = Zrangelist lo mid ++ Zrangelist mid hi.
Proof.
intros.
unfold Zrangelist.
replace (Z.to_nat (hi-lo)) with (Z.to_nat (mid-lo) + Z.to_nat (hi-mid))%nat by lia.
rewrite seq_app, map_app.
f_equal.
change seq.iota with seq.
simpl.
set (k := Z.to_nat (mid-lo)).
destruct H.
set (n := Z.to_nat (hi-mid)). clearbody n; clear hi H0.
replace mid with (lo+Z.of_nat k) by lia.
clearbody k; clear mid H.
revert k; induction n; simpl; intros; auto.
f_equal. lia.
rewrite IHn.
rewrite <- seq_shift.
rewrite map_map.
f_equal.
extensionality z.
lia.
Qed.

Lemma Zlength_Zrangelist:
  forall lo hi, lo <= hi -> Zlength (Zrangelist lo hi) = (hi-lo).
Proof.
intros.
rewrite Zlength_correct.
unfold Zrangelist.
rewrite length_map, length_seq. lia.
Qed.

Lemma Zrangelist_one: forall i j, i+1=j -> 
  Zrangelist i j = [i].
Proof.
intros.
unfold Zrangelist. replace (j-i) with 1 by lia.
simpl. f_equal. lia.
Qed.
*)

Open Scope ring_scope.


Definition matrix_upd {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x: T) : 'M[T]_(m,n) :=
    \matrix_(i',j') if  andb (Nat.eq_dec i' i) (Nat.eq_dec j' j) then x else M i' j'.

(*
Definition updij [T] [n] (R: 'M[T]_n) (i j: 'I_n) (x: T) : 'M[T]_n :=
 \matrix_(i', j') if Nat.eq_dec i i' then if Nat.eq_dec j j' then x else R i' j' else R i' j'.
*)


Section WithSTD.
Context {t : type}.

Definition neg_zero : ftype t := Binary.B754_zero (fprec t) (femax t) true.

Definition subtract_loop' [n] (A R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t -> Prop :=
  sum_any (A i j :: map (fun k' => BOPP (BMULT (R k' i) (R k' j))) 
        (map (widen_ord (ltnW (ltn_ord _))) (ord_enum k))).

Definition cholesky_jik_ij' [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     ((i < j)%N -> exists x, subtract_loop' A R i j i x /\ R i j = BDIV x (R i i))
   /\ (i=j -> exists x, subtract_loop' A R i j i x /\ R i j = BSQRT x).


Definition subtract_loop [n] (A R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
  fold_left BMINUS
    (map (fun k' => BMULT (R k' i) (R k' j))
         (map (widen_ord (ltnW (ltn_ord _))) (ord_enum k)))
    (A i j).


Definition cholesky_jik_ij [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     (forall Hij: (i<j)%N, R i j = BDIV (subtract_loop A R i j i) (R i i))  
   /\ (forall Hij: i=j, R i j = BSQRT (subtract_loop A R i j i)).

Definition cholesky_jik_spec [n: nat] (A R: 'M[ftype t]_n) : Prop :=
  forall i j, cholesky_jik_ij A R i j.

Definition cholesky_jik_upto [n] (imax: 'I_n) (jmax : 'I_n.+1) (A R : 'M[ftype t]_n) : Prop :=
  forall (i j: 'I_n),
      ((j<jmax)%N -> cholesky_jik_ij A R i j)
   /\ (nat_of_ord j = nat_of_ord jmax -> (i<imax)%N -> cholesky_jik_ij A R i j)
   /\ ((j>jmax)%N -> R i j = A i j)
   /\ (nat_of_ord j= nat_of_ord jmax -> (i>=imax)%N -> R i j = A i j).

(* BEGIN copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma update_i_lt_j_aux: forall [n] [i j: 'I_n], (i<j)%N -> (i.+1<n)%N.
Proof.
 intros.
 pose proof (ltn_ord j).
 lia.
Qed.


Lemma eq_in_subrange: 
  forall n T (i: 'I_n) (f f': 'I_n -> T),
    (forall (a: 'I_n), (a<i)%N -> f a = f' a) ->
     map (comp f (widen_ord (ltnW (ltn_ord i)))) (ord_enum (nat_of_ord i))
   = map (comp f'(widen_ord (ltnW (ltn_ord i)))) (ord_enum (nat_of_ord i)).
Proof.
intros.
apply eq_in_map.
intros ? ?; auto.
simpl.
apply H.
simpl.
apply ltn_ord.
Qed.


Definition lshift1 [n: nat] (k: ordinal n) : ordinal (S n) 
 := Ordinal (ltn_trans (ltn_ord k) (leqnn (S n))).


Lemma update_i_lt_j:
  forall n (i j: 'I_n) (A R: 'M[ftype t]_n)
   (Hij: (i < j)%N)
   (i1: 'I_n)
   (Hi1: nat_of_ord i1 = S i),
   cholesky_jik_upto i (lshift1 j) A R ->
   let rij := BDIV (subtract_loop A R i j i) (R i i) in
    @cholesky_jik_upto n i1 (lshift1 j) A (matrix_upd R i j rij).
Proof.
intros * Hij i1 Hi1 H1 rij i' j'.
subst rij.
simpl.
split; [ | split3]; intros * H2.
-
specialize (H1 i' j').
destruct H1 as [H1 _]. specialize (H1 H2).
split; intros * H4.
+
destruct H1 as [H1 _]. specialize (H1 H4). 
unfold matrix_upd.
rewrite !mxE.
destruct (Nat.eq_dec j j'); [lia |].
destruct (Nat.eq_dec _ _); simpl.
* destruct (Nat.eq_dec _ _); [ lia | simpl].
  apply ord_inj in e; subst i.
  rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE; simpl. 
  destruct (Nat.eq_dec _ _); auto; lia.
  destruct (Nat.eq_dec _ _); auto; lia.
* rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  repeat destruct (Nat.eq_dec _ _); try lia; auto.
+ destruct H1 as [_ H1].
  unfold matrix_upd. subst i'.
  rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia.
  *
  destruct (Nat.eq_dec _ _); try lia.
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
  *
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE. simpl in H2.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
- red in H1|-*.
  apply ord_inj in H2.
  subst j'.
  simpl in *.
  intro H3.
  split; intros; [ | subst; lia].
  unfold matrix_upd. 
  rewrite !mxE.
  destruct (Nat.eq_dec j j); [simpl; clear e | lia].
  destruct (Nat.eq_dec j i'); try lia. simpl.
   replace (if proj_sumbool (Nat.eq_dec i i') then R i' i' else R i' i') 
      with (R i' i') by (destruct (Nat.eq_dec _ _); auto).
   destruct (Nat.eq_dec _ _); simpl.
  * assert (i' = i) by (apply ord_inj; auto). subst i'. clear e.
    clear n0 H3.
    f_equal.
  match goal with |- _ = _ _ ?ff _ _ _ => set (f:=ff) end.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  subst f. rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia; auto.
  destruct (Nat.eq_dec _ _); try lia; auto.
  * assert (i'<i)%N by lia.  clear n1 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ [H1 _]].
   destruct H1 as [H1 _]; auto; try lia.
   rewrite H1; auto.
   f_equal.
  unfold subtract_loop.
  f_equal.
  rewrite <- !map_comp.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal;
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- unfold matrix_upd. rewrite !mxE.
  specialize (H1 i' j').
  destruct H1 as [_ [_ [H1 _]]].
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- intros.
  specialize (H1 i' j'). destruct H1 as [_ [_ [_ H1]]].
  assert (j'=j) by (apply ord_inj; auto).
  subst. clear H2.
  unfold matrix_upd. rewrite !mxE.  
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
  simpl. apply H1; auto. lia.
Qed.

Lemma ord_enum_snoc:
  forall n, ord_enum (addn n 1) = 
   map (lshift 1) (ord_enum n) ++ [Ordinal (eq_leq (addnC 1 n))].
Proof.
intros.
set (a := ord_enum _).
set (b := cat _ _).
assert (map (@nat_of_ord _) a = map (@nat_of_ord _) b).
2: clearbody a; clearbody b;
   revert b H; induction a; destruct b; simpl; intros; inv H; auto;
   try f_equal; auto;
    apply ord_inj; auto.
subst a b; rewrite val_ord_enum.
rewrite iotaD.
rewrite map_cat.
f_equal.
rewrite <- val_ord_enum.
simpl.
induction (ord_enum n); simpl; auto.
f_equal. auto.
Qed.

Lemma ord_enum_snoc':
  forall n, ord_enum (S n) = 
   map (@lshift1 n) (ord_enum n) ++ [@Ordinal (S n) n (leqnn _)].
Proof.
intros.
set (a := ord_enum _).
set (b := cat _ _).
assert (map (@nat_of_ord _) a = map (@nat_of_ord _) b).
2: clearbody a; clearbody b;
   revert b H; induction a; destruct b; simpl; intros; inv H; auto;
   try f_equal; auto;
    apply ord_inj; auto.
subst a b; rewrite val_ord_enum.
change (S n) with (addn 1 n).
rewrite {1} addnC. 
rewrite iotaD.
rewrite map_cat.
f_equal.
rewrite <- val_ord_enum.
simpl.
rewrite <- map_comp.
unfold comp.
apply eq_in_map.
intros ? ?.
simpl in *.
hnf. simpl.
induction (ord_enum n); simpl; auto.
Qed.

Lemma subtract_another':
  forall n (i j k: 'I_n) (A R: 'M[ftype t]_n)
    (Hij: (i <= j)%N) 
    (Hkj: (k < j)%N),
    subtract_loop A R i j (Ordinal (update_i_lt_j_aux Hkj))%N = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
unfold subtract_loop at 1.
simpl.
rewrite <- map_comp.
rewrite ord_enum_snoc'.
rewrite map_comp.
rewrite !map_cat.
simpl map.
rewrite fold_left_app; simpl; f_equal.
unfold subtract_loop.
f_equal. f_equal.
rewrite <- map_comp.
apply eq_in_map.
hnf; intros; simpl in *.
apply ord_inj; auto.
f_equal; f_equal; apply ord_inj; auto.
Qed.

Lemma subtract_another:
  forall n (i j k: 'I_n) (A R: 'M[ftype t]_n)
    (Hij: (i <= j)%N) 
    (Hkj: (k < j)%N)
    (k1: 'I_n)
    (Hk1: nat_of_ord k1 = S k),
    subtract_loop A R i j k1 = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
assert (Datatypes.is_true (leq (S (S (nat_of_ord k))) n)).
  pose proof ltn_ord k1; lia.
assert (k1 = @Ordinal n (S k) H). apply ord_inj; auto.
subst k1.
unfold subtract_loop at 1.
rewrite ord_enum_snoc'.
rewrite !map_cat.
simpl map.
rewrite fold_left_app; simpl; f_equal.
unfold subtract_loop.
f_equal. f_equal.
rewrite <- map_comp.
apply eq_in_map.
hnf; intros; simpl in *.
apply ord_inj; auto.
f_equal; f_equal; apply ord_inj; auto.
Qed.

(* END copied from iterative_methods/cholesky/verif_cholesky.v *)
End WithSTD.

Lemma cholesky_jik_upto_zero:
  forall t n (A: 'M[ftype t]_n) (zero: 'I_n), nat_of_ord zero=O -> cholesky_jik_upto zero (lshift1 zero) A A.
Proof.
intros i j; split; [ | split3]; simpl; try lia; auto.
Qed.

Lemma cholesky_jik_upto_newrow:
 forall t n (j: 'I_n) (A R: 'M[ftype t]_n),
  cholesky_jik_upto j (lshift1 j) A R ->
  cholesky_jik_upto (@Ordinal n 0 (leq_ltn_trans (leq0n j) (ltn_ord j)))
     (@Ordinal n.+1 (j.+1)%N (ltn_ord j)) A (matrix_upd R j j (BSQRT (subtract_loop A R j j j))).
Proof.
pose proof I.
intros.
intros i' j'.
destruct (H0 i' j') as [? [? [? ?]]]; clear H0.
split; [ | split3]; intros; try split; hnf; intros; try lia.
-
 clear H4. simpl in H0.
 destruct (Nat.eq_dec j' j).
 + apply ord_inj in e. subst j'. clear H1 H3. specialize (H2 (Logic.eq_refl _) Hij).
   unfold matrix_upd at 1. rewrite mxE.
   destruct (Nat.eq_dec _ _); [lia  |]. simpl.
   destruct H2.
   rewrite H1; [ |apply Hij]. f_equal.
   * unfold subtract_loop. f_equal.
     rewrite <- !map_comp.
     apply eq_in_subrange.
     intros. unfold matrix_upd. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
   * unfold matrix_upd. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
 + simpl in *. destruct (H1 ltac:(lia)); clear H1 H5. specialize (H4 ltac:(lia)). clear H2 H3.
   unfold matrix_upd at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia. simpl.
   rewrite H4. f_equal.
   * unfold subtract_loop. f_equal.
     rewrite <- !map_comp.
     apply eq_in_subrange.
     intros. unfold matrix_upd. rewrite !mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
   * unfold matrix_upd. rewrite mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
- subst j'. simpl in *.
  destruct (Nat.eq_dec i' j).
 + apply ord_inj in e. subst. unfold matrix_upd. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. simpl.
   f_equal.
   unfold subtract_loop. f_equal.
   rewrite <- !map_comp.
   apply eq_in_subrange.
   intros. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
 + unfold matrix_upd at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
   simpl.
   destruct (H1 ltac:(lia)). rewrite H6; auto.
   f_equal.
   unfold subtract_loop. f_equal.
   rewrite <- !map_comp.
   apply eq_in_subrange.
   intros. unfold matrix_upd. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- simpl in *; lia. 
- simpl in *. lia.
- unfold matrix_upd. rewrite !mxE. simpl in *.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- unfold matrix_upd. rewrite !mxE. simpl in *. clear H5.
  repeat destruct (Nat.eq_dec _ _); try lia; apply H3; lia.
Qed.

Locate matrix_upd.
Definition upd_cV [T][n] (v: 'cV[T]_n) (i: 'I_n) (x: T) : 'cV[T]_n :=
   matrix_upd v i ord0 x.
(*  \col_i' if (i'==i)%N then x else v i' 0. *)

Definition forward_subst_step {t: type} [n: nat] 
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) 
     : 'cV_n  :=
   upd_cV x i
    (BDIV (fold_left BMINUS
           (map (fun j => BMULT (L i j) (x j 0)) (take i (ord_enum n)))
           (x i 0))
          (L i i)).


Definition forward_subst [t: type] [n]
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV_n :=
  fold_left (forward_subst_step L) (ord_enum n) x.

Definition backward_subst_step {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) : 'cV_n :=
    upd_cV x i
      (BDIV (fold_left BMINUS 
              (map (fun j => BMULT (U i j) (x j 0)) (drop (i+1) (ord_enum n)))
              (x i 0))
         (U i i)).

Definition backward_subst {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV[ftype t]_n :=
     fold_left (backward_subst_step U) (rev (ord_enum n)) x.

(* joinLU n L U    produces a matrix whose upper-triangle (including diagonal) matches U,
         and whose lower_triangle (excluding diagonal) matches L *)
Definition joinLU {T} [n] (L U : 'M[T]_n) : 'M[T]_n :=
 \matrix_(i,j) if (i<=j)%N then U i j else L i j.

Definition mirror_UT {T} [n] (U: 'M[T]_n) : 'M[T]_n :=
  joinLU U^T U.
(*
Inductive block_cholesky {t: type}: forall (n: Z) (A R: Z -> Z -> ftype t), Prop :=
| Block_cholesky_1: forall A R, A 0 0 = BSQRT(R 0 0) -> block_cholesky 1 A R
| Block_cholesky_plus: forall n1 n2 A R,
   block_cholesky n1 A R ->
   blocksolve A n b c B
*)
