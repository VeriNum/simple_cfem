(* Copied from iterative_methods/cholesky/cholesky_model.v, 
   modified a bit, should really unify these libraries somehow *)
Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
(*Require Import VSTlib.spec_math.*)
(*Import FPCore FPCompCert. *)
(*Require Import Cholesky.cholesky.*)
(*From libValidSDP Require cholesky_infnan.*)

Set Bullet Behavior "Strict Subproofs".

(* duplicates floatlib.zerof, so at least keep it local *)
Local Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

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

Section WithSTD.
Context {t : type}.

Definition neg_zero : ftype t := Binary.B754_zero (fprec t) (femax t) true.

Definition subtract_loop (A R: Z -> Z -> ftype t) (i j k: Z) :=
  fold_left BMINUS
    (map (fun k' => BMULT (R k' i) (R k' j)) (Zrangelist 0 k))
    (A i j).

Definition cholesky_jik_ij (n: Z) (A R: Z -> Z -> ftype t) (i j: Z) : Prop :=
   (0 <= j < n) ->
     (0 <= i < j -> R i j = BDIV (subtract_loop A R i j i) (R i i))
   /\ (i=j -> R i j = BSQRT (subtract_loop A R i j i)).


Definition cholesky_jik_spec (n: Z) (A R: Z -> Z -> ftype t) : Prop :=
  forall i j, cholesky_jik_ij n A R i j.

Definition cholesky_jik_upto (n imax jmax : Z) (A R : Z -> Z -> ftype t) : Prop :=
  forall i j, 
    (j<jmax -> cholesky_jik_ij n A R i j)
   /\ (j=jmax -> i<imax -> cholesky_jik_ij n A R i j)
   /\ (j>jmax -> R i j = A i j)
   /\ (j=jmax -> i>=imax -> R i j = A i j).

(* BEGIN copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma update_i_lt_j:
  forall n i j (A R: Z -> Z -> ftype t),
   0 <= i < j -> j < n ->
   cholesky_jik_upto n i j A R ->
   let rij := BDIV (subtract_loop A R i j i) (R i i) in
    cholesky_jik_upto n (i + 1) j A (updij R i j rij).
Proof.
intros.
intros i' j'.
subst rij.
split; [ | split3]; intros.
-
specialize (H1 i' j').
destruct H1 as [H1 _]. specialize (H1 H2).
split; intros.
+
specialize (H1 H3). clear H3.
destruct H1 as [? _]. specialize (H1 H4). 
unfold updij.
destruct (zeq j j'); try lia.
if_tac; try lia.
* rewrite if_false by lia.
  subst i. rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H3.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
* rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  if_tac; auto. if_tac; try lia. auto.
+ specialize (H1 H3).
  destruct H1 as [_ H1].
  unfold updij. subst i'.
  if_tac; try lia.
  * rewrite if_false by lia.
  specialize (H1 (eq_refl _)).
  rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  *
  rewrite H1 by lia. f_equal.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  if_tac; try lia; auto. if_tac; auto; try lia.
- red in H1|-*.
  subst j'.
  intro.
  split; intros; [ | lia].
 + unfold updij. destruct (zeq j j); try lia. clear e.
   destruct (zeq j i'); try lia.
   replace (if zeq i i' then R i' i' else R i' i') with (R i' i') by (if_tac; auto).
   if_tac.
  * subst i'. clear n0 H3 H0 H4.
    f_equal.
  match goal with |- _ = _ _ ?ff _ _ _ => set (f:=ff) end.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H0.
  subst f. simpl. if_tac; try lia; auto.
  * assert (i'<i) by lia. clear H5 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ [H1 _]].
   destruct H1 as [H1 _]; try lia. rewrite H1 by auto.
   f_equal.
  unfold subtract_loop.
  f_equal.
  apply map_ext_in.
  intros. apply Zrangelist_range in H3.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
- unfold updij.
  specialize (H1 i' j').
  destruct H1 as [_ [_ [H1 _]]].
  if_tac. rewrite if_false by lia. auto. auto.
- specialize (H1 i' j'). destruct H1 as [_ [_ [_ H1]]].
  unfold updij.
  rewrite if_false by lia. apply H1; lia.
Qed.

Lemma subtract_another:
  forall i j k (A R: Z -> Z -> ftype t),
    0 <= i <= j -> 0 <= k < j ->
    subtract_loop A R i j (k+1) = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
unfold subtract_loop at 1.
replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
rewrite Zrangelist_plus1.
simpl.
rewrite !map_app.
simpl map.
rewrite fold_left_app.
simpl.
f_equal.
lia.
Qed.

(* END copied from iterative_methods/cholesky/verif_cholesky.v *)
End WithSTD.

Lemma cholesky_jik_upto_newrow:
 forall t n j (A R: Z -> Z -> ftype t),
  0 <= j < n ->
  cholesky_jik_upto n j j A R ->
  cholesky_jik_upto n 0 (j+1) A (updij R j j (BSQRT (subtract_loop A R j j j))).
Proof.
intros.
intros i' j'.
destruct (H0 i' j') as [? [? [? ?]]]; clear H0.
split; [ | split3]; intros; try split; hnf; intros; try lia.
-
 clear H4.
 destruct (zlt j' j).
 + destruct (H1 l H5); clear H1 H7. specialize (H4 ltac:(lia)). clear H2 H3 H0.
   unfold updij at 1. if_tac; try lia. rewrite H4. f_equal.
   * unfold subtract_loop. f_equal.
     apply map_ext_Forall.
     apply Forall_Zrangelist.
     intros. unfold updij. repeat if_tac; try lia; auto.
   * unfold updij. rewrite if_false by lia. auto.
 + assert (j'=j) by lia. subst j'. clear H1 H3.
   unfold updij at 1. if_tac; try lia.
   specialize (H2 eq_refl ltac:(lia)). destruct H2; auto.
   rewrite H2 by auto. f_equal.
   * unfold subtract_loop. f_equal.
     apply map_ext_Forall.
     apply Forall_Zrangelist.
     intros. unfold updij. repeat if_tac; try lia; auto.
   * unfold updij. if_tac; try lia; auto.
- subst j'.
  destruct (zeq i' j).
 + subst. unfold updij. rewrite !if_true by auto. f_equal.
   unfold subtract_loop. f_equal.
   apply map_ext_Forall.
   apply Forall_Zrangelist.
   intros. repeat if_tac; try lia; auto.
 + unfold updij at 1. rewrite !if_false by lia.
   destruct (H1 ltac:(lia) H5). rewrite H7; auto.
   f_equal.
   unfold subtract_loop. f_equal.
   apply map_ext_Forall.
   apply Forall_Zrangelist.
   intros. unfold updij; repeat if_tac; try lia; auto.
- unfold updij. repeat if_tac; try lia. subst i'.
  apply H3; lia.
  apply H3; lia.
- unfold updij. repeat if_tac; try lia; apply H3; lia.
Qed.

Definition forward_subst_step {t: type} (n: Z) 
         (L: Z -> Z -> ftype t) (x: list (ftype t)) (i: Z ) 
     : list (ftype t)  :=
   upd_Znth i x
    (BDIV (fold_left BMINUS
           (map (fun j => BMULT (L i j) (Znth j x)) (Zrangelist 0 i))
           (Znth i x))
          (L i i)).


Definition forward_subst {t: type} (n: Z)
         (L: Z -> Z -> ftype t) (x: list (ftype t)) : list (ftype t) :=
  fold_left (forward_subst_step n L) (Zrangelist 0 n) x.

Definition backward_subst_step {t: type} (n: Z)
         (U: Z -> Z -> ftype t) (x: list (ftype t)) (i: Z) : list (ftype t) :=
    upd_Znth i x
      (BDIV (fold_left BMINUS 
              (map (fun j => BMULT (U i j) (Znth j x)) (Zrangelist (i+1) n))
              (Znth i x))
         (U i i)).

Definition backward_subst {t: type} (n: Z)
         (U: Z -> Z -> ftype t) (x: list (ftype t)) : list (ftype t) :=
     fold_left (backward_subst_step n U) (rev (Zrangelist 0 n)) x.

Definition transpose {T: Type} (A: Z -> Z -> T) : Z -> Z -> T :=
  fun i j => A j i.

 
