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

Definition list_of_fun (n: Z) (f: Z -> val) : list val :=
 map (fun j => f (Z.of_nat j)) (seq.iota 0 (Z.to_nat n)).

Definition lists_of_fun (n: Z) (f: Z -> Z -> val) :=
 map (fun i => list_of_fun n (f (Z.of_nat i))) (seq.iota 0 (Z.to_nat n)).

Lemma Znth_i_iota:
  forall lo i hi, 
   0 <= i < Z.of_nat hi -> Znth i (seq.iota lo hi) = (lo+Z.to_nat i)%nat.
Proof.
 intros.
 rewrite <- (Z2Nat.id i) in * by lia.
 rewrite <- nth_Znth'.
 rewrite Nat2Z.id by lia.
 revert lo hi H; induction (Z.to_nat i); destruct hi; simpl; intros; try lia.
 rewrite IHn by lia. lia.
Qed.


Lemma Zlength_iota:
  forall lo n, Zlength (seq.iota lo n) = Z.of_nat n.
Proof.
intros. rewrite Zlength_correct. f_equal. apply seq.size_iota.
Qed.

Lemma Znth_i_list_of_fun:
  forall d f i n, 0 <= i < n -> @Znth _ d i (list_of_fun n f) = f i.
Proof.
 intros.
 unfold list_of_fun.
 rewrite Znth_map by (rewrite Zlength_iota; rep_lia).
 rewrite Znth_i_iota by rep_lia. f_equal; lia. 
Qed.

(*

Lemma length_iota:
  forall lo n, length (iota lo n) = n.
Proof.
intros. revert lo; induction n; simpl; intros; auto.
Qed.
*)

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

Lemma upto_iota:
 forall n, upto n= map Z.of_nat (seq.iota O n).
Proof.
intros.
transitivity (map (Z.add (Z.of_nat O)) (upto n)).
induction n; simpl; f_equal. rewrite map_map. f_equal.
forget O as x. revert x; induction n; simpl; intros; f_equal.
lia. rewrite <- (IHn (S x)). rewrite map_map. f_equal. extensionality y. lia.
Qed.

Lemma iota_range: forall k n, In k (seq.iota 0 n) -> (k<n)%nat.
Proof.
intros.
replace k with (k-O)%nat by lia.
forget O as u.
revert k u H; induction n; intros; try lia.
contradiction H.
replace (S n) with (n+1)%nat in H by lia.
rewrite iota_plus1 in H.
rewrite in_app in H. destruct H.
apply IHn in H; lia.
destruct H; try contradiction. lia.
Qed.

Section WithSTD.
Context {t : type}.

Definition neg_zero : ftype t := Binary.B754_zero (fprec t) (femax t) true.

Definition sumF := fold_right BPLUS neg_zero.

Definition subtract_loop (A R: Z -> Z -> ftype t) (i j k: Z) :=
  fold_left BMINUS
    (map (fun k' => BMULT (R k' i) (R k' j)) (map Z.of_nat (seq.iota 0 (Z.to_nat k))))
     (A i j).

Definition sum_upto (n: Z) (f: Z -> ftype t) :=
  sumF (map (fun k => f (Z.of_nat k)) (seq.iota 0 (Z.to_nat n))).     

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

Variable Vflo: ftype t -> val.

Definition done_to_ij (n i j: Z) (R: Z -> Z -> ftype t) (i' j': Z) : val :=
  if zlt i' 0 then Vundef
  else if zlt j' 0 then Vundef
  else if zlt j' i' then Vundef
  else if zlt (j'+1) j
         then Vflo (R i' j')
  else if zeq (j'+1) j
       then if zlt i' i
           then Vflo (R i' j')
           else Vundef
  else Vundef.

Definition done_to_n (n: Z) := done_to_ij n n n.


Lemma Znth_lists_done: 
   forall N n A d d' i j imax jmax,
   n <= N ->
   imax <= n -> jmax <= n ->
   0 <= i ->
   0 <= j < jmax ->
   i <= j ->
   (j+1=jmax -> i<imax) ->
   @Znth _ d j (@Znth _ d' i (lists_of_fun N (done_to_ij n imax jmax A))) = 
   Vflo (A i j).
Proof.
intros.
unfold lists_of_fun, done_to_ij.
rewrite Znth_map by (rewrite Zlength_iota; lia).
rewrite Znth_i_list_of_fun by rep_lia.
rewrite Znth_i_iota by lia.
rewrite !if_false by rep_lia.
if_tac. simpl; f_equal. f_equal. lia.
if_tac; try lia.
rewrite if_true by lia.
simpl; f_equal. f_equal. lia.
Qed.

Lemma upd_Znth_lists_of_fun:
  forall d N n R i j x,
   0 <= i <= j -> j < N ->
  
   upd_Znth i (lists_of_fun N (done_to_ij n i (j + 1) R))
     (upd_Znth j (@Znth _ d i (lists_of_fun N (done_to_ij n i (j + 1) R)))
        (Vflo x))
    = lists_of_fun N (done_to_ij n (i+1) (j+1) (updij R i j x)).
Proof.
intros.
unfold lists_of_fun.
set (f i0 := list_of_fun _ _).
rewrite Znth_map by (rewrite Zlength_iota; lia).
rewrite Znth_i_iota by lia.
simpl.
rewrite upd_Znth_eq by (rewrite Zlength_map, Zlength_iota; lia).
rewrite map_length, seq.size_iota.
rewrite upto_iota.
rewrite map_map.
apply map_ext_in.
intro k.
intro.
apply iota_range in H1.
subst f.
if_tac.
- subst i.
unfold list_of_fun.
rewrite upd_Znth_eq by (rewrite Zlength_map, Zlength_iota; lia).
rewrite map_length.
rewrite seq.size_iota.
rewrite upto_iota, map_map.
apply map_ext_in.
intros.
apply iota_range in H2.
if_tac.
+
subst j.
unfold done_to_ij.
rewrite !if_false by lia.
unfold updij.
rewrite !if_true by lia.
reflexivity.
+
rewrite Znth_map by (rewrite Zlength_iota; lia).
unfold done_to_ij.
rewrite Nat2Z.id.
unfold updij.
rewrite !if_false by lia.
rewrite Znth_i_iota by lia.
rewrite Nat2Z.id.
simpl.
if_tac.
rewrite !if_false by lia. auto.
if_tac.
rewrite !if_false by lia.
rewrite !if_true by lia.
rewrite if_false by lia.
auto.
if_tac; try lia.
rewrite !if_false by lia.
auto. 
-
rewrite Znth_map by (rewrite Zlength_iota; lia).
rewrite Znth_i_iota by lia.
simpl Nat.add.
rewrite Nat2Z.id.
f_equal.
unfold done_to_ij.
simpl.
extensionality j'.
rewrite !if_false by lia.
if_tac.
if_tac; auto.
if_tac.
if_tac; auto.
if_tac.
rewrite if_false by lia.
unfold updij.
rewrite if_false by lia.
auto.
if_tac; try lia.
if_tac; try lia.
rewrite if_false by lia.
rewrite if_true by lia.
unfold updij.
rewrite if_false by lia.
auto.
rewrite if_false by lia.
rewrite if_false by lia.
auto.
if_tac; auto.
Qed.

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
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H3.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
* rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
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
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  *
  rewrite H1 by lia. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
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
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H0.
  subst f. simpl. if_tac; try lia; auto.
  * assert (i'<i) by lia. clear H5 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ [H1 _]].
   destruct H1 as [H1 _]; try lia. rewrite H1 by auto.
   f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H3.
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
rewrite iota_plus1.
simpl.
rewrite !map_app.
simpl map.
rewrite fold_left_app.
simpl.
f_equal.
rewrite Z2Nat.id by lia.
f_equal.
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
     rewrite !map_map.
     apply map_ext_Forall.
     apply FPStdLib.Forall_seq.
     intros. unfold updij. repeat if_tac; try lia; auto.
   * unfold updij. rewrite if_false by lia. auto.
 + assert (j'=j) by lia. subst j'. clear H1 H3.
   unfold updij at 1. if_tac; try lia.
   specialize (H2 eq_refl ltac:(lia)). destruct H2; auto.
   rewrite H2 by auto. f_equal.
   * unfold subtract_loop. f_equal.
     rewrite !map_map.
     apply map_ext_Forall.
     apply FPStdLib.Forall_seq.
     intros. unfold updij. repeat if_tac; try lia; auto.
   * unfold updij. if_tac; try lia; auto.
- subst j'.
  destruct (zeq i' j).
 + subst. unfold updij. rewrite !if_true by auto. f_equal.
   unfold subtract_loop. f_equal.
   rewrite !map_map.
   apply map_ext_Forall.
   apply FPStdLib.Forall_seq.
   intros. repeat if_tac; try lia; auto.
 + unfold updij at 1. rewrite !if_false by lia.
   destruct (H1 ltac:(lia) H5). rewrite H7; auto.
   f_equal.
   unfold subtract_loop. f_equal.
   rewrite !map_map.
   apply map_ext_Forall.
   apply FPStdLib.Forall_seq.
   intros. unfold updij; repeat if_tac; try lia; auto.
- unfold updij. repeat if_tac; try lia. subst i'.
  apply H3; lia.
  apply H3; lia.
- unfold updij. repeat if_tac; try lia; apply H3; lia.
Qed.

