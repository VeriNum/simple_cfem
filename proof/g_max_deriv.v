(* This file currently builds in rocq-mathcomp-analysis.1.16.0 *)

From mathcomp Require Import all_boot all_algebra  all_field all_analysis all_reals.
From mathcomp.algebra_tactics Require Import ring lra.
Import derive classical_sets.
From Stdlib Require Import FunctionalExtensionality.
Set Bullet Behavior "Strict Subproofs".

Open Scope ring_scope.

Section R.
Context {R : realType}.
Context (lo hi: R).
Context (Hlo_hi: is_true (lo < hi)).

Notation mu := (@lebesgue_measure R).

Definition fbound (g: R -> R) fb := forall x : R, (lo <= x <= hi) -> ( `| g x | <= fb ).
Definition deriv_bound (f: R -> R) (b: R) := forall x, (lo <= x <= hi) ->
   derivable f x 1 /\ (`| derive1 f x | <= b).

Lemma fine_itv: forall x y: R, 0 < y -> 
 fine (mu (classical_sets.mkset (fun z : Real.sort R => is_true (z \in `[x, (x + y)%R])))) = y.
Proof.
intros. 
rewrite lebesgue_measure_itv /=.
assert (is_true (preorder.Order.lt (EFin x) (EFin (x+y)))).
change (is_true (preorder.Order.lt x (x+y))).
lra.
rewrite H0.
simpl. lra.
Qed.

Definition Rtopo := 
           @subspace_topology_subspace__canonical__filter_Nbhs
              (join_order_topology_POrderedTopological_between_Order_POrder_and_topology_structure_Topological
                 (numFieldTopology.Real_sort__canonical__order_topology_POrderedTopological R)).

Lemma within_continuous_cst:
 forall (s : interval (Real.sort R)) (c: Real.sort R),
  forall x : @subspace (GRing.regular (Real.sort R))  [set` s],
  @continuous_at _ (GRing_regular__canonical__filter_Nbhs (reals_Real__to__Num_NumDomain R)) x
      (from_subspace [set` s]   (fun=> c)).
Proof.
intros * ? ?.
hnf; simpl.
hnf in H; simpl in H.
destruct H as [a H H0].
unfold from_subspace in H0.
unfold from_subspace.
unfold preimage.
rewrite {6}/mkset.
rewrite /globally /=.
rewrite {4}/mkset /=.
destruct (in_mem _ _); simpl.
2:{ intros; apply H0. subst x0.
set n := Num.norm.
 replace (fun _ =>   _) with n; [ | extensionality zz; auto].
subst n.
simpl.
rewrite Num.Theory.ger0_norm; try lra.
}
exists a; auto.
intros ? ? ?.
apply H0.
hnf.
rewrite Num.Theory.ger0_norm; try lra.
Qed.

Lemma within_continuous_subset: 
 forall (s t : set (Real.sort R)) (g: Real.sort R -> Real.sort R),
  subset s t ->
  (forall x : @subspace (GRing.regular (Real.sort R))  t,
  @continuous_at _ (GRing_regular__canonical__filter_Nbhs (reals_Real__to__Num_NumDomain R)) x
      (from_subspace t g)) ->
  (forall x : @subspace (GRing.regular (Real.sort R))  s,
  @continuous_at _ (GRing_regular__canonical__filter_Nbhs (reals_Real__to__Num_NumDomain R)) x
      (from_subspace s g)).
Proof.
intros.
unfold subspace in x.
unfold subspace in H0.
pose proof (H0 x).
unfold from_subspace in H1|-*.
intros ? ?.
simpl in t0.
specialize (H1 t0).
apply H1 in H2.
simpl in *.
red in H2 |- *.
simpl in *.
red in H2|-*.
simpl in *.
red in H2|-*.
assert (H' := H).
rewrite -subsetP in H.
specialize (H x).
set b := in_mem x (mem s) in H|-*.
destruct b eqn:Hb.
-
subst b.
rewrite H in H2; auto.
red in H2|-*; simpl in *.
red in H2|-*.
red in H2|-*.
simpl in *.
red in H2|-*.
simpl in *.

red in H2|-*.
simpl in *.

red in H2|-*.
simpl in *.
destruct H2 as [a H2 H3].
exists a; auto.
intros  ? ? ?. specialize (H3 t1 H4).
simpl in H3.
apply H3.
apply H'; auto.
-
hnf; simpl.
intros.
subst x0.
destruct (in_mem _ _) eqn:Hd in H2.
hnf in H2; simpl in H2.
destruct H2 as [a H2 H3].
hnf in H3; simpl in H3.
apply H3.
rewrite Num.Theory.ger0_norm; try lra.
clear - Hd.
unfold in_mem, mem in Hd. simpl in Hd.
unfold in_set in Hd.
unfold boolp.asbool in Hd.
destruct (boolp.pselect (t x)); auto. discriminate.
hnf in H2; simpl in H2.
apply H2. auto.
Qed.

Lemma within_continuous_derive1_N:
forall (g: R -> R),
   derivable_oo_LRcontinuous g lo hi ->
   (forall  x0, @continuous_at (Rtopo `[lo, hi]%classic)  _ x0 (from_subspace `[lo,hi]%classic (derive1 g))) ->
 (forall  x0, @continuous_at (Rtopo `[lo, hi]%classic)  _ x0 (from_subspace `[lo,hi]%classic 
      (derive1 (@Algebra.opp
          (functions.prod__canonical__Algebra_BaseZmodule (Num.RealField.sort _)
             (Num_RealField__to__Algebra_Zmodule _))
          g)))).
Admitted.

Lemma derivable_oo_LRcontinuousN:
 forall (g: R -> R), 
  derivable_oo_LRcontinuous g lo hi ->
  derivable_oo_LRcontinuous
   (@Algebra.opp
          (functions.prod__canonical__Algebra_BaseZmodule (Num.RealField.sort _)
             (Num_RealField__to__Algebra_Zmodule _))
          g) lo hi.
Admitted.

Lemma integrable_derive1:
 forall (g : Real.sort R -> Real.sort R)
   (x y : Real.sort R)
   (H: x < y)
  (H2 : derivable_oo_LRcontinuous g x y),
  is_true (mu.-integrable `[x, y] (EFin \o g^`()%classic)).
Admitted.


Lemma g_max_deriv_oneway:
       forall (fb d : R) (g : R -> R),
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R,  
       (forall  x0,
         @continuous_at
           (Rtopo
           `[x, x + y]%classic)  _ x0 (from_subspace `[x, x + y]%classic (derive1 g))) ->
       derivable_oo_LRcontinuous g x (x + y) ->
       0<y -> 
       g x <= g(x+y) -> 
       lo <= x <= hi -> 
       lo <= x + y <= hi ->
       `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g Hfb Hd x y H1 H2 Hpos Hpos' Hx Hy.
assert   (H8 : measurable `[x, x + y]%classic) by apply measurable_itv.
assert (Hd': is_true (0 <= d))
  by (destruct (Hd _ Hx); eapply  preorder.Order.le_trans; [apply Num.Theory.normr_ge0 | eassumption]).

replace (`|y * d|) with (y * `| d |).
 2: rewrite ?Num.Theory.ger0_norm //; apply Num.Theory.mulr_ge0; auto.
rewrite Num.Theory.ger0_norm; [ | lra ].
pose proof @Rintegral_cst _ _  _ mu `[x,  x + y]%classic.
simpl in H. rewrite fine_itv in H; auto.
rewrite GRing.mulrC -{}H.
pose proof (@continuous_FTC2 R (derive1 g) g x (x+y) ltac:(lra)) H1 H2 ltac:(intros ? ?; reflexivity).
rewrite -EFinD in H.
set u := integral _ _ _ in H.
simpl in u.
destruct u eqn:?H; try discriminate.
subst u.
injection H; clear H; move => H.
rewrite -{}H.  change s with (fine (EFin s)). rewrite -{}H0.
assert (H11: is_true (mu.-integrable `[x, x + y] (EFin \o g^`()%classic))).
 apply integrable_derive1; auto. lra.
assert (H12: is_true (mu.-integrable `[x, x + y] (EFin \o (fun=> `|d|)))). {
apply continuous_compact_integrable.
apply segment_compact.
apply within_continuous_cst.
}

assert (H13:   forall x0 : @g_sigma_algebraType (ocitv_type R) (R.-ocitv).-measurable,
                   x0 \in `[x, x + y] -> g^`()%classic x0 <= `|d|). {
 intros.
 destruct (Hd x0).
 change (is_true (x <= x0 <= x+y)) in H. lra.
 rewrite Num.Theory.ger0_norm; auto.
 set a := derive1 g x0 in H3|-*.
 clearbody a. simpl in a. clear - H3.
 eapply preorder.Order.le_trans.
 apply Num.Theory.ler_norm.
 apply H3.
}
simpl in H12, H13.
apply le_Rintegral; auto.
apply H8.
Qed.

Lemma g_max_deriv:
       forall (fb d : R) (g : R -> R),
       (forall  x0, @continuous_at (Rtopo `[lo, hi]%classic)  _ x0 (from_subspace `[lo,hi]%classic (derive1 g))) ->
       derivable_oo_LRcontinuous g lo hi ->
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R,
        lo <= x <= hi -> lo <= x + y <= hi -> `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g H1 H2 Hfb Hd x y Hx Hy.
pose f := (@Algebra.opp
          (functions.prod__canonical__Algebra_BaseZmodule (Num.RealField.sort _)
             (Num_RealField__to__Algebra_Zmodule _))
          g). simpl in f.
assert (Hfb': fbound f fb).
  intros z Hz; specialize (Hfb _ Hz); rewrite /f Num.Theory.normrN //.
assert (Hd': deriv_bound f d). {
  intros z Hz. destruct (Hd _ Hz).
  split. apply derivableN; auto.
 rewrite /f derive1N // Num.Theory.normrN //.
}
assert (H1': forall  x0, @continuous_at (Rtopo `[lo, hi]%classic)  _ x0 (from_subspace `[lo,hi]%classic (derive1 f))).
    apply within_continuous_derive1_N; auto.
assert (H2': derivable_oo_LRcontinuous f lo hi).
    apply derivable_oo_LRcontinuousN; auto.
assert (Hnegy: `|- y * d| = `|y * d|).
 rewrite GRing.mulNr Num.Theory.normrN //.
assert (g (x+y) >= g(x) \/ g x >= g(x+y)) by lra.
destruct H; (assert (0 < y \/ 0 < -y \/ y=0) by lra; destruct H0 as [? | [? | ?]]).
- apply (g_max_deriv_oneway fb d g); auto.
  eapply within_continuous_subset; try apply H1;
  rewrite -subset_itvP; apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
  apply (@derivable_oo_continuousW _  _ lo hi); auto; try lra;
    apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
- rewrite -Hnegy.
  replace `|(g (x + y) - g x)| with `|f ((x+y) + -y) - f (x+y)|.
 2:{ f_equal. change (f ?A) with (- (g A)). replace ((x + y) - y) with x by lra. lra. }
  eapply (g_max_deriv_oneway fb d f); try assumption;
  replace ((x + y) - y) with x by lra; auto.
  eapply within_continuous_subset; try apply H1';
  rewrite -subset_itvP; apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
  apply (@derivable_oo_continuousW _  _ lo hi); auto; try lra;
    apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
   change (f ?x) with (- g x). lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
- replace `|(g (x+y)) - g x| with `|f ((x+y) + -y) - f (x+y)|.
 2:{ f_equal. change (f ?A) with (- (g A)). replace ((x + y) - y) with x by lra. lra. }
   replace ((x + y) - y) with x by lra.
   rewrite Num.Theory.distrC. 
  apply (g_max_deriv_oneway fb d f); try assumption; try lra.
  eapply within_continuous_subset; try apply H1';
  rewrite -subset_itvP; apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
  apply (@derivable_oo_continuousW _  _ lo hi); auto; try lra;
    apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
   change (f ?x) with (- g x). lra.
- rewrite Num.Theory.distrC.
   replace (g x) with (g (x+y + -y)) by (f_equal; lra).
  rewrite -Hnegy.
  eapply (g_max_deriv_oneway fb d g); try eassumption.
  eapply within_continuous_subset; try apply H1;
  rewrite -subset_itvP; apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
  apply (@derivable_oo_continuousW _  _ lo hi); auto; try lra;
    apply interval.subset_itv; rewrite /preorder.Order.le /=; lra.
  replace ((x + y) - y) with x by lra. lra. lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
Qed.

End R.

Module Example.

Section R.
Context {R : realType}.

Definition lo : R := -1.
Definition hi : R := 1.
Lemma Hlo_hi : lo < hi.
Proof. rewrite /lo /hi. lra. Qed.

Definition g (x: R) := (1/2 * (1-x) * cos x).

Definition fb : R := 1/2.
Definition d : R := 1.

Lemma within_continuous_g: 
       (forall  x0, @continuous_at (Rtopo `[lo, hi]%classic)  _ x0 (from_subspace `[lo,hi]%classic (derive1 g))).
Admitted.

Lemma derivable_oo_continuous_g: 
@derivable_oo_LRcontinuous (reals_Real__to__Num_NumField R)
  (Real_sort__canonical__normed_module_NormedModule R) g lo hi.
Admitted.

Lemma fbound_g: fbound lo hi g fb.
Admitted.

Lemma deriv_bound_g:  deriv_bound lo hi g d.
Admitted.

Lemma g_max_deriv: 
       forall x y : R,
        lo <= x <= hi -> lo <= x + y <= hi -> `| g (x + y) - g x | <= `| y * d |.
Proof.
intros.
apply (g_max_deriv lo hi Hlo_hi fb); auto.
apply within_continuous_g.
apply derivable_oo_continuous_g.
apply fbound_g.
apply deriv_bound_g.
Qed.

End R.
End Example.





