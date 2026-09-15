From mathcomp Require Import all_boot all_algebra  all_field all_analysis all_reals.
From mathcomp.algebra_tactics Require Import ring lra.
Import derive classical_sets.

Set Bullet Behavior "Strict Subproofs".

Open Scope ring_scope.

Section R.
Context {R : realType}.
Context {lo hi: R}.
Context {Hlo_hi: is_true (lo < hi)}.

Notation mu := (@lebesgue_measure R).

Definition fbound (g: R -> R) fb := forall x : R, (lo <= x <= hi) -> ( `| g x | <= fb ).
Definition deriv_bound (f: R -> R) (b: R) := forall x, (lo <= x <= hi) ->
   derivable f x 1 /\ (`| derive1 f x | <= b).

Lemma fine_itv: forall x y: R, 0 <= y -> 
 fine (mu (classical_sets.mkset (fun z : Real.sort R => is_true (z \in `[x, (x + y)%E])))) = y.
Admitted.


Local Lemma admit (P: Prop) : P.
Admitted.

Lemma g_max_deriv_oneway:
       forall (fb d : R) (g : R -> R),
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R,  0<y -> g x <= g(x+y) -> lo <= x <= hi -> lo <= x + y <= hi -> `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g Hfb Hd x y Hpos Hpos' Hx Hy.

assert     (H1: forall  x0,
         @continuous_at
           (@subspace_topology_subspace__canonical__filter_Nbhs
              (join_order_topology_POrderedTopological_between_Order_POrder_and_topology_structure_Topological
                 (numFieldTopology.Real_sort__canonical__order_topology_POrderedTopological R))
           `[x, x + y]%classic)
           _ x0
           (from_subspace `[x, x + y]%classic (derive1 g))).
apply admit. (* do this instead of simply "admit", otherwise lra tactic will shelve this redundantly. *)
assert   (H8 : measurable `[x, (x + y)%E]%classic).
apply admit.

assert (Hd': is_true (0 <= d))
  by (destruct (Hd _ Hx); eapply  preorder.Order.le_trans; [apply Num.Theory.normr_ge0 | eassumption]).

replace (`|y * d|) with (y * `| d |).
 2: rewrite ?Num.Theory.ger0_norm //; apply Num.Theory.mulr_ge0; auto.
rewrite Num.Theory.ger0_norm; [ | lra ].
pose proof @Rintegral_cst _ _  _ mu `[x,  x + y]%classic.
simpl in H. rewrite fine_itv in H; auto.
rewrite GRing.mulrC -{}H.
assert (H2: derivable_oo_LRcontinuous g x (x + y)%E).
apply admit.
pose proof (@continuous_FTC2 R (derive1 g) g x (x+y) ltac:(lra)) H1 H2 ltac:(intros ? ?; reflexivity).
rewrite -EFinD in H.
set u := integral _ _ _ in H.
simpl in u.
destruct u eqn:?H; try discriminate.
subst u.
injection H; clear H; move => H.
rewrite -{}H.  change s with (fine (EFin s)). rewrite -{}H0.
assert (H11: is_true (mu.-integrable `[x, (x + y)%E] (EFin \o g^`()%classic))).
apply admit.
assert (H12: is_true (mu.-integrable `[x, (x + y)%E] (EFin \o (fun=> `|d|)))).
apply admit.
assert (H13:   forall x0 : @g_sigma_algebraType (ocitv_type R) (R.-ocitv).-measurable,
                   x0 \in `[x, (x + y)%E] -> g^`()%classic x0 <= `|d|).
admit.
simpl in H12, H13.
apply le_Rintegral; auto.
apply H8.
Admitted.

Lemma g_max_deriv:
       forall (fb d : R) (g : R -> R),
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R, lo <= x <= hi -> lo <= x + y <= hi -> `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g Hfb Hd x y Hx Hy.
pose f := comp GRing.opp g.
assert (Hfb': fbound f fb).
  intros z Hz; specialize (Hfb _ Hz); rewrite /f /comp Num.Theory.normrN //.
assert (Hd': deriv_bound f d). {
  intros z Hz. destruct (Hd _ Hz).
  split. apply derivableN; auto.
 rewrite /f derive1N // Num.Theory.normrN //.
}
assert (Hnegy: `|- y * d| = `|y * d|).
 rewrite GRing.mulNr Num.Theory.normrN //.
assert (g (x+y) >= g(x) \/ g x >= g(x+y)) by lra.
destruct H; (assert (0 < y \/ 0 < -y \/ y=0) by lra; destruct H0 as [? | [? | ?]]).
- eapply g_max_deriv_oneway; eauto.
- rewrite -Hnegy.
  replace `|(g (x + y) - g x)| with `|comp GRing.opp g ((x+y) + -y) - comp GRing.opp g (x+y)|.
 2:{ f_equal. rewrite /comp /=. replace ((x + y)%E - y) with x by lra. lra. }
  fold f.
  eapply (g_max_deriv_oneway fb d f); eauto; try lra.
  rewrite /f. replace ((x + y)%E - y) with x by lra. rewrite /comp. lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
- replace `|(g (x+y)) - g x| with `|f ((x+y) + -y) - f (x+y)|.
 2:{ f_equal. rewrite /f /comp /=.  replace ((x + y)%E - y) with x by lra. lra. }
   replace ((x + y)%E - y) with x by lra.
   rewrite Num.Theory.distrC. 
  eapply (g_max_deriv_oneway fb d f); eauto; try lra.
  rewrite /f /comp. lra.
- rewrite Num.Theory.distrC.
   replace (g x) with (g (x+y + -y)) by (f_equal; lra).
  rewrite -Hnegy.
  eapply (g_max_deriv_oneway fb d g); eauto; try lra.
  replace ((x + y)%E - y) with x by lra. lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
Qed.




