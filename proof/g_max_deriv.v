From mathcomp Require Import boot algebra all_classical all_analysis order reals.
Import numFieldNormedType.Exports.
From mathcomp.algebra Require Import ring_tactic.
From Stdlib Require Import FunctionalExtensionality.
From mathcomp.zify Require Import ssrZ zify.
Import measurable_realfun MeasurableRopen.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp Require Import polydiv. Import Pdiv.CommonRing.
From Stdlib Require Reals.
From mathcomp Require Import Rstruct Rstruct_topology.

Set Bullet Behavior "Strict Subproofs".

Open Scope ring_scope.
Open Scope classical_set_scope.

Section R.
Context {R : realType}.
Context (lo hi: R).
Context (Hlo_hi: is_true (lo < hi)).

Notation mu := (@lebesgue_measure R).

Definition fbound (g: R -> R) fb := forall x : R, (lo <= x <= hi) -> ( `| g x | <= fb ).
Definition deriv_bound (f: R -> R) (b: R) := forall x, (lo <= x <= hi) ->
   derivable f x 1 /\ (`| derive1 f x | <= b).

Lemma fine_itv (x y: R) :
  0 <= y -> fine (mu `[x, x + y]) = y.
Proof.
move=> y0.
rewrite lebesgue_measure_itv/= ltEereal/=.
move: y0; rewrite le_eqVlt => /orP[/eqP<-|y0].
  by rewrite addr0 ltxx.
by rewrite ltrDl y0 -EFinD addrAC subrr add0r.
Qed.

Local Lemma admit (P: Prop) : P.
Admitted.

Lemma g_max_deriv_oneway:
       forall (fb d : R) (g : R -> R),
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R,  0<y -> g x <= g(x+y) -> lo <= x <= hi -> lo <= x + y <= hi ->
       `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g Hfb Hd x y Hpos Hpos' Hx Hy.
have H1 : forall z, z \in `]x, x + y[%R -> is_derive z 1 g (g^`() z).
  move=> z /[!in_itv]/= zxy.
  have [] := Hd z; [lra|].
  by move/derivableP; rewrite !derive1E.
have H2 : {within  `[x, x+y], continuous g}.
  apply: derivable_within_continuous => /= z.
  rewrite in_itv/= => zxy.
  by have [] := Hd z => //; lra.
have [] := MVT _ H1 H2; first by lra.
move=> c /[!in_itv]/= cxy ->.
rewrite addrAC subrr add0r mulrC !normrM ler_wpM2l//.
have [|_] := Hd c; first by lra.
move/le_trans; apply.
exact: ler_norm.
Qed.

Lemma g_max_deriv:
       forall (fb d : R) (g : R -> R),
       fbound g fb ->
       deriv_bound g d ->
       forall x y : R, lo <= x <= hi -> lo <= x + y <= hi -> `| g (x + y) - g x | <= `| y * d |.
Proof.
move => fb d g Hfb Hd x y Hx Hy.
(*pose f := comp GRing.opp g.*)
pose f := fun x => - g x.
assert (Hfb': fbound f fb).
  intros z Hz; specialize (Hfb _ Hz); rewrite /f /comp normrN //.
assert (Hd': deriv_bound f d). {
  intros z Hz. destruct (Hd _ Hz).
  split; first exact: derivableN.
  by rewrite /f derive1N // normrN.
}
assert (Hnegy: `|- y * d| = `|y * d|).
 rewrite GRing.mulNr normrN //.
assert (g (x+y) >= g(x) \/ g x >= g(x+y)) by lra.
destruct H; (assert (0 < y \/ 0 < -y \/ y=0) by lra; destruct H0 as [? | [? | ?]]).
- eapply g_max_deriv_oneway; eauto.
- rewrite -Hnegy.
  rewrite -[X in `|X| <= _]opprB opprD -!/(f _) -[X in f X - _](addrK y).
  eapply (g_max_deriv_oneway fb d f); eauto; try lra.
  rewrite /f. replace (x + y - y) with x by lra. rewrite /comp. lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
- replace `|(g (x+y)) - g x| with `|f ((x+y) + -y) - f (x+y)|.
 2:{ f_equal. rewrite /f /comp /=.  replace (x + y - y) with x by lra. lra. }
   replace (x + y - y) with x by lra.
   rewrite distrC. 
  eapply (g_max_deriv_oneway fb d f); eauto; try lra.
  rewrite /f /comp. lra.
- rewrite distrC.
   replace (g x) with (g (x+y + -y)) by (f_equal; lra).
  rewrite -Hnegy.
  eapply (g_max_deriv_oneway fb d g); eauto; try lra.
  replace (x + y - y) with x by lra. lra.
- subst. rewrite GRing.mul0r. rewrite GRing.addr0.
  replace (_ - _) with (@GRing.zero R); auto. lra.
Qed.

Definition testfun_mcr (x : R) := 2^-1 * (1-x) * cos x.

End R.

Import Reals.

Section stdlib_testfun.
Local Open Scope R_scope.

Local Notation R := Rdefinitions.R.

Variables (lo hi : R).

Definition testfun_r (x: R) := /2 * (1-x) * Rtrigo_def.cos x.

Lemma testfun_rE x : testfun_r x = testfun_mcr x.
Proof. by rewrite /testfun_r /testfun_mcr -RcosE -!RealsE. Qed.

Definition testfun_fb : R := 1.
Lemma testfun_fbound: fbound lo hi testfun_r testfun_fb.
Admitted.

Definition testfun_d: R := 1.
Lemma testfun_deriv_bound: deriv_bound lo hi testfun_r testfun_d.
Admitted.

End stdlib_testfun.
