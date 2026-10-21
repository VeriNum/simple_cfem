From mathcomp Require Import boot order algebra all_classical all_analysis reals.
From mathcomp.algebra Require Import ring_tactic.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp Require Import polydiv.
From mathcomp Require Import Rstruct Rstruct_topology.
From Stdlib Require Reals.

Import Order.TTheory GRing.Theory Num.Theory GRing.Theory.
Import numFieldNormedType.Exports.
Import measurable_realfun MeasurableRopen.
Import Pdiv.CommonRing.

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
       forall (d : R) (g : R -> R),
       deriv_bound g d ->
       forall x y : R,  0<y -> lo <= x <= hi -> lo <= x + y <= hi ->
       `| g (x + y) - g x | <= `| y * d |.
Proof.
move => d g Hd x y Hpos Hx Hy.
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
       forall (d : R) (g : R -> R),
       deriv_bound g d ->
       forall x y : R, lo <= x <= hi -> lo <= x + y <= hi ->
       `| g (x + y) - g x | <= `| y * d |.
Proof.
move => d g Hd x y Hx Hy.
have [y0|y0|->]  := ltgtP y 0; last 2 first.
- exact: (g_max_deriv_oneway _ _  Hd).
- by rewrite addr0 subrr normr0 normr_ge0.
- rewrite -[X in g _ - g X]addr0 -(subrr y) addrA distrC.
  rewrite -[leRHS]normrN -mulNr.
  set x' := x + y; set y' := - y.
  by apply: (g_max_deriv_oneway _ _ Hd); rewrite /x' /y'; lra.
Qed.

End R.

Section testfun_mcr.
Context {R : realType}.

Definition testfun_mcr (x : R) := 2^-1 * (1-x) * cos x.

Lemma ler_pdist (x y c : R) :
  0 <= x <= c -> 0 <= y <= c -> `| x - y | <= c.
Proof.
move=> /andP[] x0 xc /andP[] y0 yc.
rewrite ler_norml.
rewrite lerBlDl lerBrDl.
rewrite (@le_trans _ _ 0) ?subr_le0//=.
by rewrite (@le_trans _ _ c) ?lerDr.
Qed.

Lemma testfun_mcr_deriv_bound : deriv_bound (-1) 1 testfun_mcr 1.
Proof.
rewrite /testfun_mcr => x /andP[] N1x x1.
split; first by [].
  (* this automation might look beautiful but it is much faster to manually apply lemmas: *)
  (*
  Profile by [].
  > major words: 4.41E+05 words
  > minor words: 4.3E+08 words
  > major collections: 0
  > minor collections: 13
  > instructions: 5330769793
  > 
  > Proofview.apply:  761ms 526us, 2 calls
  > pretyping:        760ms 648us, 2 calls
  > typeclass search: 758ms 988us, 1 calls
  > Conversion:       733ms 304us, 803 calls
  > unification:      530us 005ns, 3 calls

  Profile
    apply: derivableM; [
      apply: derivableM; [exact: derivable_cst |
        apply: derivableD; [exact: derivable_cst |
          exact: derivable_opp]] |
      exact: derivable_cos].
  > major words: 5.29E+04 words
  > minor words: 4.25E+07 words
  > major collections: 0
  > minor collections: 1
  > instructions: 549927958
  > 
  > Proofview.apply: 094ms 872us, 1 calls
  > unification:     081ms 090us, 90 calls
  > Conversion:      076ms 094us, 50 calls
  > pretyping:       050ms 727us, 41 calls
  > intern:          001ms 130us, 14 calls
  *)
rewrite derive1E deriveM//=.
(* this `//` is essentially repeating the derivability proofs as above (thus slow) *)
rewrite !deriveM//=.
rewrite !deriveB//=.
rewrite !derive_cst derive_id.
rewrite sub0r scaler0 addr0.
have [_ ->] := is_derive_cos x.
rewrite /GRing.scale/=.
rewrite (mulrC (cos x)) -!mulrA -mulrDr !normrM.
rewrite normfV ger0_norm// -ler_pdivlMl// ?invr_gt0// invrK mulr1.
rewrite mulrBl mulNr !mulrN !mul1r opprK -addrA.
rewrite (le_trans (ler_normD _ _))// (_ : 2 = 1 + 1)// lerD//.
  by rewrite normrN sin_max.
have Nx1 : - x <= 1 by rewrite -lerN2 opprK.
have sin_ge0 y : 0 <= y -> y <= 1 -> 0 <= sin y.
  move=> y0 y1.
  rewrite sin_ge0_pi// y0/=.
  rewrite (le_trans _ pi_ge2)// (@le_trans _ _ 1)//.
  lra.
have cos_ge0 y : 0 <= y -> y <= 1 -> 0 <= cos y.
  move=> y0 y1.
  rewrite cos_ge0_pihalf//.
  rewrite (@le_trans _ _ 0)//=.
    by rewrite -lerN2 oppr0 opprK divr_ge0// pi_ge0.
  by rewrite (le_trans _ pihalf_ge1).
rewrite ler_pdist//.
  rewrite -(mulr1 1).
  have [|x0] := ltP x 0; last first.
    by rewrite mulr_ge0 ?sin_ge0//= ler_pM// ?sin_ge0// sin_le1.
  rewrite -oppr_gt0 -mulrNN -sinN => /ltW Nx0.
  by rewrite mulr_ge0 ?sin_ge0//= ler_pM// ?sin_ge0// sin_le1.
rewrite cos_le1 andbT.
have [|x0] := ltP x 0; last by rewrite cos_ge0.
rewrite -oppr_gt0 -cosN => /ltW Nx0.
by rewrite cos_ge0.
Qed.

End testfun_mcr.

Import Reals.

Section stdlib_testfun.
Local Open Scope R_scope.

Local Notation R := Rdefinitions.R.

Definition testfun_r (x: R) := /2 * (1-x) * Rtrigo_def.cos x.

Lemma testfun_rE x : testfun_r x = testfun_mcr x.
Proof. by rewrite /testfun_r /testfun_mcr -RcosE -!RealsE. Qed.

Definition testfun_fb : R := 1.
Lemma testfun_fbound: fbound (-1) 1 testfun_r testfun_fb.
Admitted.

Definition testfun_d: R := 1.
Lemma testfun_deriv_bound: deriv_bound (-1) 1 testfun_r testfun_d.
Proof. rewrite (funext testfun_rE); exact: testfun_mcr_deriv_bound. Qed.

End stdlib_testfun.
