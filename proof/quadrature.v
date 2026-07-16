(** * CFEM.quadrature:  Gaussian quadrature, following G. W. Stewart *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
Locate Ltac lra.
Import classical_sets.
Import numFieldNormedType.Exports.
From Stdlib Require Import FunctionalExtensionality.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.


(** First, some preliminaries *)

(* begin details : Many general-purpose supporting lemmas, not specific to quadrature *)

Lemma size_behead: forall {A} [n] (x: (n.+1).-tuple A), size (behead x) == n.
Proof. intros; rewrite size_behead size_tuple //. Qed.

Definition tuple_behead {A} [n] (x: n.+1.-tuple A) : n.-tuple A :=
  Tuple (size_behead x).

Lemma tuple_ext: forall {A}[n] (x y: n.-tuple A), tval x = tval y -> x=y.
Proof.
intros.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *; subst x. f_equal.
apply eq_irrelevance.
Qed.

Lemma tuple_rehead {A} [n] (x: n.+1.-tuple A): cons_tuple (thead x) (tuple_behead x) = x.
Proof.
apply tuple_ext.
simpl.
pose proof tuple_eta x. symmetry.
destruct x; simpl in H. inversion  H. simpl. auto.
Qed.


Lemma sorted_ij {R: realType}: 
 forall (rl: list R) (i j: nat) (d1 d2: R),
  is_true (sorted <%R rl) ->
  is_true (i < size rl)%N ->
  is_true (j < size rl)%N ->
  (nth d1 rl i < nth d2 rl j)%R = (i < j)%N.
Proof.
intros.
revert i j H0 H1; induction rl; intros.
simpl in H0; Lia.lia.
simpl in H0,H1.
destruct i,j; simpl in *.
-
rewrite ltnn lt_irreflexive //.
-
rewrite ltn0Sn.
 apply order_path_min in H; [ | intros ? ? ?; lra].
  pose proof (@all_nthP _  (> a)  rl d2). rewrite H in H2. inversion H2.
  rewrite H3; auto.
-
 replace (i.+1<0)%N with false by Lia.lia.
 apply order_path_min in H; [ | intros ? ? ?; lra].
  pose proof (@all_nthP _  (> a)  rl d1). rewrite H in H2. inversion H2.
  assert (is_true (i<size rl)%N). Lia.lia.
  specialize (H3 _ H4). lra.
-
 rewrite IHrl; auto.
 apply path_sorted in H; auto.
Qed.

Module Rewriting.

 Section R.
 Context {R : realType}.

Lemma hornerXsubC': forall [R : nzRingType] (a : NzRing.sort R), horner('X - a%:P) = (id \- fun=>a).
Proof.
intros. extensionality x. apply hornerXsubC.
Qed.

Lemma hornerX': forall {R : nzSemiRingType}, @horner R ('X) = id.
Proof.
intros. extensionality x. apply hornerX.
Qed.

Lemma hornerC': forall (c: R), horner (polyC c) = (fun=>c).
Proof. intros. extensionality x. apply hornerC.
Qed.

Lemma hornerD': forall [R] (a b: {poly R}), horner (a+b) = horner a \+ horner b.
Proof. intros. extensionality x. apply hornerD.
Qed.

Lemma hornerM': forall [R: comNzSemiRingType] (a b: {poly R}), horner (a*b) = horner a \* horner b.
Proof. intros. extensionality x. apply hornerM.
Qed.

Lemma hornerN': forall [R: nzRingType] (a: {poly R}), horner (- a) = \- horner a.
Proof. intros. extensionality x. apply hornerN.
Qed.

Definition r_horner := (@hornerXsubC, @hornerXsubC', @hornerX, @hornerX', @hornerC, @hornerC',
                                      @hornerD, @hornerD', @hornerM, @hornerM', @hornerN, @hornerN').

Lemma mul_fun1r: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun (fun=>1) f = f.
Proof.
intros. extensionality x. simpl. apply mul1r.
Qed.

Lemma mul_funr1: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun f (fun=>1) = f.
Proof.
intros. extensionality x. simpl. apply mulr1.
Qed.
Hint Rewrite @mul1r @mul_fun1r @mulr1 @mul_funr1 : horner.

Lemma mul_fun0r: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun (fun=>0) f = (fun=>0).
Proof.
intros. extensionality x. simpl. apply mul0r.
Qed.

Lemma mul_funr0: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun f (fun=>0) = (fun=>0).
Proof.
intros. extensionality x. simpl. apply mulr0.
Qed.
Hint Rewrite @mul0r @mul_fun0r @mulr0 @mul_funr0 : horner.

Lemma opp_funC: forall  {U : Type} {V : BaseZmodule.type} (c: V), 
  @opp_fun U V (fun=>c) = (fun=> opp c).
Proof.
intros. extensionality x. reflexivity.
Qed.

Lemma opp_funr0:  forall {U: Type}, (fun _:U=> (-0):R) = (fun _:U => 0:R).
Proof.
intros. extensionality x. apply oppr0.
Qed.

Lemma sub_funr0: forall {U: Type} {V: zmodType} (f: U -> V),
  sub_fun f (fun=>0) = f.
Proof. intros. extensionality x. simpl. apply subr0.
Qed.

Lemma add_fun0r: forall {U: Type} {V: nmodType} (f: U -> V),
  add_fun (fun=>0) f = f.
Proof. intros. extensionality x. simpl. apply add0r.
Qed.

Lemma add_funr0: forall {U: Type} {V: nmodType} (f: U -> V),
  add_fun f (fun=>0) = f.
Proof. intros. extensionality x. simpl. apply addr0.
Qed.

Lemma mul_funDr: forall  {s : pzSemiRingType} {T: Type},
   @right_distributive (T -> PzSemiRing.sort s) _ mul_fun add_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrDr. Qed.

Lemma mul_funDl: forall  {s : pzSemiRingType} {T: Type},
   @left_distributive (T -> PzSemiRing.sort s) _ mul_fun add_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrDl. Qed.

Lemma mul_funA: forall  {s : pzSemiRingType} {T: Type},
   @associative (T -> PzSemiRing.sort s) mul_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrA. Qed.

Lemma mul_funC: forall  {s : comPzSemiRingType} {T: Type},
   @commutative (T -> s) _ mul_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrC. Qed.

Lemma mul_fun_consts: forall {s : comPzSemiRingType} {T: Type} (a b: s),
    @mul_fun s T (fun=>a) (fun=>b) = fun=> a*b.
Proof. intros; extensionality i; auto. Qed.

Definition r_ring := (@mulr1, @mul1r, @mulr0, @mul0r, @addr0, @add0r, @oppr0, @subr0).
Definition r_lift := (@mul_funr1, @mul_fun1r, @mul_funr0, @mul_fun0r, @mul_fun_consts,
                               @add_funr0, @add_fun0r, @opp_funr0, @sub_funr0, @opp_funC).

Lemma hornerX_i: (fun x: Real.sort R => x) = (@horner (reals_Real__to__GRing_NzSemiRing R) 'X).
Proof. extensionality x. rewrite hornerX //. Qed.

Lemma poly0 {F: Num.NumDomain.type}: forall f, @poly  F 0 f = 0.
Proof.
intros.
unlock poly.
rewrite locked_withE /poly_expanded_def /= polyC0 //.
Qed.

Lemma mul_polyC': forall a b: R, polyC a * polyC b = polyC (a*b).
Proof.
intros.
rewrite mul_polyC scale_polyC //.
Qed.

Lemma polyCN: forall  (x:R), polyC(opp x) = - polyC x.
Proof. intros.
rewrite -scaleN1r -scale_polyC scaleN1r //.
Qed.

Definition polynil: {poly R} := @Polynomial _ nil oner_neq0.
Lemma polynil_eq: polynil=0.
Proof.
apply /eqP.
rewrite -nil_poly //.
Qed.

Lemma polyC1': 1%:P = @Polynomial R [:: 1] oner_neq0.
Proof.
rewrite polyC1.
apply poly_inj.
rewrite polyseq1 //.
Qed.

Lemma polyC': forall (c: R) (H: is_true (c != 0)), c%:P = @Polynomial R [:: c] H.
Proof.
intros.
apply poly_inj.
unlock polyC. rewrite /insubd /poly_nil /odflt /oapp /insub.
destruct idP; auto.
simpl in n. contradiction.
Qed.

Lemma polyC0': 0%:P = @Polynomial R [:: ] oner_neq0.
Proof.
rewrite polyC0.
rewrite -polynil_eq.
apply poly_inj; auto.
Qed.

Lemma polyX': 'X = @Polynomial R [:: 0; 1] oner_neq0.
Proof.
intros.
unlock polyX; destruct polyX_key; rewrite /polyX_def  /=.
unlock cons_poly;
rewrite ?polyC0' ?polyC1' //.
Qed.

Lemma polyX2': 'X * 'X = @Polynomial R [:: 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyseqMX.
rewrite  /= polyX' //.
rewrite polyX_eq0 //.
Qed.

Lemma polyX3': 'X * ('X * 'X) = @Polynomial R [:: 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX2'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX4': 'X * ('X * ('X * 'X)) = @Polynomial R [:: 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX3'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX5': 'X * ('X * ('X * ('X * 'X))) = @Polynomial R [:: 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX4'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX6': 'X * ('X * ('X * ('X * ('X * 'X)))) = @Polynomial R [:: 0; 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX5'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX7': 'X * ('X * ('X * ('X * ('X * ('X * 'X))))) = @Polynomial R [:: 0; 0; 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX6'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Definition integ (p: {poly R}) : {poly R} := cons_poly 0 (\poly_(i < (size p)) (p`_i / ((S i)%:R))).

Lemma deriv_integ: forall p: {poly R}, deriv (integ p) = p.
Proof.
move => [s H].
rewrite /integ /deriv /=.
apply poly_inj.
destruct (size s) eqn:H0.
-
destruct s; try discriminate H0. clear H0.
rewrite /= poly0 size_cons_poly nil_poly ?eq_refl /= poly0 polyseq0 //.
-
assert (H7: is_true (s`_n != 0))
 by (rewrite (last_nth Algebra.zero) H0 in H; auto).
rewrite size_cons_poly H0 /nilp size_poly_eq.
2:{  rewrite ?prednK; try Lia.lia. simpl. 
revert H7.
set d := s`_n. clearbody d.
apply contraNN.
intro.
rewrite mulIr_eq0 in H1; auto.
intros ? ? ?.
set (u := natmul _ _) in H1. 
assert (u > 0)%R by apply ltr0Sn.
clearbody u.
assert (x1 / u * u = x2 / u * u)%R. f_equal; auto.
rewrite -!mulrA in H3.
rewrite mulVf ?mulr1 in H3; auto.
apply lt0r_neq0; auto.
}
simpl.
apply (@eq_from_nth _ 0).
rewrite size_poly_eq //. 
simpl. 
rewrite coef_cons. simpl.
rewrite coefE ltnSn.
clear - H7; rewrite mulrn_eq0 /= mulf_eq0 negb_or H7 /= invr_neq0 //.
intros.
rewrite size_poly_eq in H1.
2: rewrite coef_cons /= coefE ltnSn mulrn_eq0 /= mulf_eq0 negb_or H7 /= invr_neq0 //.
rewrite coefE H1 coef_cons /= coefE H1 -mulrnAr -mulr_natr mulVr ?mulr1 //.
rewrite unitfE mulrn_eq0 /=  oner_eq0 //.
Qed.

Lemma derivable_oo_LRcontinuous_horner: forall P lo hi, @derivable_oo_LRcontinuous R _ (horner P) lo hi.
Proof.
intros.
split.
- intros ? ?. apply derivable_horner.
- exact/cvg_at_right_filter/continuous_horner.
- exact/cvg_at_left_filter/continuous_horner.
Qed.

Lemma Rintegral_poly: forall lo hi (lo_lt_hi: lo<hi)
  (P: polynomial (reals_Real__to__GRing_NzSemiRing R)),
eq
  (Rintegral (reverse_coercion (lebesgue_measure_lebesgue_measure__canonical__measure_function_Measure R) (@lebesgue_measure R))
     (mkset
        (fun x : Order.POrder.sort (reals_Real__to__Order_POrder R) =>
         is_true (in_mem x (mem (Interval (BSide true lo) (BSide false hi))))))
     (fun x : Measurable.sort (measurable_structure_g_sigma_algebraType__canonical__measurable_structure_Measurable measurable) =>
      horner P x))
 (GRing.add (horner (integ P) hi) (opp (horner (integ P) lo))).
Proof.
intros.
rewrite /Rintegral (@continuous_FTC2 R (horner P) (horner (integ P)) lo hi lo_lt_hi).
- reflexivity.
- apply derivable_within_continuous; intros ? ?; apply derivable_horner.
- apply derivable_oo_LRcontinuous_horner.
-  intros ? ?. 
rewrite -derivE. rewrite deriv_integ //.
Qed.

End R.

End Rewriting.

Import Rewriting.

(* end details *)

(* begin details:  Lemmas and tactics copied from matrix_util.v *)
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
rewrite H. rewrite nth_iota. Lia.lia. Lia.lia.
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
pose proof (ltn_ord i); Lia.lia.
Qed. 

Lemma index_enum_ord_enum: forall n: nat, 
   index_enum (fintype_ordinal__canonical__fintype_Finite n) = ord_enum n.
Proof.
intros.
unfold index_enum.
rewrite locked_withE.
rewrite Finite.enum.unlock.
simpl.
auto.
Qed.

Ltac is_ground_nat n := lazymatch n with O => idtac | S ?n' => is_ground_nat n' end.

Ltac compute_ord_enum n := 
  tryif is_ground_nat n then idtac 
      else  fail "compute_ord_enum: Need a ground term natural number, but got" n; 
  pattern (ord_enum n); 
  match goal with |- ?F _ => 
    let f := fresh "f" in set (f:=F);
      let c := constr:(ord_enum n) in let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with ssrbool.isT by apply eq_irrelevance; clear e | try (contradiction e; reflexivity)]);
     subst f
  end.

Ltac ord_enum_cases j :=
 lazymatch type of j with ordinal ?n => 
  pattern j; 
  apply ord_enum_cases;
  compute_ord_enum n
 end;
 repeat apply List.Forall_cons; try apply List.Forall_nil;
 clear j.

Ltac expand_bigop :=
 match goal with |- context [bigop.body _ (index_enum (fintype_ordinal__canonical__fintype_Finite ?n))] =>
 let B := fresh "B" in 
 set B := bigop.body _ _ _; pattern B; subst B; 
 lazymatch goal with |- ?b _ => set B := b end;
rewrite bigop.unlock index_enum_ord_enum;
 compute_ord_enum n;
 try rewrite ?/reducebig ?/foldr ?/applybig;
  repeat change (comp ?A ?B ?C) with (A (B C));
 cbv beta match;
 repeat change (nat_of_ord (@Ordinal _ ?a _)) with a;
 simpl nth;
 subst B; cbv beta
end.

(* end details *)

(** Now, on with the show.  The [Context] command parameterizes the whole development
  by any construction of the real numbers. *)

Section R.
Context {R : realType}.

(** This derivation follows Lecture 23 of _Afternotes on Numerical Analysis_ 
    by G. W. Stewart, SIAM Press, 1996.  Henceforth Stewart will be in Roman font
  _and your humble Editor will write in Italics.  -- Andrew Appel_. *)

(** _All the definitions and theorem-statements from Stewart are formalized
  in Rocq, but many of the theorems are Admitted, not proved.  However,
  all the theorems (below) for the specific application to Legendre polynomials
  are proved_. *)

(** ** Gaussian quadrature: The Setting *)

(** 1. The Gauss formula we will actually derive has the form,

      [  ∫_a ^b f(x) w(x) dx ≅ A_0 f(x_0) + A_1 f(x_1) + ⋯ + A_n f(x_n)   ]

  where w(x) is a weight function that is greater than zero on the interval [[a,b]].

   2. The incorporation of a weight function creates no complications in the theory.
  However, it makes our integrals, which are already too long, even more cumbersome.
 Since the interval [[a,b]] and the weight w(x) do not change, we will suppress them along with
 the variable of integration and write, 
    ∫ f =  [  ∫_a^b f(x) w(x) dx  ].
*)

Section Integral.
 Variable (a b : R).
 Variable Hab: a<b.
 Variable w: R -> R.
 Variable wpos: forall x, a <= x <= b -> w x > 0.
 Definition  intgal (f: R -> R) := 
            \int[lebesgue_measure]_(x in `[a,b]%classic) (f x * w x).
 Notation "∫" := intgal.
 
(** 3.  Regarded as an operator on functions, ∫  is linear.  That is, 

         ∫ α f = α ∫  f and ∫ (f + g) = ∫ f + ∫ g.  

     We will make extensive use of linearity in what follows. *)

 Lemma intgal_linear1: forall (α: R) (f:  R->R), ∫ (α \*: f) = α * ∫ f.
 Admitted.

 Lemma intgal_linear2: forall (f g: R -> R), ∫ (f \+ g) = ∫ f + ∫ g.
 Admitted.

(** ** Orthogonal polynomials *)

(** 4.  Two functions f and g are said to be _orthogonal_ if ∫  f g = 0.

  The term "orthogonal" derives from the fact that the integral ∫  f g can be regarded as an inner product
  of f and g.  Thus two polynomials are orthogonal if their inner product is zero, which is the usual definition
  of orthogonality in R^n. *)


 Definition orthogonal (f g: R -> R) := ∫ (f \* g) = 0.

(**  5. A sequence of  _orthogonal polynomials_ is a sequence {p_i},  i={0,1,...,∞} of polynomials
   with deg(p_i) = i such that      i ≠ j -> ∫ p_i p_j = 0.                         (23.1)

  _Editor's note: the [size] of a polynomial is the degree plus 1_.
*)

 Definition orthogonal_polynomials (p: nat -> {poly R}) : Prop := 
   (forall i, size (p i) = (i+1)%N) /\
   (forall i j: nat, i<>j ->  orthogonal (horner (p i)) (horner (p j))).

(** Since orthogality is not altered by multiplication by a nonzero constant, we
   may normalize the polynomial p_i so that the coefficient of x^i is one: i.e.,

   p_i(x) = x^i + a_{i,i-1}x^{i-1} + ⋯ + a_{i0}.

 Such a polynomial is said to be _monic_.  *)

Locate monic_pred.  (*  Constant mathcomp.algebra.poly.monic_pred *)
Print monic_pred.  (* = fun [R] (p : {poly R}) => lead_coef p == 1 *)

(** 6. Our immediate goal is to establish the existence of orthogonal polynomials.
  Although we could, in principle, determine the coefficients [a_{ij}] of [p_i] in the
  natural basis by using the orthogonality conditions (23.1), we get better results by
  expressing [p_{n+1}] in terms of lower-order orthogonal polynomals.  To do this
  we need the following general result.
    ------------------------------------------------------------------------------------------------
   Let \{p_i\}_{i=0}^∞ be a sequence of (monic) polynomials such that p_i is exactly of
   degree i. If

       q(x) = a_n x^n + a_{n-1} x^{n-1} + ⋯ + a_0                   (23.2)

  then q can be written uniquely in the form

       q = b_n p_n + b_{n-1} p_{n-1} + ⋯ + b_0 p_0.               (23.3)
*)

Section P.

  Variable  (p: nat -> {poly R}).
  Variable p_degree: forall i, size (p i) = (i+1)%N.
  Variable p_monic: forall i, monic_pred (p i).

  Lemma exist_orthogonal_polynomials:
      forall (n: nat) (q: {poly R}), 
        size q = (n+2)%nat ->
        { b: 'I_n.+1 -> R | 
          horner q = \big[add_fun/fun=>0]_(i<n.+1) (b i  \*: horner (p i))}.

(** 7.  In establishing this result, we may assume that the polynomials [ p_i ] are monic.
  The proof is by induction.  For n=0 we have,

      [ q(x) = a_0 = a_0 ⋅ 1 = a_0 p_0(x) ].

   Hence we must have [ b_0 = a_0 ].

     Now assume that q has the form (23.2).  Since [ p_n ] is the only polynomial in
    the sequence [ p_n, p_{n-1}, ⋯, p_0 ] that contains x^n and since [ p_n ] is monic, it follows
    that we must have [ b_n = a_n ].  Then the polynomial [ q-a_n p_n ] is of degree n-1.
    Hence by the induction hypothesis, it can be expressed uniquely in the form

           [  q - a_n p_n = b_{n-1} p_{n-1} + ⋯ + b_0 p_0 ],

    which establishes the result.
*)

Proof.
induction n.
Admitted.

(** 8.  A consequence of this result is the following.
            The polynomial [ p_{n+1} ] is orthogonal to any polynomial q of degree n or less.

      For from (23.3) it follows that

            [ ∫  p_{n+1} q = b_n ∫  p_{n+1} p_n + ⋯ + b_0 ∫  p_{n+2}p_0 = 0 ],

      the last equality following from the orthogonality of the polynomials [p_i].


       _(Note: [p_{n+2}p_0] sic in original, but surely p_{n+1}p_0 is meant.)_
*)

Lemma polySn_orthogonal_n: forall (n:nat) (q: {poly R}), 
            (size q <= n.+1)%nat ->
            orthogonal (horner (p n.+1)) (horner q).
Admitted.

End P.

(** 9. To establish the existence of orthogonal polynomials, we begin by computing
    the first two.  Since [p_0] is monic and of degree zero,

                [  p_0(x) ≡ 1.   ]

      Since [p_1] is monic and of degree one, it must have the form

                [   p_1(x) = x - α_1.    ]

    To determine [α_1], we use orthogonality:

           [    0 = ∫  p_1 p_0 = ∫  (x-α_1)⋅1  = ∫  x - α_1 ∫ 1.    ]

    Since the function 1 is positive in the interval of integration,  ∫ 1 > 0, and it 
    follows that

           [              α_1 = (∫ x) / (∫ 1).   ]

     10.  In general we will seek [ p_{n+1} ]  in the form

        [  p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1} - γ_{n+1} p_{n-2} - ⋯ . ]

      As in the construction of [p_1], we use orthogonality to determine the coefficients

      [ α_{n+1}, β_{n+1}, γ_{n+1}, ⋯ ]

          To determine [ α_{n+1} ], write

      [ 0 = ∫  p_{n+1} p_n = ∫  x p_n p_n - α_{n+1} ∫ p_n p_n - β_{n+1} ∫  p_{n-1} p_n - γ_{n+1} ∫ p_{n-2} p_n - ⋯ . ]

      By orthogonality, [ 0 = ∫ p_{n-1} p_n = ∫  p_{n-2} p_n = ⋯ ] .   Hence

            [  ∫  x p_n^2 - α_{n+1} ∫ p_n^2 = 0. ]

      Since [ ∫  p_n^2 > 0 ] , we may solve this equation to get

            [   α_{n+1} = ∫ x p_n^2  /  ∫  p_n^2. ]

      For [ β_{n+1} ], write

           [ 0 = ∫ p_{n+1} p_{n-1} = ∫ x p_n p_{n-1} - α_{n+1} ∫ p_n p_{n-1} - β_{n+1} ∫ p_{n-1} p_{n-1} - γ_{n+1} ∫ p_{n-2} p_{n-1} - ⋯ ] .

     Dropping terms that are zero because of orthogonality, we get

                   [   ∫ x p_n p_{n-1} - β_{n+1} ∫ p_{n-1}^2 = 0  ]
      or [ β_{n+1} = (∫ x p_n p_{n-1} ) / (∫ p_{n-1}^2).  ]

     11. The formulas for the remaining coefficients are similar to the formula for [ β_{k+1} ]; e.g.,

                [  γ_{n+1} = (∫  x p_n p_{n-2}) / (∫  p_{n-2}^2)  ].

        However, there is a surprise here.  The denominator [[sic]]   [ x p_n p_{n-2} ] can be written
        in the form [∫  x p_{n-2} p_n].  Since [x p_{n-2}] is of degree n-1 it is orthogonal to [p_n];
        i.e.,  [∫ x p_{n-2} p_{n-1 [sic]}   = 0].  Hence [γ_{k+1} = 0], and likewise the coefficients of
         [p_{n-3}, p_{n-4}, ⋯] are zero.

     12.  To summarize:
          The orthogonal polynomials can be generated by the following recurrence:

          -      [p_0 = 1,]
          -      [p_1 = x - α_1,]
          -      [p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1},               n=1,2,⋯,]
         where 

                 [ α_{n+1} = (∫  x p_n^2) / (∫ p_n^2)]   and [β_{n+1} =  (∫  x p_n p_{n-1}) / (∫  p_{n-1}^2)]. 

          The first two equations in the recurrence merely start things off.  The right-hand side
          of the third equation  contains three terms and for that reason is called the
          _three-term recurrence_ for the orthogonal polynomials.
*)

Fixpoint three_term_recurrence (n: nat) : {poly R} * {poly R} :=
   match n with
   | 0 => (1%:P, 0%:P)
(*   | 1 => let α1 :=  ∫ id /  ∫ (fun=>1) in ('X - α1%:P, 1%:P) *)
            (* the 1 case seems unnecessary, as it seems a special case of the S n' case. *)
   | S n' => let (pn', pn'') := three_term_recurrence n'
                   in let αn :=  ∫ (id \* (horner pn' \* horner pn')) / ∫(horner pn' \* horner pn')
                   in let βn := ∫ (id \* (horner pn' \* horner pn'')) / ∫(horner pn'' \* horner pn'')
                   in ('X * pn' - scale_poly αn pn' - scale_poly βn pn'', pn')
  end.

Definition ortho_p n := fst (three_term_recurrence n).

Lemma ortho_p_monic: forall n, monic_pred (ortho_p n).
Admitted.

Lemma ortho_p_orthogonal: orthogonal_polynomials ortho_p.
Admitted.

(** ** Zeros of orthogonal polynomials *)

(** 13.  It will turn out that the abscissas of our Gaussian quadrature formula will
        be the zeros of [p_{n+1}].  We will now show that 
        
         The zeros of [p_{n+1}] are real, simple, and lie in the interval [[a,b]].

     14.  Let [x_0, x_1, ⋯, x_k]  be the zeros of odd multiplicity of [p_{n+1}] in [[a,b];] i.e.,
         [x_0, x_1, ⋯, x_k] are the points at which [p_{n+1}] changes sign in [[a,b]].  If k=n, we are 
         through, since the [x_i] are the n+1 zeros of [p_{n+1}].

               Suppose then that k<n and consider the polynomial

                    [   q(x) = (x-x_0)(x-x_1)⋯(x-x_k)  ].

        Since deg(q) = k+1 < n+1, by orthogonality

                    [  ∫ p_{n+1} q = 0  ].

        On the other hand, [p_{n+1}(x) q(x)] cannot change sign on [[a,b]] -- each sign change
        in [p_{n+1}(x)] is cancelled by a corresponding sign change in q(x).  It follows that

                    [ ∫ p_{n+1} q <> 0 ],

         which is a contradiction.
*)

(** _Editor's note: The following predicate [roots_of_ortho_p] says that [roots] is 
     a list of n distinct values, all of which evaluate (under the polynomial) to zero, 
    which implies that they are simple roots_.*)

Record roots_of_ortho_p (n: nat) := {
  ROOTS_vals: n.-tuple R;
  ROOTS_zero: all (root (ortho_p n)) (tval ROOTS_vals);
  ROOTS_sorted: sorted Order.lt (tval ROOTS_vals);
  ROOTS_inrange: all (fun x => a <= x <= b) (tval ROOTS_vals)
}.
Arguments ROOTS_vals [n].
Arguments ROOTS_zero [n].
Arguments ROOTS_sorted [n].
Arguments ROOTS_inrange [n].

(** _Editor's note: the statement "14.  . . . are the n+1 zeros of [p_{n+1}]" implicitly claims that 
     there are at most n+1 zeros.  That is any zero of the polynomial is already in the roots list,
     which is explicitly an n.-tuple_.  Therefore: *)

Lemma roots_of_ortho_p_at_most: forall [n] (roots: roots_of_ortho_p n),
  forall x, root (ortho_p n) x -> x \in ROOTS_vals roots.
Admitted.

Lemma roots_of_ortho_p_unique (n: nat) : forall r r' : roots_of_ortho_p n, r=r'.
Proof.
(* begin details: partial proof of this lemma *)
move => r r'.
move :(roots_of_ortho_p_at_most r) => J1.
move :(roots_of_ortho_p_at_most r') => J2.
destruct r as [v1 Hz1 Hs1 Hin1].
destruct r' as [v2 Hz2 Hs2 Hin2].
simpl in J1, J2.
assert (forall x, x \in v1 <-> x \in v2). {
 intros; split; intro.
 + apply J2; move :Hz1; move  /allP => A1. apply A1; auto.
 + apply J1; move :Hz2; move /allP => A2; apply A2; auto.
}
assert (v1 = v2). {
clear - H Hs1 Hs2.
revert v1 v2 Hs1 Hs2 H; induction n; simpl; intros.
rewrite -boolp.eq_opE tuple0 eq_sym tuple0 //.
specialize (IHn (tuple_behead v1) (tuple_behead v2)).
rewrite -(tuple_rehead v1) -(tuple_rehead v2).
assert (thead v1 = thead v2). {
 pose proof (H (thead v1)).
 pose proof (H (thead v2)).
 admit.
}
rewrite H0.
rewrite IHn; auto.
rewrite -(tuple_rehead v1) in Hs1.
simpl in Hs1. apply path_sorted in Hs1; auto.
rewrite -(tuple_rehead v2) in Hs2.
simpl in Hs2. apply path_sorted in Hs2; auto.
intros.
admit.
}
subst v1.
f_equal; apply eq_irrelevance.
all: fail.
(* end details *)
Admitted.

(** _Editor's note:   Stewart's derivation talks about "THE roots" of the polynomial, as if
  they constructively exist.  Well, indeed they do exist, but_:
  - We want concretely presented roots in a simple form that we can calculate with, AND
  - Mathcomp-Analysis does not yet have proof that a polynomial can be factored into n roots, AND
  - Mathcomp-Analysis especially does not have a CONSTRUCTIVE such proof, AND
  - Even a constructive proof would not be useful unless it presented the roots in a simple
       form that we could calculate with.

  _Therefore we will do it slightly differently.  For the polynomials of interest, we will present
   the roots explicitly, and prove that they are indeed roots and are indeed distinct.  That
   is, we will present instances of the package [roots_of_ortho_p]_. *)

(** ** Gaussian quadrature *)

(** 15.  The Gaussian quadrature formula is obtained by constructing a Newton-Cotes
     formula on the zeros of the orthogonal polynomial [p_{n+1}].

     Let [x0, x_1, ⋯, x_n] be the zeros of the orthogonal polynomial [p_{n+1}] and set

              [ A_i = ∫  L_i,   i = 0, 1, ⋯, n, ]

     where [L_i ] is the ith Lagrange polynomial over [x_0, x_1, ⋯, x_n].  For any function f let

              [ G_n f = A_0 f(x_0) + A_1 f(x_1) + ⋯ + A_n f(x_n) ].

    Then  [ deg(f) ≤ 2n+1  ⇒  ∫  f = G_n f ].
*)

 Section Quadrature.
  Variable n : nat.
  Variable roots: roots_of_ortho_p n.
  Definition zeros_of_ortho_p := tval (ROOTS_vals roots).


  (** _Editor's note: When manipulating Lagrange polynomials in MathComp, we
     will need to prove that the numbers [x_0, x_1, ..., x_{n-1}] are distinct.  That is,
    MathComp's lagrangeE lemma requires injectivity over (fun i => x_i).  In this case, 
    the sequence x is the zeros_of_ortho_p, so we need to prove that function is injective.
    Unfortunately, lagrangeE stupidly requires injectivity over all the natural numbers,
    not just  over the [0..n-1] that index the roots list.  So we need this [extend_roots] 
    function to make that work_. *)
  Definition extend_roots  (i: nat) : R :=
     nth ((i+1)%:R+b) zeros_of_ortho_p i.

   Lemma extend_roots_injective: injective extend_roots.
   (* begin details: Proof. ... Qed. *)
   Proof.
    pose proof ROOTS_inrange roots.
    pose proof ROOTS_sorted roots.
    rewrite /extend_roots /zeros_of_ortho_p.
    set rl := tval (ROOTS_vals roots) in H,H0|-*. clearbody rl.
    simpl in H.
    assert (is_true (all (fun x => x <= b) rl)).
    eapply sub_all; [ | apply H].  intros ? ?. lra. clear H. rename H1 into H.
    intros i j H1.
    assert (is_true (i < size rl) \/ is_true (i >= size rl))%N by Lia.lia.
    assert (is_true (j < size rl) \/ is_true (j >= size rl))%N by Lia.lia.
    destruct H2 as [Hi|Hi];  destruct H3 as [Hj|Hj].
    -
     assert ((i < j)%N \/ i=j \/ (j<i)%N) by Lia.lia.
     destruct H2 as [? |[?|?]]; auto.
     rewrite <- (sorted_ij rl i j ((i + 1)%:R + b)%E ((j + 1)%:R + b)%E H0 Hi Hj) in H2.
     rewrite H1 in H2. apply lt_nsym in H2; auto; contradiction.
     rewrite <- (sorted_ij rl j i ((j + 1)%:R + b)%E ((i + 1)%:R + b)%E H0 Hj Hi) in H2.
     rewrite H1 in H2. apply lt_nsym in H2; auto; contradiction.
   - 
    pose proof (@all_nthP _  (fun x => x  <= b)  rl ((i + 1)%:R + b)%E). rewrite H in H2. inversion H2.
    apply H3 in Hi.
    rewrite H1 in Hi. clear H2 H3.
    rewrite nth_default in Hi; auto.
    assert ((j+1)%:R <= 0%:R) by lra.
    rewrite ler_nat in H2. Lia.lia.
   - 
    pose proof (@all_nthP _  (fun x => x  <= b)  rl ((j + 1)%:R + b)%E). rewrite H in H2. inversion H2.
    apply H3 in Hj.
    rewrite -H1 in Hj. clear H2 H3.
    rewrite nth_default in Hj; auto.
    assert ((i+1)%:R <= 0%:R) by lra.
    rewrite ler_nat in H2. Lia.lia.
   -
    rewrite ?nth_default in H1; auto.
    assert ((j+1)%:R == (i+1)%:R) by lra.
    rewrite eqr_nat in H2. Lia.lia.
  Qed.
(* end details *)

  Definition L : n.-tuple {poly_n R} := lagrange n extend_roots.
  Definition gauss_weight (i: 'I_n) := ∫ (horner (tnth L i)).

  Definition G (f: R->R) := \sum_i (gauss_weight i * (f (tnth zeros_of_ortho_p i))).

  (** 16.  To establish this result, first note that by construction the integration formula
    [G_n f] is exact for polynomials of degree less than or equal to n (see section 21.17).

         Now let deg(f) ≤ 2n+1.  Divide f by [p_{n+1}] to get

                 [ f = p_{n+1}q + r],      deg(q), deg(r) ≤ n.                             (23.4)

      Then

       - [G_n f = Σ_i A_i f(x_i)]
       -          = [Σ_i A_i(p_{n+1}(x_i)q(x_i) + r(x_i))]                       (by 23.4)
       -          = [Σ_i A_i r(x_i)]                                                 because p_{n+1}(x_i)=0
       -          = [G_n r]
       -          = [∫ r]                                                because [G_n] is exact for deg(r) ≤ n
       -          = [∫ (p_{n+1}q+r)]                            because [∫ p_{n+1}q = 0] for deg(q) ≤ n
       -          = ∫ f                                                (by 23.4).
      Quot erat demonstrandum.
  *)



  Lemma quadrature_exact_for: 
      forall f: {poly R}, (size f <= 2*n+2)%N -> ∫ (horner f) = G (horner f).
  Admitted.

(** 17. An important corollary of these results is that the coefficients [A_i] are positive.
       To see this note that

               [ L_i(x_j) = L_i^2(x_j) = if i=j then 1 else 0 ]. 

      Since [ L_i^2(x) ≥ 0] and [deg(L_i^2) = 2n],

             [  0 < ∫ L_i^2 = Σ_j A_i L_i^2(x_j) = A_i ].
*)
   Lemma gauss_weight_positive: forall i, gauss_weight i > 0.
   Admitted.

(** 18.  Since [ A_0 + A_1 + ⋯ + A_n = ∫ 1 ], no coefficient can be larger than 1.  Consequently,
     we cannot have a situation in which large coefficients create large intermediate results
      that suffer cancellation when they are added. *)

   Lemma gauss_weight_leq_1:  forall i, gauss_weight i <= 1.
   Admitted.

(** ** Error and convergence *)

(** 19.  Gaussian quadrature has error formulas similar to the ones for Newton-Cotes
    formulas.  Specifically

        [  ∫  f - G_n f =  ( f^(2n+2)(ξ) / (2n+2)!) ∫ p_{n+1}^2 ],

     where ξ ∈ [[a,b]]. *)
  Lemma quadrature_error: forall (f: R->R),
      exists ξ:R, a <= ξ <= b /\
       ∫ f - G f =  
       derive1n (2*n+2) f ξ /
        (factorial(2*n+2))%:R * ∫ (fun x => (horner (ortho_p(n.+1)) x)^2).
  Admitted.

(** 20. A consequence of the positivity of the coefficients A_i is that Gaussian
    quadrature converges for any continuous function; that is,

       [ f continuous ⇒ \lim_{n→∞} G_n f = ∫ f ].

    The proof -- it is a good exercise in elementary analysis -- is based on the Weierstrass
    approximation theorem, which says that for any continuous function f
    there is a sequence of polynomials that converges uniformly to f.
*)

  Lemma quadrature_converges:  forall (f: Real.sort R -> Real.sort R) (x: R),
    (forall x, continuous_at x f) -> limn (fun n => G f) = ∫ f.
  Abort.  (* Provable I'm sure, but it's not clear that we need it. *)


End Quadrature.
End Integral.
End R.
(** ** Examples *)

(** 21. Particular Gauss formulas arise from particular choices of the interval [[a,b]]
      and the weight function w(x).  The workhorse is Gauss-Legendre quadrature,
     in which [[a,b]] = [[-1,1]] and w(x)=1, so that the formula approximates the integral,

      [ ∫_{-1}^1 f(x) dx ].

    The corresponding orthogonal polynomials are called Legendre polynomials.
*)

(** _Editor's note:  Thus ends Stewart's presentation, except for paragraph 22 (Gauss-Laguerre
     quadrature), paragraph 23 (Gauss-Hermite quadrature), and paragraph 24 (there are many
     other such Gauss formulas suitable for special purposes). In the remainder of this file, 
     your humble editor permits himself to write in Roman font, not Italic. -- Andrew Appel_ *)

Module Legendre.
 Section R.
 Context {R : realType}.
 Definition lo : R := -1.
 Definition hi : R := 1.
 Lemma lo_lt_hi: (lo < hi)%R.    Proof. rewrite /lo /hi; lra. Qed.
 Definition w (x: R) : R := 1.
 Lemma w_positive: forall x, is_true (lo <= x <= hi) -> is_true (0 < w x).
 Proof. intros. rewrite /w. lra. Qed.
 
 Definition legendre (n: nat) : {poly R} :=  ortho_p lo hi w n.

 (** Presto! the Legendre polynomials have been defined.  But we want to put
  them into a much more usable form.  The remainder of this Module Legendre
  will instantiate the theory of orthogonal polynomials for this instance,
  then prove specific useful things (in this theory) about the Legendre polynomials of 
  degree up to 4. *)

 (** First, instantiate the notion of integral from lo to hi, from the general theory into the specific: *)

 Definition intgal := @intgal R lo hi w.
 Notation "∫" := intgal.

 Lemma intgal_eq: forall f,
       ∫ f = \int[lebesgue_measure]_(x in `[lo,hi]%classic) (f x).
(* begin details: Proof ... Qed. *)
 Proof. intros. rewrite /intgal /quadrature.intgal. f_equal. extensionality x. rewrite /w mulr1 //. Qed.
(* end details *)


(* begin details: A whole bunch of useful rewriting lemmas, to be used automatically in the rewrite tactic *)

Lemma intgal_linear1 : forall (α : R) (f : R -> R), ∫ (α \*: f) =  α * ∫ f.
Proof.
intros. rewrite /intgal intgal_linear1 -/intgal //. apply lo_lt_hi. 
Qed.

Lemma intgal_linear1' : forall (α : R) (f : {poly R}), ∫ (horner (polyC α * f)) =  α * ∫ (horner f).
Proof.
intros.
rewrite -intgal_linear1.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Lemma intgal_linear1'' : forall (α : R) (f : {poly R}), ∫ (horner ((- polyC α) * f)) =  (-α) * ∫ (horner f).
Proof.
intros.
rewrite -intgal_linear1.
f_equal. extensionality x. rewrite ?hornerE //.
Qed.

Lemma intgal_linearN : forall (f : R -> R), ∫ (opp_fun f) =  - ∫ f.
Proof.
intros.
transitivity ( ∫ ((fun=> -1)  \* f)).
f_equal; extensionality x; simpl; lra.
rewrite intgal_linear1; lra.
Qed.

Lemma intgal_linearN' : forall (f : {poly R}), ∫ (horner (-f)) =  - ∫ (horner f).
Proof.
intros.
rewrite -intgal_linearN.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Lemma intgal_linear2: forall  f g : R -> R,  ∫ (f \+ g) =  ∫ f +  ∫ g.
Proof.
intros. rewrite /intgal intgal_linear2 -/intgal //. apply lo_lt_hi. 
Qed.

Lemma intgal_linear2': forall  f g : {poly R},  ∫ (horner (f + g)) =  ∫ (horner f) +  ∫ (horner g).
Proof.
intros.
rewrite -intgal_linear2.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Definition intgal_linear := (intgal_linear1'', intgal_linear1', intgal_linear1, intgal_linearN, intgal_linearN', intgal_linear2', intgal_linear2).
(* end details *)

(** ** Packaging the Legendre polynials *)

(** We want to build packages, for each n up to degree 4, of:
  - LR_poly:  the conventional simplified form of the normalized Legendre polynomial
    (in contrast to ortho_p which produces a very large expression); 
  - LR_poly_eq: a proof that the legendre polynomial constructed by the three-term recurrence
     really is equal to LR_poly;
  - LR_roots: an instance of the roots_of_ortho_p package, which itself is an n.-tuple of roots
     along with proofs that they are strictly sorted and really evaluate to zero. 
*)

Record legendre_roots (n: nat) := {
   LR_poly: R -> R;
   LR_poly_eq: horner (legendre n) = LR_poly;
   LR_roots: roots_of_ortho_p lo hi w n
}.
Arguments LR_poly [n].
Arguments LR_poly_eq [n].
Arguments LR_roots [n].
Arguments Build_legendre_roots [n].

(** Similarly, we will build packages, for each n up to degree 4, of the gauss weights
    for the nth Legendre polynomial. *)
Record gauss_weights (n: nat) := {
   GW_legendre: legendre_roots n;
   GW_vals: n.-tuple R;
   GW_good: forall i, gauss_weight _ _ _ _ (LR_roots GW_legendre) i = tnth GW_vals i
}.
Arguments GW_legendre [n].
Arguments GW_vals [n].
Arguments GW_good [n].
Arguments Build_gauss_weights [n].

(** The following is a concrete implementation of the formula G_n(f) in Stewart's paragraph 15. *)

 Definition compute_G [n] (GW: gauss_weights n) (f: R -> R) :=
  \sum_i (tnth (GW_vals GW) i) * f (tnth (ROOTS_vals lo hi w n (LR_roots (GW_legendre GW))) i).

Lemma compute_G_eq: forall n (GW: gauss_weights n) f, 
  compute_G GW f = G lo hi w n (LR_roots (GW_legendre GW)) f.
(* begin details:  Proof.  ... Qed. *)
Proof.
intros.
rewrite /compute_G /G.
f_equal.
extensionality i.
f_equal; f_equal; symmetry; apply GW_good.
Qed.
(* end details *)

(** Now we instantiate the general quadrature_error theorem for the instance of
   Legendre polynomials *)

 Lemma legendre_quadrature_error: forall [n: nat] (GW: gauss_weights n) (f: R -> R),
      exists ξ:R, lo <= ξ <= hi /\
       ∫ f - compute_G GW f =  derive1n (2*n+2) f ξ / 
       (factorial(2*n+2))%:R * ∫ (fun x => (horner (legendre n.+1) x)^2).
Proof.
intros.
rewrite compute_G_eq /intgal.
apply quadrature_error. apply lo_lt_hi. apply w_positive.
Qed.

(* begin details:  A bunch of useful rewriting rules *)

Definition r_integral:
 forall P : {poly R}, \int[lebesgue_measure]_(x in `[lo, hi]) P.[x] = (integ P).[hi] - (integ P).[lo]
 := Rintegral_poly _ _ lo_lt_hi.

Lemma intgal_X: ∫ (horner 'X) = 0.
Proof.
rewrite polyX' intgal_eq  r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_0: ∫ (horner 0%:P) = 0.
Proof.
rewrite polyC0 intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
rewrite size_poly0.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_1: ∫ (horner 1%:P) = 2.
Proof.
rewrite polyC1 intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly size_polyC oner_neq0 /= polyseq1.
repeat expand_bigop.
field; auto.
Qed.

Lemma intgal_C: forall c,  ∫ (horner c%:P) = 2*c.
Proof.
intros. rewrite -(mulr1 c%:P) ?intgal_linear intgal_1 mulrC //.
Qed.

Lemma intgal_X2: ∫ (horner ('X * 'X)) = 2/3.
Proof.
rewrite polyX2' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X3: ∫ (horner ('X * ('X * 'X))) = 0.
Proof.
rewrite polyX3' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X4: ∫ (horner ('X * ('X * ('X * 'X)))) = 2/5.
Proof.
rewrite polyX4' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X5:  ∫ (horner ('X * ('X * ('X * ('X * 'X))))) = 0.
Proof.
rewrite polyX5' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X6:  ∫ (horner ('X * ('X * ('X * ('X * ('X * 'X)))))) = 2/7.
Proof.
rewrite polyX6' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X7:  ∫ (horner ('X * ('X * ('X * ('X * ('X * ('X * 'X))))))) = 0.
Proof.
rewrite polyX7' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Definition r_intgal := (intgal_linear, intgal_0, intgal_1, intgal_C, intgal_X, intgal_X2, 
                      intgal_X3, intgal_X4, intgal_X5, intgal_X6, intgal_X7).

Lemma pull_left1: forall u: {poly R}, 'X * u = u * 'X.
Proof. intros. ring. Qed.

Lemma pull_left2: forall u v: {poly R}, 'X * (u * v) = u * ('X * v).
Proof. intros. ring. Qed.

Definition pull_left (u: {poly R}) := (pull_left1 u, pull_left2 u).


Lemma pull_left1': forall u: R, 'X * (polyC u) = (polyC u) * 'X.
Proof. intros. ring. Qed.

Lemma pull_left2': forall (u: R) (v: {poly R}), 'X * (polyC u * v) = polyC u * ('X * v).
Proof. intros. ring. Qed.

Lemma scale_polyC': forall x y: R, scale_poly x (polyC y) = polyC (x*y).
Proof.
intros.
rewrite scale_polyE mul_polyC' //.
Qed.

Lemma mulrA'X: forall a b c: {poly R}, a * b * c = a * (b * c).
Proof.
symmetry. apply mulrA.
Qed.

Definition norm_poly := (mulrA'X, pull_left1', pull_left2', scale_1poly, scale_0poly, scale_polyC', r_ring, r_intgal).

Definition mulrD {R: pzRingType} := (@mulrDr R, @mulrDl R, @mulrN R, @mulNr R, @opprK R).

Lemma hornerD'': forall (a b: {poly R}), @horner R (a-b) = horner a \- horner b.
Proof. intros. extensionality x. rewrite hornerD. rewrite hornerN. reflexivity.
Qed.

Lemma eq_opI: forall {s} (A B: Equality.sort s), A=B -> is_true (eq_op A B).
Proof.
intros.
subst.
apply eq_refl.
Qed.

Lemma sub_mul2: forall (x :R), -x-x = -(2*x).
Proof. intros. lra. Qed.

Lemma opp_sub: forall {s: zmodType} (x y:s), -x-y = -(x+y).
Proof. intros.
pose proof (opprB x (-y)).
rewrite opprK in H. rewrite H. apply addrC.
Qed.

Ltac do_one_integral u := 
let i := fresh "i" in let g := fresh "g" in 
set i := ∫ _;  pattern i; match goal with |- ?G _ => set g := G end; subst i;
rewrite ?mulrD -?mulrA ?(pull_left u) ?r_intgal ?r_ring; subst g; cbv beta; rewrite ?r_ring ?scale_0poly ?r_ring.

(* end details *)

(** *** The degree-0 Legendre polynomial *)

(** First, prove that the 0-th Legendre polynomial, as constructed by the [ortho_p]
    recurrence, is the constant function 1.  This is rather trivial, but when we get to n=3
    and n=4 it won't be so easy. *)
Lemma Legendre_poly_0: horner (legendre 0) = fun x: R => 1.
Proof.
rewrite /legendre /ortho_p /= ?scale_polyE ?r_intgal ?r_horner ?r_ring //.
Qed.

(** Second, package up the [legendre_roots] structure for degree 0 *)
Definition legendre_roots_0 : legendre_roots 0.
  apply (Build_legendre_roots _ Legendre_poly_0).
  apply (Build_roots_of_ortho_p lo hi _ 0 (@Tuple 0 _ nil isT)).
- constructor.
- reflexivity.
- reflexivity.
Defined.

(** *** The degree-1 Legendre polynomial *)

Lemma Legendre_poly_1: horner (legendre 1) =  fun x:R => x.
Proof.
rewrite /legendre /ortho_p /= hornerX_i -?hornerM' ?mulr1 ?mul1r ?mulr0 ?mul0r -/intgal ?r_intgal ?scale_polyE.
f_equal; ring.
Qed.

Definition legendre_roots_1: legendre_roots 1.
  apply (Build_legendre_roots _ Legendre_poly_1).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 1 _ [:: 0] isT)).
-
simpl; red; rewrite ?Bool.andb_true_iff; repeat split;
rewrite /root -/(legendre _).
rewrite Legendre_poly_1.
apply eq_refl.
-
reflexivity.
-
simpl; red; rewrite /lo /hi ?Bool.andb_true_iff; repeat split;  lra.
Defined.


(** *** The degree-2 Legendre polynomial *)

Lemma Legendre_poly_2: horner (legendre 2) =   fun x :R => x*x - 1/3.
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring.
rewrite -/intgal ?r_intgal ?r_ring ?scale_0poly ?scale_1poly ?r_ring.
rewrite ?r_intgal ?r_ring scale_0poly ?r_ring scale_polyE mulr1.
extensionality x.
rewrite ?hornerE.
field; auto.
Qed.

(** Now we start to need square roots.  It could be worse: above degree 4, the roots
  don't even have closed-form expressions with square roots.  Fortunately, we don't 
  need to go above degree 4. *)
Notation sqrt := (@Num.sqrt R).

Lemma sqrt_exists: forall (x: R), 0 < x -> 
 in_mem (sqrt x) (mem unit).
Proof.
intros.
rewrite -sqrtr_gt0 in H.
apply unitf_gt0; auto.
Qed.

Lemma sqr_sqrt: forall x:R, 0 <= x -> (sqrt x * sqrt x) = x.
Proof.
intros.
apply sqr_sqrtr; auto.
Qed.

(** The roots of the degree-2 Legendre polynomial are  -1/sqrt(3) and +1/sqrt(3).  *)
Definition legendre_roots_2: legendre_roots 2.
  apply (Build_legendre_roots _ Legendre_poly_2).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 2 _ [:: -1/(sqrt 3); 1/(sqrt 3)]  isT)).
-
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_2.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI.
 + rewrite ?mulN1r ?mulrNN -?invrM; [ | apply sqrt_exists; lra .. ].
    rewrite sqr_sqrt; lra.
 + rewrite mulf_div mulr1 sqr_sqrt; lra.
-
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split.
  assert (0 <  1 / sqrt 3)
  by (apply divr_gt0; rewrite ?sqrtr_gt0; lra).
  lra.
-  
  assert (0 <  1 / sqrt 3) by (apply divr_gt0; rewrite ?sqrtr_gt0; lra).
  assert (sqrt 3 > 1) by (rewrite -{1}sqrtr1; rewrite ltr_sqrt; lra).
  assert (1 / sqrt 3 < 1) by (rewrite mul1r invf_lt1; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Defined.


(** *** The degree-3 Legendre polynomial *)

Lemma Legendre_poly_3: horner (legendre 3) =  fun x :R => x*x*x - (3/5)*x.
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring -/intgal ?norm_poly ?mulrD ?norm_poly.
extensionality x.
rewrite /= ?hornerE /=.
field; auto.
Qed.

(** The roots of the degree-2 Legendre polynomial are  -sqrt(3/5), 0, and +sqrt(3/5).  *)
Definition legendre_roots_3: legendre_roots 3.
  apply (Build_legendre_roots _ Legendre_poly_3).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 3 _ [:: -(sqrt (3/5)); 0; (sqrt (3/5))]  isT)).
-
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_3.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI;
  rewrite /tnth /= ?mulrNN ?sqr_sqrt; lra.
-
  assert (0 <  sqrt (3/5)) by (rewrite sqrtr_gt0; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; lra.
-
  assert (0 < sqrt (3/5)) by  (rewrite ?sqrtr_gt0; lra).
  assert (sqrt(3/5) < 1) by (rewrite -{3}sqrtr1 ltr_sqrt; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Defined.

(** *** The degree-4 Legendre polynomial *)


Lemma Legendre_poly_4: horner (legendre 4) =  fun x :R => x*x*x*x - (30/35)*(x*x) + (3/35).
(* These proofs are getting longer and longer! *)
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring.
match goal with |- _ = ?B => set RHS := B end.
rewrite -/intgal ?r_intgal ?r_ring ?scale_0poly ?scale_1poly ?r_ring.
rewrite ?r_intgal ?r_ring ?scale_0poly ?r_ring scale_polyE ?r_ring.
set u := ( _ / _ / _)%:P.
rewrite (invf_div 2 3).
set v := 3/2.
rewrite ?scale_polyE.
repeat do_one_integral u.
subst v.
set a := 2/5 - _.
set b := inv _ * _.
set c := inv _ * _.
rewrite ?norm_poly.
rewrite ?mulrD ?norm_poly.
extensionality x.
rewrite ?hornerE /=.
subst u a b c  RHS.
simpl.
field; auto.
Qed.

Definition legendre_roots_val := 
  @Tuple 4 _ 
    [:: -(sqrt ((3 + 2 * sqrt(6/5))/7)); -(sqrt ((3 - 2 * sqrt(6/5))/7)); 
         (sqrt ((3 - 2 * sqrt(6/5))/7)); (sqrt ((3 + 2 * sqrt(6/5))/7)) ] isT.

Lemma legendre_roots_4a: 
   is_true (all (root (ortho_p lo hi w 4)) (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
simpl.
assert (H3: is_true (0 <= (3 - 2 * sqrt (6 / 5)) / 7)). {
  assert (3/(2) >= sqrt (6/5))%R; [ | nra].
  assert (sqrt (9/4) = 3/2).
  transitivity (sqrt ((3/2) * (3/2))). f_equal; lra.
  rewrite sqrtrM ?sqr_sqrt; lra.
  rewrite -H ler_sqrt; lra.
}
assert (H4: 0 < sqrt (6/5)) by (rewrite sqrtr_gt0; lra).
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_4.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H,H3,H4|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H4,H3,H|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H,H3,H4|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H3,H4,H|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
Qed.
(* end details *)

Lemma legendre_roots_4b:
  is_true (sorted <%R (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
assert (H4: 0 < sqrt (6/5)) by (rewrite sqrtr_gt0; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split.
+ rewrite lterNl opprK ltr_sqrt; lra.
+
match goal with |-  (- ?A < _) = true => assert (0 < A); [ | lra] end.
rewrite sqrtr_gt0.
assert (sqrt (6/5) <= 6/5); [ | lra].
assert (6/5 = sqrt ((6/5)*(6/5))). 
rewrite sqrtrM ?sqr_sqrt ; lra.
rewrite H.
rewrite ler_sqrt.
rewrite -H. lra. lra.
+
rewrite ltr_sqrt; lra.
Qed.
(* end details *)

Lemma legendre_roots_4c:
 is_true   (all (fun x : Order.Preorder.sort (reals_Real__to__Order_Preorder R) => lo <= x <= hi)
     (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
assert (1 < sqrt (6/5)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (sqrt(6/5)<6/5) by (rewrite -{2}(sqr_sqrt (6/5)); nra).
assert (0 < sqrt((3%R + (2 * Num.ExtraDef.sqrtr (6 / 5))%R)%E / 7))
   by (rewrite sqrtr_gt0; lra).
assert (sqrt((3%R + (2 * Num.ExtraDef.sqrtr (6 / 5))%R)%E / 7) < 1) 
  by ( rewrite -{6}sqrtr1 ltr_sqrt; lra).
assert (0 < sqrt((3 - (2 * Num.ExtraDef.sqrtr (6 / 5))) / 7))
   by (rewrite sqrtr_gt0; lra).
assert (sqrt((3 - (2 * Num.ExtraDef.sqrtr (6 / 5))) / 7) < 1) 
  by ( rewrite -{6}sqrtr1 ltr_sqrt; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Qed.
(* end details *)

Definition legendre_roots_4: legendre_roots 4.
  apply (Build_legendre_roots _ Legendre_poly_4).
 apply (Build_roots_of_ortho_p lo hi _ _  legendre_roots_val
   legendre_roots_4a legendre_roots_4b legendre_roots_4c).
Defined. 

(** ** Building the Gauss weights of Legendre polynomials *)

(** *** Gauss weights of degree-0 Legendre polynomials *)

Definition gauss_weights_0 : gauss_weights 0.
 apply (Build_gauss_weights legendre_roots_0 [::]).
 intros.
 ord_enum_cases i.
  (* no cases *)
 Defined.


(** *** Gauss weights of degree-1 Legendre polynomials *)
(**  The Gauss weights of degree 1 is just the singleton 2. *)
Lemma gauss_weight_1_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_1) (@Ordinal 1 0 isT) = 2.
Proof.
rewrite /gauss_weight /legendre_roots_1 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
 cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner invr1 ?r_lift.
  rewrite (_: (fun=>1) = horner (polyC 1)).
  2: extensionality x; rewrite hornerE //.
  rewrite -/intgal intgal_C mulr1 //.
Qed.

Definition gauss_weights_1 : gauss_weights 1.
 apply (Build_gauss_weights legendre_roots_1 [:: 2 ]).
 intros. 
 ord_enum_cases i.
 - (* case 0 *) apply gauss_weight_1_0.
Defined.


(** *** Gauss weights of degree-2 Legendre polynomials *)
(**  The Gauss weights of degree 2 are the sequence 1,1. *)
Lemma gauss_weight_2_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 0 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
rewrite /extend_roots /= ?r_horner ?r_ring ?r_lift.
set s3 := Num.sqrt 3. simpl in s3.
rewrite -(div1r s3) mulN1r -/intgal.
transitivity ( ∫ (horner ('X * -(s3/2)%:P + (1/2)%:P))).
-
f_equal.
extensionality x.
simpl.
rewrite ?hornerE.
field.
assert (0 < s3); rewrite ?sqrtr_gt0; lra.
-
transitivity ( ∫ (horner (-(s3/2))%:P \* (horner 'X) \+ horner (1/2)%:P)).
f_equal; extensionality x; rewrite ?hornerE /= ?hornerE;  lra.
rewrite -hornerM' ?r_intgal ?r_ring.
lra.
Qed.

Lemma gauss_weight_2_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 1 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta.
expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift
        -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''
        -hornerM' ?r_intgal ?r_ring.
field.
assert (0 < sqrt 3);  rewrite ?sqrtr_gt0; lra.
Qed.

Definition gauss_weights_2 : gauss_weights 2.
 apply (Build_gauss_weights legendre_roots_2 [:: 1; 1]).
Proof.
intros.
 ord_enum_cases i.
 - (* case 0 *) apply gauss_weight_2_0.
 - (* case 1 *) apply gauss_weight_2_1.
Defined.

(** *** Gauss weights of degree-3 Legendre polynomials *)
(**  The Gauss weights of degree 3 are 5/9, 8/9, 5/9. *)

Lemma gauss_weight_3_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 0 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift
  -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
rewrite (_: - s3 - s3 = -(s3 * 2) :> R); [ | lra].
rewrite mulrNN (mulrA s3) {1 2}/s3.
rewrite sqr_sqrt ; [ | lra].
rewrite (mulrC _ 2) mulrA.
do_one_integral (s3%:P).
field; auto.
Qed.

Lemma gauss_weight_3_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 1 isT) = 8/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
rewrite opprK mulrN.
rewrite sqr_sqrt; [ | lra].
do_one_integral (- s3)%:P.
do_one_integral s3%:P.
rewrite mulNr.
rewrite (mulrC 2 s3).
rewrite (mulrA s3).
rewrite sqr_sqrt ; [ | lra].
field; auto.
Qed.

Lemma gauss_weight_3_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 2 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
set u := _ - _. replace u with ((s3 * 2))%R by (subst u; lra). clear u.
rewrite -(mulrA s3).
rewrite (mulrC 2 s3) ?mulrA.
rewrite sqr_sqrt ; [ | lra].
do_one_integral (- s3)%:P.
field; auto.
Qed.

Definition gauss_weights_3 : gauss_weights 3.
 apply (Build_gauss_weights legendre_roots_3 [:: 5/9; 8/9; 5/9]).
Proof.
intros.
ord_enum_cases i.
apply gauss_weight_3_0.
apply gauss_weight_3_1.
apply gauss_weight_3_2.
Defined.

(** *** Gauss weights of degree-4 Legendre polynomials *)
(**  The Gauss weights of degree 3 are 1/2-sqrt(5/6)/6, 1/2+sqrt(5/6)/6, 1/2+sqrt(5/6)/6, 1/2-sqrt(5/6)/6. *)

Lemma add_mul2: forall (x :R), x+x = 2*x.
Proof. intros. lra. Qed.

Lemma add_mul3: forall (x :R), x+(x+x) = 3*x.
Proof. intros. lra. Qed.

Lemma gauss_weight_4_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 0 isT) = 
       1/2 - Num.sqrt(5/6)/6.
(* begin details: Proof.  ... very long and tedious ... Qed. *)
Proof.
set RHS := _ - _.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD'' ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite opprK.
set a := inv _.
set b := Num.sqrt _.
set c := Num.sqrt _. simpl in a,b,c.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
set u := - b - b; replace u with (-2*b) by (subst u; lra); clear u.
rewrite -?hornerM'.
rewrite r_intgal.
rewrite ?(@mulrD {poly _}) -?mulrA.
rewrite ?(pull_left (-c%:P)) ?r_intgal ?r_ring.
rewrite ?(pull_left (b%:P)) ?r_intgal ?r_ring.
rewrite ?(pull_left (c%:P)) ?r_intgal ?r_ring.
transitivity (a * ((- c * (2 / 3))%R + (- b * (2 / 3))%R + ((b * (2 / 3))%R + (- (b * b) * (2 * - c))%R))%E); [ ring | ].
rewrite sqr_sqrt; try lra. 
rewrite addrA. 
rewrite (mulNr b).
rewrite ?mulrDr ?mulrDl.
rewrite ?mulNr ?mulrN.
set u := a * (b * _).
rewrite add_mul2.
rewrite ?mul1r.
rewrite add_mul3.
clearbody u. simpl in u.
rewrite add_mul2.
rewrite add_mul2 ?mulrN opprK.
set d := - (_ * _).
simpl  in d.
rewrite -(addrA d).
rewrite (addrC (opp u)).
replace (d + _) with d by lra.
clear u.
subst d.
rewrite !mulrA.
rewrite (mulrC (_ * _) c).
rewrite !mulrA.
rewrite (mulrC c a).
rewrite -(mulrA _ 2 (inv 3)).
rewrite -(mulrN (a*c)).
rewrite -(mulrA (a*c)).
rewrite -mulrDr.
set (d := _ * 2).
subst a c.
set a := Num.sqrt _.
set c := Num.sqrt _.
simpl in *.
rewrite add_mul2 ?mulrN ?mulNr.
rewrite mulrA.
set e := _ * (- a - c).
replace e with (a*a - c*c) by (subst e; nra).
clear e.
rewrite !sqr_sqrt; try (subst a c; lra).
clear c.
clear b.
set u := _ / 7 - _ / 7.
replace u with ((4/7)*s3) by (subst u; nra). clear u.
rewrite ?mulrA.
rewrite invrN mulNr.
rewrite invrM; try (rewrite unitfE; lra).
2: rewrite unitfE; assert (0 < a) by (rewrite sqrtr_gt0; lra);  lra.
rewrite (mulrC _ a).
rewrite mulrA.
rewrite mulfV.
2: assert (0 < a) by (rewrite sqrtr_gt0; lra);  lra.
clear a.
subst d.
rewrite -(mulNr (2*s3) (inv 7)).
rewrite -mulrDl.
rewrite r_ring.
rewrite addrC.
rewrite -(mulrA _ s3).
rewrite (mulrC _ (s3 * _)).
rewrite (mulrA (s3 * 2)).
rewrite invrM; [  |  rewrite unitfE; lra ..].
rewrite invrK.
rewrite mulNr.
rewrite (mulrC 7).
rewrite -(mulrA _ 7).
rewrite (mulrC 7).
rewrite (mulrDl _ _ 7).
rewrite -(mulrA _ (inv 7)).
rewrite (mulrC (inv 7) 2).
rewrite -(mulrA _ (2/7)).
rewrite -(mulrA _ (inv 7) 7).
rewrite mulVr;  [ | rewrite unitfE; lra ].
rewrite mulr1.
rewrite -(mulrA s3).
rewrite invrM;   [ | rewrite unitfE; lra ..].
rewrite -(mulrA _ (inv s3)).
rewrite (mulrDl _ _ 2).
rewrite addrC.
rewrite addrA.
set e := _ + (3*2).
rewrite (mulrDr (inv _)).
rewrite  mulNr mulrN.
rewrite (mulrC 2 s3) -(mulrA s3).
rewrite (mulrA _ s3).
rewrite mulVr;  [ | rewrite unitfE; lra ].
rewrite mul1r.
rewrite mulrC.
rewrite (mulrC _ e).
subst e.
rewrite (mulrDl _ _ (inv (2*4))).
rewrite !mulNr.
rewrite (addrC (- (_ * 7))).
rewrite (mulrC _ (inv(2*4))).
rewrite mulrA.
rewrite opprB.
subst RHS.
rewrite -(invf_div 6 5).
rewrite sqrtrV; [ | lra].
change (Num.sqrt _) with s3.
nra.
Qed.
(* end details *)

Lemma gauss_weight_4_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 1 isT) = 
       1/2 + Num.sqrt(5/6)/6.
(* begin details: Proof.  ... very long and tedious ... Qed. *)
Proof.
set RHS := _ + _. simpl in RHS.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite -/intgal ?r_ring /extend_roots /= ?r_ring. 
set s3 := Num.sqrt (6/5). simpl in s3.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite polyCN opprK.
rewrite ?hornerE /=.
set a := inv _.
rewrite ?mulrD.
rewrite -?mulrA.
rewrite ?r_intgal ?r_ring.
rewrite ?(pull_left (polyC _)) ?r_intgal ?r_ring.
replace a with ( (((- c)%R + b)%E * ((- c - c) * (- c - b)))^-1 : R) by (subst a; f_equal; ring).
clear a; set a := inv _.
transitivity (a * ((- b * (2 / 3))%R + (- c * (2 / 3))%R + ((b * (2 / 3))%R + (b * (- c * (2 * - b)))%R))%E); [ ring |].
simpl in a.
unfold b,c in a.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
rewrite mulrA ?mulrN ?mulNr ?mulrN.
rewrite -(mulrA c 2). rewrite (mulrA b c).
rewrite opprK.
rewrite (mulrC (b*c)) -(mulrA 2 b) (mulrA b b) sqr_sqrt; try lra.
rewrite ?(mulrDr a) ?mulrN.
set u := (a * (b * _)).
rewrite -(mulrC c).
rewrite !(mulrA _ _ (_ 7)).
rewrite (mulrDr c).
rewrite (mulrDr 2).
rewrite (mulrDr a).
rewrite !(mulrC 2 (c * _)).
rewrite -(mulrA c 3 2).
rewrite -(mulrA c (2 * s3)).
rewrite !(mulrA a c).
set (v := a*c).
match goal with |- (?x + ?z) + (?y + ?A) = RHS =>  transitivity (z + A) end.
ring.
clear u.
subst v a.
clear b.
subst c.
set c := (3 - 2*s3)/7.
set b := (3 + 2*s3)/7.
rewrite sub_mul2 ?mulNr ?mulrN.
rewrite opp_sub ?mulrN ?mulnR ?opprK ?mulrN.
rewrite ?mulrDr ?mulNr ?mulrN.
rewrite ?mulr1.
rewrite -?(mulrA 2).
rewrite sqr_sqrt; auto.
rewrite -sqrtrM; [ | subst c; lra].
rewrite ?(addrC (- _)).
rewrite ?(mulrA _ 2) ?(mulrC _ 2).
rewrite -?(mulrA 2 _ c).
rewrite ?(mulrDl _ _ c).
rewrite ?(mulrDr 2) ?mulrN ?mulNr ?mulrN.
rewrite ?(mulrDl (2*_) _ (Num.sqrt _)) ?mul1r.
set bcc := Num.sqrt b * c.
set ccc := Num.sqrt c * c.
rewrite -(mulrA 2 (Num.sqrt b) (Num.sqrt (c*b))).
rewrite -sqrtrM; [ | subst b; lra].
rewrite mulNr.
rewrite -(mulrA 2 (Num.sqrt c) (Num.sqrt (c*b))).
rewrite -sqrtrM; [ | subst c; lra].
rewrite (mulrA c c).
rewrite (mulrC (c*c)).
rewrite (@sqrtrM _ b (c*c)); [ | subst b; lra].
rewrite (@sqrtrM _ c c); auto.
rewrite sqr_sqrt; auto.
rewrite (mulrC b (c*b)) -(mulrA c b b).
rewrite (@sqrtrM _ c (b*b)); auto.
rewrite (@sqrtrM _ b b); [ | subst b; lra].
rewrite sqr_sqrt; [ | subst b; lra].
fold bcc.
set cbb := Num.sqrt c * b.
rewrite add_mul2.
rewrite add_mul2.
set u := (_ - _)+ (_ - _).
replace u with (2*(cbb-ccc)) by (subst u; lra).
clear u.
assert (cbb - ccc \is a unit). {
 rewrite unitfE.
 subst cbb ccc. clear bcc. rewrite -mulrBr.
apply mulf_neq0.
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H2. lra.
subst b c. lra.
}
rewrite invrM; [  |  rewrite unitfE; lra | auto ].
set u := (cbb-ccc).
unfold cbb, ccc in u.
revert u.
rewrite -mulrBr. simpl.
rewrite invrM; [ | rewrite unitfE ..].
2:{ 
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H3; lra.
}
2: subst b c; lra.
rewrite !mulrA.
rewrite (mulrC _ (inv 2)).
rewrite !mulrA.
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite (mulrC _ 3).
rewrite (mulrC _ (inv 3)).
rewrite (mulrC _ (inv 2)).
rewrite (mulrC _ s3).
rewrite  -!mulrA.
rewrite mulVf.
2: {
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H3; lra. }
rewrite mulr1.
clear ccc cbb bcc H2. 
rewrite !mulrA.
subst b c.
revert RHS.
rewrite -(invrK (5/6)).
rewrite sqrtrV; [ |  lra].
rewrite invf_div.
change (Num.sqrt _) with s3.
intro.
rewrite (mulrC 3).
rewrite !(mulrC _ (inv 7)).
rewrite -?(mulrBr (inv 7)).
set u := (_ + _)- (_ - _).
replace u with (4 * s3)%R by (subst u; lra).
clear u.
rewrite mulrDr.
rewrite invrM; [ | rewrite unitfE; lra .. ].
rewrite -(mulrA s3 (inv 2)).
rewrite invrK.
rewrite mulVf; [ | lra]. rewrite mulr1.
rewrite (mulrC _ 7).
rewrite -(mulrA _ _ 3).
rewrite (mulrA (inv 7) 7).
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite (mulrC (s3 * 2)).
rewrite -(mulrA _ _ (s3*2)).
rewrite (mulrA _ 7).
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite invrM; [ | rewrite unitfE; lra ..].
rewrite (mulrC _ (inv 4)).
rewrite -(mulrA _ (inv s3) (_ * 2)).
rewrite (mulrC (inv 4) (_ * (_ * 2))).
rewrite mulrA.
rewrite mulVr.
2: rewrite unitfE; lra.
rewrite mul1r.
rewrite (addrC _ (2/4)).
rewrite -addrA.
subst RHS.
f_equal.
lra.
lra.
Qed.
(* end details *)

Lemma gauss_weight_4_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 2 isT) = 
       1/2 + Num.sqrt(5/6)/6.
(* begin details: make use of the gauss_weight_4_1 lemma, with appropriate adaptation *)
Proof.
rewrite -gauss_weight_4_1.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; apply lo_lt_hi .. ].
cbv zeta; repeat expand_bigop.
  rewrite /extend_roots /= ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite -/intgal.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?hornerE /= ?opprK ?r_ring.
set a := inv _.
rewrite ?opp_sub ?mulrN ?mulNr ?opprK.
set a' := inv _.
assert (a'=-a). subst a a'. rewrite -invrN. f_equal. ring.
rewrite H; clear H a'.
rewrite ?polyCN ?opprK ?add_mul2.
rewrite -?mulrA.
rewrite ?r_intgal.
rewrite ?mulrD ?mul_polyC' -?mulrA.
rewrite ?(pull_left (polyC _)) ?r_intgal ?r_ring.
ring.
Qed.
(* end details *)

Lemma gauss_weight_4_3: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 3 isT) = 
       1/2 - Num.sqrt(5/6)/6.
(* begin details: make use of the gauss_weight_4_0 lemma, with appropriate adaptation *)
Proof.
rewrite -gauss_weight_4_0.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; apply lo_lt_hi .. ].
cbv zeta; repeat expand_bigop.
  rewrite /extend_roots /=  ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite ?opprK.
rewrite -/intgal ?r_intgal.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?hornerE /= ?polyCN ?opprK ?r_ring.
set a := inv _.
set a' := inv _.
assert (a'=-a). subst a a'. rewrite -invrN. f_equal. ring.
rewrite H; clear H a'.
rewrite ?mulrD -?mulrA ?(pull_left (polyC _)) ?r_intgal ?r_ring.
ring.
Qed.
(* end details *)

Definition gauss_weights_4 : gauss_weights 4.
 apply (Build_gauss_weights legendre_roots_4
   [:: 1/2 - Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 - Num.sqrt(5/6)/6]).
Proof.
intros.
ord_enum_cases i.
apply gauss_weight_4_0.
apply gauss_weight_4_1.
apply gauss_weight_4_2.
apply gauss_weight_4_3.
Defined.

(** ** Packaging together the packages *)

(** We will construct a sequence such that for any ordinal n in 'I_5,
  the ith element of the sequence is guaranteed to be the legendre_roots package for degree n,
  and a similar sequence for gauss_weights.  That guarantee will be enforced by 
  dependent types, so we first need to define the notion of a dependently typed list,
  where the nth element has type T(n).
*)

Inductive iseq (T: nat -> Type) : nat ->Type :=
| i_nil: iseq T O
| i_cons: forall i, T i -> iseq T i -> iseq T (S i).

Arguments i_nil {T}.
Arguments i_cons {T} [i].

Fixpoint nth_iseq [T: nat -> Type] [n: nat] (s: iseq T n) (i: 'I_n) {struct n} : T i.
(* begin details: A function to return the ith element of an iseq *)
destruct n; destruct i as [i Hi].
discriminate.
specialize (nth_iseq T n).
inversion s. subst i0.
simpl.
destruct (PeanoNat.Nat.eq_dec i n).
rewrite e; apply X.
assert (i<n)%N by abstract Lia.lia.
change i with (nat_of_ord (Ordinal H)).
apply nth_iseq. apply X0.
Defined.
(* end details *)

Declare Scope iseq_scope.
Delimit Scope iseq_scope with iseq.

Infix "::" := i_cons (at level 60, right associativity) : iseq_scope.

(** *** The legendre_roots packages up to degree 4 *)

Definition some_legendre_roots: iseq legendre_roots 5 := 
   (legendre_roots_4 
    :: legendre_roots_3
    :: legendre_roots_2 
    :: legendre_roots_1
    :: legendre_roots_0  
    :: i_nil )%iseq.

(** *** The gauss_weights packages up to degree 4 *)

Definition some_gauss_weights: iseq gauss_weights 5 := 
   (gauss_weights_4 
    :: gauss_weights_3
    :: gauss_weights_2 
    :: gauss_weights_1
    :: gauss_weights_0  
    :: i_nil )%iseq.

Lemma legendre_roots_unique: forall [n] (r r': legendre_roots n),
    r=r'.
(* begin details: Proof.  ... easy, by roots_of_ortho_p_unique ... Qed. *)
Proof.
intros.
destruct r as [f1 Hf1 roots1].
destruct r' as [f2 Hf2 roots2].
subst f1 f2.
f_equal.
apply roots_of_ortho_p_unique.
apply lo_lt_hi.
apply w_positive.
Qed.
(* end details *)

(** *** Specialization of quadrature error to our instances for degrees up to 4 *)

  Lemma legendre_quadrature_error': forall (n: 'I_5) (f: R->R),
   let GW := nth_iseq some_gauss_weights n in
      exists ξ:R, lo <= ξ <= hi /\
       ∫ f - compute_G GW f =  
       derive1n (2*n+2) f ξ / 
        (factorial(2*n+2))%:R * ∫ (fun x => (horner (legendre n.+1) x)^2).
  Proof.
  intros. apply legendre_quadrature_error.
 Qed.

End R.

End Legendre.

(** ** The remainder of Stewart's Chapter 23. *)
(** 22.  If we take [[a,b]]=[[0,∞]] and w(x)=e^{-x}, we get a formula to approximate

      [ ∫_0^∞ f(x) e^{-x} dx ].

   This is Gauss-Laguerre quadrature. *)

(** 23. If we take [[a,b]]=[[-∞,∞]] and w(x)=e^{-x^2}, we get a formula to approximate,

       [ ∫_{-∞}^∞ f(x) e^{-x^2} dx ].

   This is Gauss-Hermite quadrature. *)

(** 24.  There are many other Gauss formulas suitable for special purposes.  Most
     mathematical handbooks have tables of abscissas and coefficients.  The
     automatic generation of Gauss formulas is an interesting subject in its own right. *)

(* begin details: some scribblings that should be discarded *)
(** The following experiment should probably be abandoned; perhaps there is
   something in the CoqEAL library that's useful instead. *)
Module ComputableIntegral.

Section R.
Context {R : realType}.



Fixpoint integ_rec {F: Num.NumDomain.type} (al: list F) (n: nat) :=
 match al with
 | nil => nil
 | a :: al' => a / natmul 1 (S n) :: integ_rec al' (S n)
 end.

Lemma integ_last_nonnil: forall {F: Num.NumDomain.type} (al: list F) (n: nat),
  nilp al = false ->
  is_true (last 1 al != 0) -> is_true (last 1 (Algebra.zero :: integ_rec al n) != 0).
intros.
destruct al. discriminate.
simpl in H0. clear H.
simpl.
assert (H1: is_true (last s (integ_rec al n.+1) != 0)).
2:{
clear - H1.
destruct al; auto.
simpl in *.
revert H1; apply contraNN.
rewrite mulIr_eq0 //.
apply /rregP.
apply invr_neq0.
set (a := 0).
replace a
   with (natmul (@GRing.one F) O); auto; clear a.
rewrite eqr_nat. auto.
}
revert n s H0; induction al; simpl; intros; auto.
apply IHal.
rename H0 into H1.
clear - H1.
destruct al; auto.
simpl in *.
revert H1; apply contraNN.
rewrite mulIr_eq0 //.
apply /rregP.
apply invr_neq0.
set (b := 0).
replace b
   with (natmul (@GRing.one F) O); auto; clear b.
rewrite eqr_nat. auto.
Qed.

Definition polylast {F: nzSemiRingType} (p: {poly F}) : last 1 (polyseq p) != 0 :=
  match p with @Polynomial _ _ H => H end.

Definition integ {F: Num.NumDomain.type} (p: {poly F}) : {poly F} :=
 (if nilp (polyseq p) as b return (nilp (polyseq p) = b ->  {poly Num_NumDomain__to__GRing_NzSemiRing F})
  then fun=> p
  else fun H : nilp (polyseq p)=false => Polynomial (integ_last_nonnil (polyseq p) 0 H (polylast p))) erefl.

Lemma integ_eq: forall (* {F: Num.NumDomain.type}*) (p: {poly R}),
  integ p = cons_poly 0 (\poly_(i < (size p)) (p`_i / ((S i)%:R))).
Proof.
destruct p as [al H].
simpl.
destruct al eqn:H0; simpl.
subst .
rewrite Rewriting.poly0 cons_poly_def mul0r add0r polyC0 /integ /=.
apply poly_inj.
rewrite polyseq0 //.
simpl in *.
subst al.
apply poly_inj. simpl.
rewrite invr1 mulr1.
set z:=0. rewrite {3}/z. clearbody z. simpl in z.
rewrite polyseq_cons.
rewrite nil_poly.
set p := poly _ _.
assert (p != 0) by admit.
rewrite H0.
f_equal.
change ((size l).+1) with (size (s::l)) in p.
change (is_true (last 1 (s::l) != 0)) in H.
replace (s :: integ_rec l 1) with (integ_rec (s::l) O)
  by  rewrite /= invr1 mulr1 //.
subst p.
rewrite polyseq_poly; [ | admit].
set al := s::l. clearbody al. clear H0 H s l z.
Admitted.

Fixpoint add_poly' {R: nzSemiRingType} (al bl: seq R) :=
 match al, bl with
 | a :: al', b :: bl' =>  add a b :: add_poly' al' bl'
 | [::], _ => bl
 | _, [::] => al
 end.

Lemma add_poly'_nil: forall {R: nzSemiRingType}  (al: seq R), add_poly' al [::] = al.
Proof.
induction al; simpl; intros; auto.
Qed.

Fixpoint mul_poly'aux {R: nzSemiRingType} (al bl: seq R) :=
 match al with
 | [::] => [::] 
 | a :: al' => add_poly' (map (mul a) bl) (0 :: mul_poly'aux al' bl)
 end.

Definition mul_poly' {R: nzSemiRingType} (al bl: seq R) :=
 match bl with
 | [::] => [::] 
 | _ => mul_poly'aux al bl
 end.

Lemma lastr_neq0: forall [R : nzSemiRingType] (s : seq (NzSemiRing.sort R)) (x : NzSemiRing.sort R),
 is_true (last x s != 0) -> is_true (last 1 s != 0).
Proof.
induction s; simpl; intros; auto.
apply oner_neq0.
Qed.


Lemma mul_poly_eq_aux'{F: idomainType}: forall al bl: seq F,
     last 0 (mul_poly'aux  al bl) = last 0 al * last 0 bl.
Proof.
induction al => bl.
- rewrite mul0r //.
-
simpl.
Admitted.


Lemma mul_poly_eq_aux{F: idomainType}: forall (A B: {poly F}),
     last 1(mul_poly' (polyseq A) (polyseq B)) != 0.
Proof.
destruct A as [al Ha]. destruct B as [bl Hb].
destruct al as [ | a al]; destruct bl as [ | b bl]; try apply oner_neq0.
rewrite /polyseq.
change (last 1 (a::al)) with (last 0 (a::al)) in Ha.
change (last 1 (b::bl)) with (last 0 (b::bl)) in Hb.
pose proof (mul_poly_eq_aux' (a::al) (b::bl)).
assert (last 1 (mul_poly' (a::al) (b::bl)) = last 0 (mul_poly' (a::al) (b::bl)))
 by (simpl; auto).
rewrite H0.
rewrite H.
clear - Ha Hb. simpl in *.
rewrite mulIr_eq0; auto.
apply /rregP; auto.
Qed.

Lemma mul_poly_eq {F: idomainType}: forall (A B: {poly F}),
  mul_poly A B = 
 @Polynomial F (mul_poly' (polyseq A) (polyseq B)) (mul_poly_eq_aux _ _).
Admitted.

End R.
End ComputableIntegral.
(* end details *)



