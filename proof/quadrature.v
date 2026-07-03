(** * CFEM.quadrature:  Gaussian quadrature, following G. W. Stewart *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
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


Section R.
Context {R : realType}.

(** This derivation follows Lecture 23 of _Afternotes on Numerical Analysis_ 
    by G. W. Stewart, SIAM Press, 1996 *)

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
 Definition  intgal (f: R -> R) := \int[lebesgue_measure]_(x in `[a,b]%classic) (f x * w x).
 Notation "∫" := intgal.
 
(** 3.  Regarded as an operator on functions, ∫  is linear.  That is, ∫ α f = α ∫  f and
  ∫ (f + g) = ∫ f + ∫ g.  We will make extensive use of linearity in what follows. *)


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

(**  5. A sequence of  _orthogonal polynomials_ is a sequence {p_i}_{i=0}^∞ of polynomials
   with deg(p_i) = i such that      i <> j -> ∫ p_i p_j = 0.                         (23.1)
*)


 Definition orthogonal_polynomals (p: nat -> {poly R}) : Prop := 
   (forall i, size (p i) = (i+1)%N) /\
   (forall i j: nat, i<>j -> ∫ (horner (p i) \* horner (p j)) = 0).

(** Since orthogality is not altered by multiplication by a nonzero constant, we
   may normalize the polynomial p_i so that the coefficient of x^i is one: i.e.,

   p_i(x) = x^i + a_{i,i-1}x^{i-1} + ⋯ + a_{i0}.

 Such a polynomial is said to be _monic_.  *)

Locate monic_pred.  (*  Constant mathcomp.algebra.poly.monic_pred *)
Print monic_pred.  (* = fun (R : nzSemiRingType) (p : {poly R}) => lead_coef p == 1
     : [ forall [R : nzSemiRingType], {poly R} -> bool  ] *)

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
         { b: 'I_n.+1 -> R | horner q = \big[add_fun/fun=>0]_(i<n.+1) (b i  \*: horner (p i))}.

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

       _(Note: [p_{n+2}p_0] sic in original, but surely p_{n+1}p_0 is meant.)_
      the last equality following from the orthogonality of the polynomials [p_i].
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

Lemma ortho_p_orthogonal: forall i j, (i<>j)%N -> orthogonal (horner (ortho_p i)) (horner (ortho_p j)).
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

(** _Editor's note: This predicate says that [roots] is a list of n distinct values, all of which evaluate
     (under the polynomial) to zero, which implies that they are simple roots._*)

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
     there are at most n+1 zeros.  That is: *)

Lemma roots_of_ortho_p_at_most: forall [n] (roots: roots_of_ortho_p n),
  forall x, root (ortho_p n) x -> x \in ROOTS_vals roots.
Admitted.


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

Lemma roots_of_ortho_p_unique (n: nat) : forall r r' : roots_of_ortho_p n, r=r'.
Proof.
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
Admitted.

(** _Editor's note:  The following is what we want; it is a constructive existence, so that we 
   can calculate with these roots.  But Stewart's proof is nonconstructive.
  The complex roots of a rational-valued polynomial do exist constructively, see for example
   the Jenkins-Traub algorithm(s); then one could use Stewart's proof to guarantee that all
  the complex roots are real.  There are simpler algorithms than Jenkins-Traub,
   which don't converge as fast but would suffice for a constructive existence proof,
   but we want more than constructive existence, eventually we want to check how close
   certain floating-point numbers are to the true roots.  That is, we want constructive accuracy,
   i.e., fast convergence.  Either way, since the roots are found by iteration, then the construction
   is effectively a Cauchy sequence_.

   _And furthermore, at present MathComp Analysis doesn't yet have a full theory of the roots of 
   real polynomials, nor any formalization of Jenkins-Traub, so any such proof will not be trivial_. *)
Definition roots_of_ortho_p_exist (n: nat) : roots_of_ortho_p n.
Abort.

(** _Therefore, we will proceed assuming that, for any given ortho_p (such as Gauss-Legendre,
  Gauss-Hermite, etc.) someone will present an constructive instance of roots_of_ortho_p. *)


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


  (** Editor's note: we need this [extend_roots] to prove injectivity when using [lagrangeE] *)
  Definition extend_roots  (i: nat) : R :=
     nth ((i+1-n)%:R) zeros_of_ortho_p i.

  Lemma extend_roots_injective: injective extend_roots.
  Admitted.

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



  Lemma quadrature_exact_for: forall f: {poly R}, (size f <= 2*n+2)%N -> ∫ (horner f) = G (horner f).
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
       ∫ f - G f =  derive1n (2*n+2) f ξ / natmul 1 (factorial(2*n+2)) * ∫ (fun x => (horner (ortho_p(n+1)) x)^2).
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
  Admitted.


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

(* From mathcomp Require Import Rstruct.
Import Rdefinitions. *)
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

Lemma pull_left_const1: forall  {s : comPzSemiRingType} (c: s) (B: s->s),
  mul_fun (fun x: ComPzSemiRing.sort s => x)
     (mul_fun (fun=>c)  B)
= mul_fun (fun=>c) (mul_fun (fun x: ComPzSemiRing.sort s => x) B).
Proof.
intros. rewrite mul_funC. rewrite -mul_funA. f_equal. apply mul_funC.
Qed. 

Lemma pull_left_const2: forall  {s : comPzSemiRingType} (c: s),
  mul_fun (fun x: ComPzSemiRing.sort s => x) (fun=>c)  
= mul_fun (fun=>c) (fun x: ComPzSemiRing.sort s => x).
Proof. intros; apply  mul_funC.
Qed.

Lemma pull_left_const3: forall  {s : comPzSemiRingType} (c d: s) (B: s->s),
  mul_fun (fun=> c) (mul_fun (fun=>d) B) 
= mul_fun (fun=> c*d) B.
Proof. intros. rewrite mul_funA. f_equal.
Qed.

Lemma pull_left_const4: forall (c: R) (B: R -> R),
  opp_fun (mul_fun (fun=>c) B) = mul_fun (fun=> - c) B.
Proof.
intros.
extensionality x. simpl. lra.
Qed.

Lemma pull_left_const5 : forall (c: R),
  opp_fun (fun x : R =>c) = (fun x : R => - c).
Proof.
intros.
extensionality x. simpl. lra.
Qed.

Definition pull_left_const := (@pull_left_const1, @pull_left_const2, @pull_left_const3, @pull_left_const4, @pull_left_const5).

End R.

End Rewriting.
Module Legendre.
 Section R.
 Context {R : realType}.
 Import Rewriting.
 Definition lo : R := (-1)%R.
 Definition hi : R := 1%R.
 Lemma lo_lt_hi: (lo < hi)%R.
 Proof. unfold lo,hi. lra. Qed.
 Definition w (x: R) : R := 1%R.
 Lemma w_positive: forall x, is_true (lo <= x <= hi) -> is_true (0 < w x).
 Proof. intros. rewrite /w. lra. Qed.


 Notation "∫" := (@intgal R lo hi w).

Definition intgal_linear1 := @intgal_linear1 R (-1) 1 lo_lt_hi w ltac:(intros; rewrite /lo /hi /w /=; lra).
Definition intgal_linear2 := @intgal_linear2 R lo hi lo_lt_hi w ltac:(intros; rewrite /lo /hi /w /=; lra).

Lemma intgal_w1_x:  ∫ id = 0.
Proof.
Admitted.

Lemma intgal_w1_1:  ∫ (fun=>1) = 2.
Admitted.

Lemma intgal_w1_C: forall c,  ∫ (fun=>c) = 2*c.
Admitted.

Lemma intgal_w1_x2:  ∫(id \* id) = 2/3.
Admitted.

Lemma intgal_w1_x3: ∫ (id \* (id \* id)) = 0.
Admitted.

Lemma intgal_w1_x4: ∫ (id \* (id \* (id \* id))) = 2/5.
Admitted.

Lemma intgal_w1_x5: ∫ (id \* (id \* (id \* (id \* id)))) = 0.
Admitted.

Lemma intgal_w1_x6: ∫ (id \* (id \* (id \* (id \* (id \* id))))) = 2/7.
Admitted.

Lemma intgal_w1_x7: ∫ (id \* (id \* (id \* (id \* (id \* (id \* id)))))) = 0.
Admitted.

Definition r_intgal := (intgal_w1_1,intgal_w1_C, intgal_w1_x, intgal_w1_x2, 
        intgal_w1_x3, intgal_w1_x4, intgal_w1_x5,
        intgal_w1_x6, intgal_w1_x7 ).

Definition legendre (n: nat) : R -> R :=  horner (ortho_p lo hi w n) .

Record legendre_roots (n: nat) := {
   LR_poly: R -> R;
   LR_poly_eq: legendre n = LR_poly;
   LR_roots: roots_of_ortho_p lo hi w n
}.
Arguments LR_poly [n].
Arguments LR_poly_eq [n].
Arguments LR_roots [n].
Arguments Build_legendre_roots [n].

Record gauss_weights (n: nat) := {
   GW_legendre: legendre_roots n;
   GW_vals: n.-tuple R;
   GW_good: forall i, gauss_weight _ _ _ _ (LR_roots GW_legendre) i = tnth GW_vals i
}.
Arguments GW_legendre [n].
Arguments GW_vals [n].
Arguments GW_good [n].
Arguments Build_gauss_weights [n].

 Let compute_G [n] (GW: gauss_weights n) (f: R -> R) :=
  \sum_i (tnth (GW_vals GW) i) * f (tnth (ROOTS_vals lo hi w n (LR_roots (GW_legendre GW))) i).

Lemma compute_G_eq: forall n (GW: gauss_weights n) f, compute_G GW f = G lo hi w n (LR_roots (GW_legendre GW)) f.
Proof.
intros.
rewrite /compute_G /G.
f_equal.
extensionality i.
f_equal.
f_equal.
symmetry; apply GW_good.
Qed.

 Lemma legendre_quadrature_error: forall [n: nat] (GW: gauss_weights n) (f: R -> R),
      exists ξ:R, lo <= ξ <= hi /\
       ∫ f - compute_G GW f =  derive1n (2*n+2) f ξ / natmul 1 (factorial(2*n+2)) * ∫ (fun x => (legendre (n+1) x)^2).
Proof.
intros.
rewrite compute_G_eq.
apply quadrature_error. apply lo_lt_hi. apply w_positive.
Qed.

Lemma Legendre_poly_0: legendre 0 = fun x: R => 1%R.
Proof.
rewrite /legendre /ortho_p /= ?scale_polyE ?r_intgal ?r_horner ?r_ring ?r_lift ?r_intgal ?r_lift ?r_ring ?r_lift //.
Qed.

Lemma Legendre_poly_1: legendre 1 =  fun x:R => x.
Proof.
rewrite  /legendre /ortho_p /= ?scale_polyE ?r_intgal ?r_horner ?r_ring ?r_lift ?r_intgal ?r_lift ?r_ring ?r_lift //.
Qed.

Lemma Legendre_poly_2: legendre 2 =   fun x :R => x*x - 1/3.
Proof.
rewrite  /legendre /ortho_p /= ?scale_polyE ?r_intgal ?r_horner ?r_intgal ?r_ring ?r_lift  ?r_intgal ?r_ring ?r_lift ?r_intgal //.
extensionality x; simpl; lra.
Qed. 

Lemma Legendre_poly_3: legendre 3 =  fun x :R => x*x*x - (3/5)*x.
Proof.
rewrite /legendre /ortho_p /=.
match goal with |- _ = ?B => set RHS := B end.
rewrite !hornerC' ?r_lift.
rewrite ?r_intgal ?r_ring ?scale_0poly ?r_ring.
rewrite hornerX' ?r_intgal ?r_ring ?scale_0poly ?r_ring.
match goal with |- context [scale_poly ?x] => replace x with (@inv R 3) by nra end.
rewrite ?scale_polyE.
rewrite !r_horner ?r_lift ?r_intgal ?r_ring ?r_lift.
match goal with |- context [fun=> opp ?A] => set a := opp A; simpl in a end.
repeat rewrite ?mul_funDr ?mul_funDl ?intgal_linear2.
rewrite -?mul_funA.
rewrite ?mul_fun_consts ?pull_left_const.
rewrite ?intgal_linear1 ?r_intgal ?r_lift ?r_ring ?r_lift.
rewrite -?mul_funA.
rewrite !pull_left_const.
subst RHS a.
extensionality x; simpl; field; auto.
Qed.

Lemma Legendre_poly_4: legendre 4 =  fun x :R => x*x*x*x - (30/35)*(x*x) + (3/35).
Proof.
rewrite /legendre /ortho_p /=.
match goal with |- _ = ?B => set RHS := B end.
rewrite !hornerC' ?r_lift.
rewrite ?r_intgal ?r_ring ?scale_0poly ?r_ring.
rewrite hornerX' ?r_intgal ?r_ring ?scale_0poly ?r_ring.
match goal with |- context [scale_poly ?x] => replace x with (@inv R 3) by nra end.
rewrite ?scale_polyE.
rewrite !r_horner ?r_lift ?r_intgal ?r_ring ?r_lift.
match goal with |- context [fun=> opp ?A] => set a := opp A; simpl in a end.
simpl.
time 
(* with_strategy opaque [intgal add_fun opp_fun mul_fun inv ] *)
repeat rewrite ?(@mul_funDr R R) ?(@mul_funDl R R) ?intgal_linear2.
rewrite -?mul_funA.
rewrite ?mul_fun_consts.
simpl.
time  with_strategy opaque [intgal add_fun opp_fun mul_fun inv ]
rewrite ?pull_left_const. (* 18 seconds *)
rewrite ?intgal_linear1 ?r_intgal ?r_lift ?r_ring ?r_lift.
rewrite -?mul_funA.
rewrite !pull_left_const.
rewrite !intgal_linear1 !r_intgal ?r_ring.
rewrite !r_lift ?r_ring ?r_lift.
subst RHS a.
extensionality x.
simpl.
field.
auto.
Qed.

Definition legendre_roots_0 : legendre_roots 0.
  apply (Build_legendre_roots _ Legendre_poly_0).
  apply (Build_roots_of_ortho_p lo hi _ 0 (@Tuple 0 _ nil isT)).
- constructor.
- reflexivity.
- reflexivity.
Defined.

Require CFEM.matrix_util.

Notation sqrt := (@Num.sqrt R).

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

Lemma eq_opI: forall {s} (A B: Equality.sort s), A=B -> is_true (eq_op A B).
Proof.
intros.
subst.
apply eq_refl.
Qed.

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

Definition legendre_roots_val := 
  @Tuple 4 _ 
    [:: -(sqrt ((3 + 2 * sqrt(6/5))/7)); -(sqrt ((3 - 2 * sqrt(6/5))/7)); 
         (sqrt ((3 - 2 * sqrt(6/5))/7)); (sqrt ((3 + 2 * sqrt(6/5))/7)) ] isT.

Lemma legendre_roots_4a: 
   is_true (all (root (ortho_p lo hi w 4)) (tval legendre_roots_val)).
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

Lemma legendre_roots_4b:
  is_true (sorted <%R (tval legendre_roots_val)).
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

Lemma legendre_roots_4c:
 is_true   (all (fun x : Order.Preorder.sort (reals_Real__to__Order_Preorder R) => lo <= x <= hi)
     (tval legendre_roots_val)).
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


Definition legendre_roots_4: legendre_roots 4.
  apply (Build_legendre_roots _ Legendre_poly_4).
 apply (Build_roots_of_ortho_p lo hi _ _  legendre_roots_val
   legendre_roots_4a legendre_roots_4b legendre_roots_4c).
Defined.

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


Definition gauss_weights_0 : gauss_weights 0.
 apply (Build_gauss_weights legendre_roots_0 [::]).
intros.
matrix_util.ord_enum_cases i.
Defined.

Lemma gauss_weight_1_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_1) (@Ordinal 1 0 isT) = 2.
Proof.
rewrite /gauss_weight /legendre_roots_1 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift;
  rewrite  invr1; 
  apply intgal_w1_1.
Qed.

Definition gauss_weights_1 : gauss_weights 1.
 apply (Build_gauss_weights legendre_roots_1 [:: 2 ]).
intros.
matrix_util.ord_enum_cases i.
apply gauss_weight_1_0.
Defined.

Lemma gauss_weight_2_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 0 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
 set s3 := Num.sqrt 3. simpl in s3.
rewrite -(div1r s3) mulN1r.
transitivity ( ∫ (((fun=> -(s3/2)) \* id) \+ (fun=>1/2))).
-
f_equal.
extensionality x.
simpl.
assert (0 < s3). rewrite sqrtr_gt0; lra.
set u := _ / _.
set v := _ - u.
replace v with (-(2*u)) by (subst v; lra). clear v.
rewrite invrN.
subst u.
rewrite mul1r.
rewrite invf_div.
rewrite mulrDr.
rewrite mulrNN.
rewrite  (mulrC (s3 / 2)) mulrA (mulrC _ s3).
rewrite mulfV; try lra.
-
rewrite ?intgal_linear2 ?intgal_linear1 ?intgal_w1_C ?intgal_w1_x.
lra.
Qed.


Lemma gauss_weight_2_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 1 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
 set s3 := Num.sqrt 3. simpl in s3.
rewrite -(div1r s3) mulN1r.
rewrite opprK.
transitivity ( ∫ (((fun=> (s3/2)) \* id) \+ (fun=>1/2))).
-
f_equal.
extensionality x.
simpl.
assert (0 < s3). rewrite sqrtr_gt0; lra.
set u := _ / _.
set v := _ + u.
replace v with ((2*u)) by (subst v; lra). clear v.
subst u.
rewrite mul1r.
rewrite invf_div.
rewrite mulrDr.
rewrite opprK.
rewrite  (mulrC (s3 / 2) (inv s3)) mulrA (mulrC _ s3).
rewrite mulfV; try lra.
-
rewrite ?intgal_linear2 ?intgal_linear1 ?intgal_w1_C ?intgal_w1_x.
lra.
Qed.

Definition gauss_weights_2 : gauss_weights 2.
 apply (Build_gauss_weights legendre_roots_2 [:: 1; 1]).
Proof.
intros.
matrix_util.ord_enum_cases i.
apply gauss_weight_2_0.
apply gauss_weight_2_1.
Defined.

Lemma gauss_weight_3_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 0 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
 set s3 := Num.sqrt (3/5). simpl in s3.
set u := _ - _. simpl in u.
replace u with (- (s3 * 2))%R by (subst u; lra). clear u.
rewrite mulrNN.
rewrite mulrA. rewrite {1 2}/s3.
rewrite sqr_sqrt ; [ | lra].
rewrite (mulrC _ 2) mulrA.
rewrite invf_div.
rewrite intgal_linear1.
rewrite mul_funDr.
rewrite intgal_linear2.
rewrite (mul_funC _ (fun=> - s3)).
rewrite intgal_linear1 intgal_w1_x intgal_w1_x2. lra.
Qed.


Lemma gauss_weight_3_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 1 isT) = 8/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
 set s3 := Num.sqrt (3/5). simpl in s3.
rewrite opprK. rewrite mulrN invrN. 
rewrite sqr_sqrt ; [ | lra].
rewrite invf_div.
rewrite intgal_linear1.
rewrite mul_funDr ?mul_funDl ?intgal_linear2 ? intgal_linear1.
rewrite (mul_funC _ (fun _ => -s3)) ?intgal_linear1.
rewrite ?intgal_w1_C.
rewrite intgal_w1_x intgal_w1_x2.
rewrite r_ring. rewrite mulr0 add0r addr0 opprK.
rewrite (mulrC s3) -mulrA.
rewrite ?mulNr.
rewrite sqr_sqrt; lra.
Qed.

Lemma gauss_weight_3_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 2 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
 set s3 := Num.sqrt (3/5). simpl in s3.
set u := _ - _. simpl in u.
replace u with ((s3 * 2))%R by (subst u; lra). clear u.
rewrite (mulrC s3) -mulrA.
rewrite sqr_sqrt ; [ | lra].
rewrite intgal_linear1.
rewrite mul_funDl.
rewrite intgal_linear2.
rewrite intgal_linear1 intgal_w1_x intgal_w1_x2. lra.
Qed.


Definition gauss_weights_3 : gauss_weights 3.
 apply (Build_gauss_weights legendre_roots_3 [:: 5/9; 8/9; 5/9]).
Proof.
intros.
matrix_util.ord_enum_cases i.
apply gauss_weight_3_0.
apply gauss_weight_3_1.
apply gauss_weight_3_2.
Defined.

Lemma add_mul2: forall (x :R), x+x = 2*x.
Proof. intros. lra. Qed.

Lemma add_mul3: forall (x :R), x+(x+x) = 3*x.
Proof. intros. lra. Qed.

Lemma gauss_weight_4_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 0 isT) = 
       1/2 - Num.sqrt(5/6)/6.
Proof.
set RHS := _ - _. simpl in RHS.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite opprK.
rewrite intgal_linear1.
match goal with |- ?A * _ = _ => set a := A end.
rewrite -opp_funC.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in a,b,c.
rewrite ?mul_funDl ?mul_funDr.
simpl.
rewrite ?intgal_linear2 ?intgal_linear1.
rewrite  -?mul_funA.
rewrite ?pull_left_const ?intgal_linear1.
rewrite ?r_intgal.
rewrite ?r_ring.
rewrite ?opprK.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
rewrite mulrA mulrN sqr_sqrt; try lra.
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

Lemma sub_mul2: forall (x :R), -x-x = -(2*x).
Proof. intros. lra. Qed.

Lemma opp_sub: forall (x y:R), -x-y = -(x+y).
Proof. intros. lra. Qed.

Lemma gauss_weight_4_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 1 isT) = 
       1/2 + Num.sqrt(5/6)/6.
Proof.
set RHS := _ + _. simpl in RHS.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ]].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite opprK.
rewrite intgal_linear1.
match goal with |- ?A * _ = _ => set a := A end.
rewrite -opp_funC.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in a,b,c.
rewrite ?mul_funDl ?mul_funDr.
simpl.
rewrite ?intgal_linear2 ?intgal_linear1.
rewrite  -?mul_funA.
rewrite ?pull_left_const ?intgal_linear1.
rewrite ?r_intgal.
rewrite ?r_ring.
rewrite ?opprK.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
rewrite mulrA ?mulrN ?mulNr.
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
rewrite (mulrA _ 7).
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

Lemma gauss_weight_4_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 2 isT) = 
       1/2 + Num.sqrt(5/6)/6.
Proof.
rewrite -gauss_weight_4_1.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ] .. ].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite ?opprK.
rewrite ?intgal_linear1.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?mul_funDl ?mul_funDr.
rewrite ?intgal_linear2 ?intgal_linear1.
rewrite ?opprK. rewrite ?mulNr ?mulrN.
rewrite ?pull_left_const ?intgal_linear1.
rewrite ?r_intgal.
rewrite ?r_ring.
rewrite !mulrN ?mulNr.
rewrite ?opp_sub ?mulrN ?mulnR.
set cu := (c*(2/3)).
set cv := (b * (2/3)).
set cb2c := (c * (b * (2 * c))).
set u1 := (_ + cv + _ ).
replace u1 with (cv - cb2c)%R by (subst u1; lra). clear u1.
set u2 := (_ + (_ -- _)).
replace u2 with (-(cv - cb2c))%R by (subst u2; lra); clear u2.
rewrite mulrN.
rewrite ?mulrA.
rewrite -mulNr.
f_equal.
rewrite ?mulrN ?mulNr opprK.
rewrite -invrN.
f_equal.
lra.
Qed.

Lemma gauss_weight_4_3: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 3 isT) = 
       1/2 - Num.sqrt(5/6)/6.
Proof.
rewrite -gauss_weight_4_0.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; [apply lo_lt_hi | apply w_positive ] .. ].
rewrite bigop.unlock index_enum_ord_enum;
  match goal with |- context [ord_enum ?n] => matrix_util.compute_ord_enum n end;
  rewrite /extend_roots /= ?r_horner ?r_lift.
 rewrite ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite ?opprK.
rewrite ?intgal_linear1.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?mul_funDl ?mul_funDr.
rewrite ?intgal_linear2 ?intgal_linear1.
rewrite ?opprK. rewrite ?mulNr ?mulrN.
rewrite ?pull_left_const ?intgal_linear1.
rewrite ?r_intgal.
rewrite ?r_ring.
rewrite !mulrN ?mulNr.
rewrite ?opp_sub ?mulrN ?mulnR.
set cu := (c*(2/3)).
set cv := (b * (2/3)).
rewrite (mulrC b).
rewrite (mulrC 2 c).
rewrite !(mulrA c).
rewrite (mulrA (c *c)).
set cb2c := (c * c * 2 * b).
set u1 := (_ + cu+ _ ).
replace u1 with (cv - cb2c)%R by (subst u1; lra). clear u1.
set u2 := (_ + (_ -- _)).
replace u2 with (-(cv - cb2c))%R by (subst u2; lra); clear u2.
rewrite mulrN.
rewrite ?mulrA.
rewrite -mulNr.
f_equal.
rewrite ?mulrN ?mulNr opprK.
rewrite -invrN.
f_equal.
lra.
Qed.

Definition gauss_weights_4 : gauss_weights 4.
 apply (Build_gauss_weights legendre_roots_4
   [:: 1/2 - Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 - Num.sqrt(5/6)/6]).
Proof.
intros.
matrix_util.ord_enum_cases i.
apply gauss_weight_4_0.
apply gauss_weight_4_1.
apply gauss_weight_4_2.
apply gauss_weight_4_3.
Defined.

Record legendre_roots_and_weights :=  { 
    PR_n : nat ;
    PR_roots: legendre_roots PR_n;
    PR_weights: gauss_weights PR_n
}.

Inductive iseq (T: nat -> Type) : nat ->Type :=
| i_nil: iseq T O
| i_cons: forall i, T i -> iseq T i -> iseq T (S i).

Arguments i_nil {T}.
Arguments i_cons {T} [i].

Fixpoint nth_iseq [T: nat -> Type] [n: nat] (s: iseq T n) (i: 'I_n) {struct n} : T i.
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

Declare Scope iseq_scope.
Delimit Scope iseq_scope with iseq.

Infix "::" := i_cons (at level 60, right associativity) : iseq_scope.

Definition some_legendre_roots: iseq legendre_roots 5 := 
   (legendre_roots_4 
    :: legendre_roots_3
    :: legendre_roots_2 
    :: legendre_roots_1
    :: legendre_roots_0  
    :: i_nil )%iseq.

Definition some_gauss_weights: iseq gauss_weights 5 := 
   (gauss_weights_4 
    :: gauss_weights_3
    :: gauss_weights_2 
    :: gauss_weights_1
    :: gauss_weights_0  
    :: i_nil )%iseq.

End R.

End Legendre.

(** 22.  If we take [[a,b]]=[[0,∞]] and w(x)=e^{-x}, we get a formula to approximate

      [ ∫_0^∞ f(x) e^{-x} dx ].

   This is Gauss-Laguerre quadrature. *)

(** 23. If we take [[a,b]]=[[-∞,∞]] and w(x)=e^{-x^2}, we get a formula to approximate,

       [ ∫_{-∞}^∞ f(x) e^{-x^2} dx ].

   This is Gauss-Hermite quadrature. *)

(** 24.  There are many other Gauss formulas suitable for special purposes.  Most
     mathematical handbooks have tables of abscissas and coefficients.  The
     automatic generation of Gauss formulas is an interesting subject in its own right. *)










