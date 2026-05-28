(** * CFEM.quadrature:  Gaussian quadrature, following G. W. Stewart *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
Import classical_sets.
Import numFieldNormedType.Exports.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.


Section S.
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

(** 7.  In establishing this result, we may assume that the polynomials p_i are monic.
  The proof is by induction.  For n=0 we have,

      q(x) = a_0 = a_0 ⋅ 1 = a_0 p_0(x).

   Hence we must have b_0 = a_0.

     Now assume that q has the form (23.2).  Since p_n is the only polynomial in
    the sequence p_n, p_{n-1}, ⋯, p_0 that contains x^n and since p_n is monic, it follows
    that we must have b_n = a_n.  Then the polynomial q-a_n p_n is of degree n-1.
    Hence by the induction hypothesis, it can be expressed uniquely in the form

             q - a_n p_n = b_{n-1} p_{n-1} + ⋯ + b_0 p_0,

    which establishes the result.
*)

Proof.
induction n.
Admitted.

(** 8.  A consequence of this result is the following.
            The polynomial p_{n+1} is orthogonal to any polynomial q of degree n or less.

      For from (23.3) is follows that

             ∫  p_{n+1} q = b_n ∫  p_{n+1} p_n + ⋯ + b_0 ∫  p_{n+2}p_0 = 0,

       [note: p_{n+2}p_0 sic in original, but surely p_{n+1}p_0 is meant.  ]
      the last equality following from the orthogonality of the polynomials p_i.
*)

Lemma polySn_orthogonal_n: forall (n:nat) (q: {poly R}), 
            (size q <= n.+1)%nat ->
            orthogonal (horner (p n.+1)) (horner q).
Admitted.

End P.

(** 9. To establish the existence of orthogonal polynomials, we begin by computing
    the first two.  Since p_0 is monic and of degree zero,

                  p_0(x) \equiv 1.

      Since p_1 is monic and of degree one, it must have the form

                   p_1(x) = x - α_1.

    To determine α_1, we use orthogonality:

               0 = ∫  p_1 p_0 = ∫  (x-α_1)⋅1  = ∫  x - α_1 ∫ 1.

    Since the function 1 is positive in the interval of integration,  ∫ 1 > 0, and it 
    follows that

                         α_1 = (∫ x) / (∫ 1).

     10.  In general we will seek p_{n+1} in the form

        p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1} - γ_{n+1} p_{n-2} - ⋯ .

      As in the construction of p_1, we use orthogonality to determine the coefficients

      α_{n+1}, β_{n+1}, γ_{n+1}, ⋯ 

          To determine α_{n+1}, write

      0 = ∫  p_{n+1} p_n = ∫  x p_n p_n - α_{n+1} ∫ p_n p_n - β_{n+1} ∫  p_{n-1} p_n - γ_{n+1} ∫ p_{n-2} p_n - ⋯ .

      By orthogonality, 0 = ∫ p_{n-1} p_n = ∫  p_{n-2} p_n = ⋯ .   Hence

              ∫  x p_n^2 - α_{n+1} ∫ p_n^2 = 0.

      Since ∫  p_n^2 > 0, we may solve this equation to get

               α_{n+1} = ∫ x p_n^2  /  ∫  p_n^2.

      For β_{n+1}, write

             0 = ∫ p_{n+1} p_{n-1} = ∫ x p_n p_{n-1} - α_{n+1} ∫ p_n p_{n-1} - β_{n+1} ∫ p_{n-1} p_{n-1} - γ_{n+1} ∫ p_{n-2} p_{n-1} - ⋯ .

     Dropping terms that are zero because of orthogonality, we get

                      ∫ x p_n p_{n-1} - β_{n+1} ∫ p_{n-1}^2 = 0
      or β_{n+1} = (∫ x p_n p_{n-1} ) / (∫ p_{n-1}^2).

     11. The formulas for the remaining coefficients are similar to the formula for β_{k+1}; e.g.,

                  γ_{n+1} = (∫  x p_n p_{n-2}) / (∫  p_{n-2}^2).

        However, there is a surprise here.  The denominator [sic]   x p_n p_{n-2}  can be written
        in the form ∫  x p_{n-2} p_n.  Since x p_{n-2} is of degree n-1 it is orthogonal to p_n;
        i.e.,  ∫ x p_{n-2} p_{n-1 [sic]}   = 0.  Hence γ_{k+1} = 0, and likewise the coefficients of p_{n-3},
         p_{n-4}, ⋯ are zero.

     12.  To summarize:
          The orthogonal polynomials can be generated by the following recurrence:

          -      p_0 = 1,
          -      p_1 = x - α_1,
          -      p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1},               n=1,2,⋯,
         where 

                  α_{n+1} = (∫  x p_n^2) / (∫ p_n^2)   and β_{n+1} =  (∫  x p_n p_{n-1}) / (∫  p_{n-1}^2).

          The first two equations in the recurrence merely start things off.  The right-hand side
          of the third equation  contains three terms and for that reason is called the
          _three-term recurrence_ for the orthogonal polynomials.
*)

Fixpoint three_term_recurrence (n: nat) : {poly R} * {poly R} :=
   match n with
   | 0 => (1%:P, 0%:P)
   | 1 => let α1 :=  ∫ id /  ∫ (fun=>1) in ('X - α1%:P, 1%:P)
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
        be the zeros of p_{n+1}.  We will now show that 
        
         The zeros of p_{n+1} are real, simple, and lie in the interval [[a,b]].

     14.  Let x_0, x_1, ⋯, x_k  be the zeros of odd multiplicity of p_{n+1} in [a,b]; i.e., x_0,
          x_1, ⋯, x_k are the points at which p_{n+1} changes sign in [a,b].  If k=n, we are 
         through, since the x_i are the n+1 zeros of p_{n+1}.

               Suppose then that k<n and consider the polynomial

                       q(x) = (x-x_0)(x-x_1)⋯(x-x_k).

        Since deg(q) = k+1 < n+1, by orthogonality

                      ∫ p_{n+1} q = 0.

        On the other hand, p_{n+1}(x) q(x) cannot change sign on [[a,b]] -- each sign change
        in p_{n+1}(x) is cancelled by a corresponding sign change in q(x).  It follows that

                     ∫ p_{n+1} q <> 0,

         which is a contradiction.
*)

Lemma roots_of_ortho_p_weak: forall (n: nat) (x: R), 
       root (ortho_p n) x -> 
       proj1_sig (multiplicity_XsubC (ortho_p n) x) = 1%nat /\
       a <= x <= b.
Admitted.

(** It appears that MathComp Analysis does not yet have a full theory of 
    the roots of real polynomials, so in this first attempt we just say that the real 
    roots of p_n are simple and in the interval, but this omits that all the roots are real. *)

Definition roots_of_ortho_p: forall (n: nat),
    { roots: n.-tuple R | all (root (ortho_p n)) (tval roots) /\ uniq_roots (tval roots)}.
(** That is, p_n has n distinct roots.  From that, one could prove that they're all simple,
   and that there are no nonreal roots. 
   However, since MathComp Analysis doesn't yet have a full theory of the roots of 
   real polynomials, this might not be so easy.
 *)
Admitted.

(** ** Gaussian quadrature *)

(** 15.  The Gaussian quadrature formula is obtained by constructing a Newton-Cotes
     formula on the zeros of the orthogonal polynomial p_{n+1}.

     Let x0, x_1, ⋯, x_n be the zeros of the orthogonal polynomial p_{n+1} and set

               A_i = ∫  L_i,   i = 0, 1, ⋯, n,

     where L_i is the ith Lagrange polynomial over x_0, x_1, ⋯, x_n.  For any function f let

               G_n f = A_0 f(x_0) + A_1 f(x_1) + ⋯ + A_n f(x_n).

    Then   deg(f) ≤ 2n+1  ⇒  ∫  f = G_n f.
*)

 Section Quadrature.
  Variable n : nat.
  Definition zeros_of_ortho_p := proj1_sig (roots_of_ortho_p n).
  Definition L : n.-tuple {poly_n R} := lagrange n (nth 0 zeros_of_ortho_p).
  Definition A (i: 'I_n) := ∫ (horner (tnth L i)).

  Definition G (f: R->R) := \sum_i (A i * (f (tnth zeros_of_ortho_p i))).

  (** 16.  To establish this result, first note that by construction the integration formula
    G_n f is exact for polynomials of degree less than or equal to n (see section 21.17).

         Now let deg(f) ≤ 2n+1.  Divide f by p_{n+1} to get

                  f = p_{n+1}q + r,      deg(q), deg(r) ≤ n.                             (23.4)

      Then

       - G_n f = Σ_i A_i f(x_i)
       -          = Σ_i A_i(p_{n+1}(x_i)q(x_i) + r(x_i))                       (by 23.4)
       -          = Σ_i A_i r(x_i)                                                 because p_{n+1}(x_i)=0
       -          = G_n r
       -          = ∫ r                                                because G_n is exact for deg(r) ≤ n
       -          = ∫ (p_{n+1}q+r)                            because ∫ p_{n+1}q = 0 for deg(q) ≤ n
       -          = ∫ f                                                (by 23.4).
      Quot erat demonstrandum.
  *)

  Lemma quadrature_exact_for: forall f: {poly R}, (size f <= 2*n+2)%N -> ∫ (horner f) = G (horner f).
  Admitted.

(** 17. An important corollary of these results is that the coefficients A_i are positive.
       To see this note that

                L_i(x_j) = L_i^2(x_j) = if i=j then 1 else 0.

      Since L_i^2(x) ≥ 0 and deg(L_i^2) = 2n,

              0 < ∫ L_i^2 = Σ_j A_i L_i^2(x_j) = A_i.
*)
   Lemma A_positive: forall i, A i > 0.
   Admitted.

(** 18.  Since A_0 + A_1 + ⋯ + A_n = ∫ 1, no coefficient can be larger than 1.  Consequently,
     we cannot have a situation in which large coefficients create large intermediate results
      that suffer cancellation when they are added. *)

   Lemma A_leq_1:  forall i, A i <= 1.
   Admitted.

(** ** Error and convergence *)

Locate "^`".

(** 19.  Gaussian quadrature has error formulas similar to the ones for Newton-Cotes
    formulas.  Specifically

          ∫  f - G_n f =  ( f^(2n+2)(ξ) / (2n+2)!) ∫ p_{n+1}^2,

     where ξ ∈ [[a,b]]. *)
  Lemma quadrature_error: forall (f: R->R),
      exists ξ:R, a <= ξ <= b /\
       ∫ f - G f =  derive1n (2*n+2) f ξ / natmul 1 (factorial(2*n+2)) * ∫ (fun x => (horner (ortho_p(n+1)) x)^2).
  Admitted.

(** 20. A consequence of the positivity of the coefficients A_i is that Gaussian
    quadrature converges for any continuous function; that is,

        f continuous ⇒ lim_{n→∞} G_n f = ∫ f.

    The proof -- it is a good exercise in elementary analysis -- is based on the Weierstrass
    approximation theorem, which says that for any continuous function f
    there is a sequence of polynomials that converges uniformly to f.
*)

  Lemma quadrature_converges:  forall (f: Real.sort R -> Real.sort R) (x: R),
    (forall x, continuous_at x f) -> limn (fun n => G f) = ∫ f.
  Admitted.


End Quadrature.
End Integral.

(** ** Examples *)

(** 21. Particular Gauss formulas arise from particular choices of the interval [[a,b]]
      and the weight function w(x).  The workhorse is Gauss-Legendre quadrature,
     in which [[a,b]] = [[-1,1]] and w(x)=1, so that the formula approximates the integral,

      ∫_{-1}^1 f(x) dx.

    The corresponding orthogonal polynomials are called Legendre polynomials.
*)

Section Legendre.
 Notation "∫" := (intgal (-1) 1 (fun=>1)).

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

Require Import FunctionalExtensionality.

Lemma Legendre_poly_1:
   horner (ortho_p (-1) 1 (fun=>1) 1) = 
  fun x => x.
Proof.
extensionality x.
unfold ortho_p. simpl. rewrite intgal_w1_1 intgal_w1_x.
rewrite ?scale_polyE ?hornerM ?hornerD ?hornerN ?hornerM ?hornerXsubC ?hornerX ?hornerD ?hornerC.
lra.
Qed.

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

Lemma opp_funC: forall  {U : Type} {V : BaseZmodule.type} (c: V), 
  @opp_fun U V (fun=>c) = (fun=> opp c).
Proof.
intros. extensionality x. reflexivity.
Qed.

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

Lemma sub_funr0: forall {U: Type} {V: zmodType} (f: U -> V),
  sub_fun f (fun=>0) = f.
Proof. intros. extensionality x. simpl. apply subr0.
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

Lemma Legendre_poly_2:
   horner (ortho_p (-1) 1 (fun=>1) 2) = 
  fun x => x*x - 1/3.
Proof.
extensionality x.
unfold ortho_p. simpl. rewrite intgal_w1_1 intgal_w1_x.
rewrite ?scale_polyE ?hornerM ?hornerD ?hornerN ?hornerM ?hornerXsubC ?hornerX ?hornerD ?hornerC.
rewrite hornerXsubC' mul0r sub_funr0 subr0 hornerC' ?mul_funr1.
rewrite mulr1.
rewrite intgal_w1_1 intgal_w1_x3 intgal_w1_x2.
rewrite ?mul0r subr0.
f_equal.
lra.
Qed. 

Lemma Legendre_poly_3:
   horner (ortho_p (-1) 1 (fun=>1) 3) = 
  fun x => x*x*x - (3/5)*x.
Proof.
extensionality x.
unfold ortho_p. simpl. rewrite intgal_w1_1 intgal_w1_x.
rewrite ?scale_polyE ?hornerM ?hornerD ?hornerN ?hornerM ?hornerXsubC ?hornerX ?hornerD ?hornerC.
rewrite hornerXsubC' ?hornerC'.
rewrite mul0r subr0 sub_funr0 mul_funr1.
rewrite  intgal_w1_x3 intgal_w1_x2 mul0r.
rewrite ?hornerM' ?hornerD' ?hornerN' ?hornerM' hornerX' ?hornerC' /=.
rewrite mul_fun0r mul_fun1r mul_funr1 intgal_w1_1.
rewrite mulr1 mul0r subr0.
repeat change (?A \+ \- ?B) with (A \- B).
rewrite sub_funr0.
set a := (2 / 3 / 2); replace a with ((1/3):R) by (subst a; lra); clear a.
rewrite subr0.
rewrite ?mul_funDr ?mul_funDl ?(intgal_linear2 ltac:(lra) ltac:(intros; lra)).
rewrite ?mul_funDr ?mul_funDl ?(intgal_linear2 ltac:(lra) ltac:(intros; lra)).
rewrite -?mul_funA.
set a := (fun=> - _).
rewrite (mul_funC id (a \* _)) -?mul_funA.
rewrite (mul_funC _ a).
rewrite (mul_funC id (a \* _)) -?mul_funA.
rewrite (mul_funC id (a \* _)) -?mul_funA.
repeat rewrite (intgal_linear2 ); [  | intros; lra..].
rewrite (mul_funC id (a \* _)) -?mul_funA.
rewrite (mul_funA a a).
replace (mul_fun a a) with (fun _:R => (1/9:R)).
2:  extensionality y; unfold a; simpl; lra.
unfold a; rewrite ?intgal_linear1; try (intros; lra).
rewrite intgal_w1_x5 intgal_w1_x3 intgal_w1_x4 intgal_w1_x intgal_w1_x2 intgal_w1_C.
field; auto.

(** 22.  If we take [[a,b]]=[[0,∞]] and w(x)=e^{-x}, we get a formula to approximate

       ∫_0^∞ f(x) e^{-x} dx.

   This is Gauss-Laguerre quadrature. *)

(** 23. If we take [[a,b]]=[[-∞,∞]] and w(x)=e^{-x^2}, we get a formula to approximate,

       ∫_{-∞}^∞ f(x) e^{-x^2} dx.

   This is Gauss-Hermite quadrature. *)

(** 24.  There are many other Gauss formulas suitable for special purposes.  Most
     mathematical handbooks have tables of abscissas and coefficients.  The
     automatic generation of Gauss formulas is an interesting subject in its own right. *)

End S.










