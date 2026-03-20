(** * CFEM.shape:  Lagrange shape functions, and some supporting theory *)

(**  We define the set of shape functions and vertices for a finite element, as real-valued functions
   along with their derivatives and proofs of their properties: lagrangian w.r.t. the vertices,
   continuously differentiable.
*)

(* begin details : Require Imports and Open Scope, etc. *)
From mathcomp Require Import all_ssreflect ssralg ssrnum archimedean finfun.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
From CFEM Require Import matrix_util.
From Stdlib Require Import Lia FunctionalExtensionality.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.
(* end details *)

(** ** Definition of a package of real-valued shape functions.
*)
Section S.
(** In the mathematical components library, we don't talk about _the_ real numbers,
  we talk about any structure _R_ that satisfies the axioms of the reals. *)  
Context {R : realType}.

(** A function from #\(R^n\rightarrow R\)# is continuously differentiable if
   it is differentiable and its derivative (with respect to the i'th direction vector,
   for each i) is continuous.    We use column vectors ['cV[R]_n] to represent #\(R^n\)#.  *)
Definition continuously_differentiable [n] (f: 'cV[R]_n -> R) : Prop :=
  (forall x, differentiable f x) /\ forall i, continuous (derive f ^~ (delta_mx i 0)).

(** This predicate states that dθ really is the derivative of θ *)
Definition is_shape_deriv [d n] (θ : 'cV[R]_d -> 'rV[R]_n) (dθ: 'cV_d -> 'M[R]_(n,d)) :=
   forall x, dθ x =  \matrix_(i<n,j<d) 'D_(delta_mx j 0) θ x 0 i.

End S.


(** ** We enclose the [shape] record in a module #<a id=shape>#

   so that, outside the module, we can refer to
   [Shape.θ], [Shape.dθ], etc., and not pollute the namespace with identifiers θ, dθ, etc. *)
Module Shape.
Section S.
Context {R : realType}.

Record shape : Type := {
  d : nat;  (* number of dimensions of the finite element *)
  nsh: nat;  (* number of shape functions, also number of vertices *)
  θ: 'cV[R]_d -> 'rV[R]_nsh;  (* nsh shape functions, each #\(R^d\rightarrow R\)# *)
  dθ: 'cV[R]_d -> 'M[R]_(nsh,d);  (* derivatives of the shape functions *)
  vtx: 'M[R]_(d,nsh);   (* [nsh] vertices, each one a point in d-space *)
  lagrangian: forall i j, θ (col i vtx) 0 j  = if i==j then 1 else 0;  (* Lagrangian property: 
        The j'th shape function, applied to the i'th vertex, is 1 iff i=j. *)
  diff: forall j: 'I_nsh, continuously_differentiable (fun i => θ i 0 j);
  deriv: is_shape_deriv θ dθ  (* dθ really is the derivative of θ *)
}.

End S.
End Shape.

Section S.
Context {R : realType}.

(** *** Convex hull of a set of vertices *)

Definition convex_combination [d n] (vtx: 'M[R]_(d,n)) (y: 'cV_d) : Prop :=
   exists x: 'cV_n, (forall i, x i 0 >= 0)
  /\   col_mx vtx (const_mx (m:=1) 1)  *m x = col_mx y (const_mx 1).

Definition convex_hull [n d] (vtx: 'M[R]_(d,n)) : 'cV[R]_d -> Prop := 
        convex_combination vtx.

Definition convex_combination' [d n] (vtx: 'M[R]_(d,n)) (y: 'cV_d) : Prop :=
   exists x: 'cV_n, (forall i, x i 0 >= 0) 
                 /\  \sum_i x i 0 = 1
                 /\  vtx *m x = y.

Lemma convex_combination_e: forall d n vtx y, 
   @convex_combination d n vtx y <-> @convex_combination' d n vtx y.
(* begin details *)
Proof.
intros.
split; intros [x [H H0]]; exists x; split; auto.
-
rewrite mul_col_mx in H0.
apply eq_col_mx in H0.
destruct H0.
split; auto.
clear - H1.
match type of H1 with ?A = ?B => assert (A 0 0 = B 0 0) by congruence end.
rewrite !mxE in H.
etransitivity; [clear H | apply H].
apply eq_bigr => i Hi.
rewrite mxE mul1r //.
-
clear H.
destruct H0. subst y.
rewrite mul_col_mx.
f_equal.
apply matrixP.
intros i j.
rewrite !ord1. clear i j.
rewrite !mxE.
etransitivity; [clear H | apply H].
apply eq_bigr => i Hi.
rewrite mxE mul1r //.
Qed.
(* end details *)

(** *** Multivariate Polynomials are continuously differentiable *)

(** We do not assume that our shape functions are polynomials.  In practice, however,
  they usually are polynomials, and in that case we can take advantage of the
  properties of polynomials.  So first we define an inductive predicate to say that
   a given function from #\(R^n\rightarrow R\)# is indeed a (multivariate) polynomial. *)

Inductive is_multivariate_polynomial [d] : ('cV[R]_d -> R) -> Prop :=
| IMP_const: forall (c: R), is_multivariate_polynomial (fun _ => c)
| IMP_sum: forall a b, is_multivariate_polynomial a -> is_multivariate_polynomial b ->
            is_multivariate_polynomial (fun x => a x + b x)
| IMP_opp: forall a, is_multivariate_polynomial a -> 
            is_multivariate_polynomial (fun x => - a x)
| IMP_prod: forall a b, is_multivariate_polynomial a -> is_multivariate_polynomial b ->
            is_multivariate_polynomial (fun x => a x * b x)
| IMP_mono1: forall i j, is_multivariate_polynomial (fun x => x i j)
| IMP_mono: forall i j (k: nat), is_multivariate_polynomial (fun x => x i j ^ k).

(**  Next we will prove that any multivariate polynomial is continuously differentiable.
  We start with some helper lemmas. *)
Lemma derive_comp_mx: forall [n] (f: R -> Real.sort R), 
   (forall x, differentiable f x) ->
  forall i : 'I_n.+1, 
   'D_(delta_mx i 0) (f \o (fun m : 'cV[R]_n.+1 => m i 0)) = 
   ('D_1 f) \o  (fun m: 'cV[R]_n.+1 => m i 0).
(* begin details *)
Proof.
intros.
apply functional_extensionality => z.
set g := (fun _ => _).
assert (Hg: forall x, differentiable g x).
intro. subst g.
 apply differentiable_coord.
assert (Hfg: forall x, differentiable (f \o g) x).
 move => x. simpl in x.  apply differentiable_comp; auto.
simpl in *.
pose proof deriveE (1: Real.sort R) (H (g z)).
rewrite (deriveE (delta_mx i 0) (Hfg z)).
rewrite diff_comp; auto.
rewrite /comp.
rewrite -(deriveE (delta_mx i 0) (Hg z)).
replace ('D_(delta_mx i 0) g z) with (1: Real.sort R).
congruence.
clear - g Hg.
have @f : {linear 'cV[R]_n.+1 -> R}.
  by exists (fun N : 'cV[R]_( _) => N i 0); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
rewrite deriveE //.
change g with ( Linear.sort f).
rewrite diff_lin //.
subst f. simpl. rewrite mxE //.
simpl. rewrite eq_refl. reflexivity.
apply (@coord_continuous (Real.sort R)).
Qed.
(* end details *)

Lemma derive_comp_mx_neq: forall [n] (f: R -> Real.sort R), 
   (forall x, differentiable f x) ->
  forall i j : 'I_n.+1, 
   j != i ->
   'D_(delta_mx i 0) (f \o (fun m : 'cV[R]_n.+1 => m j 0)) = (fun=>0).
(* begin details *)
Proof.
intros.
apply functional_extensionality => z.
set g := (fun _ => _).
assert (Hg: forall x, differentiable g x).
intro. subst g.
 apply differentiable_coord.
assert (Hfg: forall x, differentiable (f \o g) x).
 move => x. simpl in x.  apply differentiable_comp; auto.
simpl in *.
pose proof deriveE (1: Real.sort R) (H (g z)).
rewrite (deriveE (delta_mx i 0) (Hfg z)).
rewrite diff_comp; auto.
rewrite /comp.
rewrite -(deriveE (delta_mx i 0) (Hg z)).
replace ('D_(delta_mx i 0) g z) with (0: Real.sort R).
2:{
rewrite deriveE; auto.
clear - g Hg H0.
have @f : {linear 'cV[R]_n.+1 -> R}.
  by exists (fun N : 'cV[R]_( _) => N j 0); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
change g with ( Linear.sort f).
rewrite diff_lin //.
subst f. simpl. rewrite mxE //.
destruct (j==i); try discriminate.
reflexivity.
apply (@coord_continuous (Real.sort R)).
}
rewrite linear0.
reflexivity.
Qed.
(* end details *)

(** Constant functions are continously differentiable *)
Lemma continuously_differentiable_cst: forall [d] c, @continuously_differentiable R d.+1 (fun=>c).
(* begin details *)
Proof.
split.
simpl. intro. apply differentiable_cst.
intro.
set j := ('D_ _ _). simpl in j.
replace j with (fun _:'cV[R]_d.+1 => @zero  (Real_sort__canonical__normed_module_NormedModule R)).
intro.
apply differentiable_continuous.
apply differentiable_cst.
symmetry.
simpl in i.
subst j.
change (fun=>c) with ((fun _: R => c) \o (fun m: 'cV[R]_d.+1 => m i 0)).
change (('D_1 (fun _:R =>c)) \o (fun r: 'cV[R]_d.+1 => r i 0) = fun=>0).
set f := (fun=>c).
assert (forall y, is_derive y (1:R) f 0%R).
move=> y;  apply: is_derive_eq.  auto.
extensionality x.
rewrite /comp.
specialize (H (x i 0)).
apply derive_val.
Qed.
(* end details *)

(** Functions from #\(R^0\rightarrow R\)# are continuously differentiable *)
Lemma continuously_differentiable_vacuous: forall f, @continuously_differentiable R O f.
(* begin details *)
intros.
assert (exists c, f = fun=>c).
  pose m := @const_mx R O 1 (0:R).
  exists (f m).
  extensionality x. destruct x. destruct m. f_equal. apply matrixP. intros i j. destruct i. lia.
destruct H as  [c H].
subst f.
split.  intro.
apply differentiable_cst.
simpl. intro. destruct i. lia.
Qed.
(* end details *)

(** If functions a(x) and b(x) are c.d., then so is (a+b)(x) *)
Lemma continuously_differentiable_add:
  forall [d] (a b: 'cV_d.+1 -> Real.sort R),
   continuously_differentiable a ->
   continuously_differentiable b ->
   continuously_differentiable (a \+ b)%E.
(* begin details *)
Proof.
intros.
destruct H as [Da Ca].
destruct H0 as [Db Cb].
simpl in *.
split; simpl; intros.
apply differentiableD; auto.
pose proof @derive_comp_mx d.
replace (fun _ => _) with (fun z : matrix (Real.sort R) (S d) 1 => add (derive a z (delta_mx i zero)) (derive b z (delta_mx i zero))).
2: extensionality z; rewrite deriveD //; apply diff_derivable; auto.
apply (@continuousD _ _ _ _ _ _ (Ca i x) (Cb i x)).
Qed.
(* end details *)

(** If functions a(x) and b(x) are c.d., then so is (a*b)(x) *)
Lemma continuously_differentiable_mul:
  forall [d] (a b: 'cV_d.+1 -> Real.sort R),
   continuously_differentiable a ->
   continuously_differentiable b ->
   continuously_differentiable (fun x => a x * b x).
(* begin details *)
Proof.
intros.
destruct H as [Da Ca].
destruct H0 as [Db Cb].
simpl in *.
split; simpl; intros.
apply differentiableM; auto.
pose proof @derive_comp_mx d.
replace (fun _ => _) with (fun z : matrix (Real.sort R) (S d) 1 =>  (a z *: 'D_(delta_mx i zero) b z + b z *: 'D_(delta_mx i zero) a z)%E).
2: extensionality z; rewrite deriveM //; apply diff_derivable; auto.
apply (@continuousD (reals_Real__to__Num_NumField R) (Real_sort__canonical__normed_module_NormedModule R)
  (@normed_module_NormedModule__to__topology_structure_Topological
     (Num_NumField__to__Num_NumDomain (reals_Real__to__Num_NumField R))
     (matrix_matrix__canonical__normed_module_NormedModule (reals_Real__to__Num_NumField R) (S d) (S O)))).
unfold scale.
simpl.
apply (@continuousM _ _ _ _ _ (differentiable_continuous (Da x)) (Cb i x)).
apply (@continuousM _ _ _ _ _ (differentiable_continuous (Db x)) (Ca i x)).
Qed.
(* end details *)

(** The function that simply selects the ith coordinate of a vector, is continuously differentiable *)
Lemma continously_differentiable_coord: 
  forall [d] (i: 'I_d.+1) (j: 'I_1),
continuously_differentiable (fun x : 'cV[R]_d.+1 => fun_of_matrix x i j).
(* begin details *)
Proof.
intros.
rewrite ord1. clear j.
split; simpl; intros.
apply differentiable_coord.
rename i0 into j.
destruct (j == i) eqn:?Hij.
-
change (is_true (j==i)) in Hij.
rewrite boolp.eq_opE in Hij; subst j.
pose proof @derive_comp_mx d id.
rewrite {1}/comp in H. rewrite H; auto.
apply continuous_comp.
apply (@coord_continuous (Real.sort R)).
assert (forall y, is_derive y (1 : R) id 1).
move=> y;  apply: is_derive_eq; auto.
simpl in H0.
red.
set y := fun_of_matrix _ _ _.
replace (fun _ => _) with (fun _: Real.sort R =>  (one (reals_Real__to__GRing_PzSemiRing R))).
apply cst_continuous.
extensionality u.
symmetry; apply (H0 u).
-
assert   (forall
     x : Filtered.sort
           (topology_structure_Topological__to__filter_Filtered
              (normed_module_NormedModule__to__topology_structure_Topological
                 (Real_sort__canonical__normed_module_NormedModule R))),
   differentiable id x).
clear.
simpl. intro.
replace (fun _ => _) with (@add (Real.sort R) 0).
2: extensionality z; apply add0r.
apply differentiableD; auto.
pose proof @derive_comp_mx_neq d id H j i.
unfold comp in H0.
rewrite H0.
clear.
apply differentiable_continuous.
apply differentiable_cst.
rewrite eq_sym Hij //.
Qed.
(* end details *)

(* begin details: Some utility lemmas to allow rewriting under the [differentiable] predicate, etc. *)
Lemma eq_differentiable: forall {K: numDomainType} {V W: normedModType K} 
   (f g: NormedModule.sort V -> NormedModule.sort W) x,
   f =1 g -> differentiable f x = differentiable g x.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.

Lemma eq_continuously_differentiable: forall {R: realType} [n]  (f g: ('cV_n -> Real.sort R) ),
   f =1 g -> continuously_differentiable f = continuously_differentiable g.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.

Lemma eq_locked_continuously_differentiable: forall {R: realType} [n] (f g: ('cV_n -> Real.sort R) ),
   f =1 g -> locked continuously_differentiable n f  = locked continuously_differentiable n g.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.
(* end details *)

(** The i'th variable, taken to the k'th power, is continuously differentiable *)
Lemma continuously_differentiable_variable_power: 
 forall [d] (i: 'I_d.+1) (j: 'I_1) (k: nat), 
    continuously_differentiable (fun x : 'cV[R]_d.+1 => x i j ^ Posz k).
(* begin details *)
Proof.
 induction k.
 +
  replace (fun _ => _) with (fun _: 'cV[R]_d.+1 => one R). 
  apply continuously_differentiable_cst.
  extensionality x. rewrite expr0z //.
 + 
 rewrite [continuously_differentiable]lock;
 under eq_locked_continuously_differentiable do [ rewrite exprSzr ];
 rewrite -lock.
 apply continuously_differentiable_mul; auto.
 apply continously_differentiable_coord.
Qed.
(* end details *)

(** Now we make use of all these individual lemmas, along with the inductive
   definition of a multivariate polynomial, to prove that any polynomial is
   continuously differentiable *)
Lemma multivariate_polynomial_continuously_differentiable: 
  forall [d] (f: 'cV[R]_d -> R),
  is_multivariate_polynomial f ->
  continuously_differentiable f.
Proof.
destruct d; [ intros; apply continuously_differentiable_vacuous | ].
induction 1.
- apply continuously_differentiable_cst.
- apply continuously_differentiable_add; auto.
- replace (fun _ => _) with (fun x: 'cV[R]_d.+1 => -1 * a x).
  apply continuously_differentiable_mul; auto.
  apply continuously_differentiable_cst.
  extensionality x. lra.
- apply continuously_differentiable_mul; auto.
- apply continously_differentiable_coord.
- apply continuously_differentiable_variable_power.
Qed.

End S.

(** *** Lemmas needed only until we switch to MathComp-Analysis 1.16 *)

(* begin details *)
Section pointwise_derivable.
Local Open Scope classical_set_scope.
Context  {R: realType}{V : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

(* The two admitted lemmas in this section are proved in 
   https://github.com/math-comp/analysis/pull/1829
  see also https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/Gradient.20components
*)

Lemma derivable_mxP: forall
   (M : NormedModule.sort V -> 'M[R]_(m, n))
   (t : Algebra.Zmodule.sort (normed_module_NormedModule__to__Algebra_Zmodule V))
   (v : GRing.LSemiModule.sort (normed_module_NormedModule__to__GRing_LSemiModule V)),
  derivable M t v <-> forall i j, derivable (fun x => M x i j) t v.
Admitted.

Lemma derive_mx: forall  [M : NormedModule.sort V -> 'M[R]_(m, n)]
  [t : Algebra.Zmodule.sort (normed_module_NormedModule__to__Algebra_Zmodule V)]
  [v : GRing.LSemiModule.sort (normed_module_NormedModule__to__GRing_LSemiModule V)],
derivable M t v ->
'D_v M t = \matrix_(i, j) 'D_v (fun t0 : NormedModule.sort V => fun_of_matrix (M t0) i j) t.
Admitted.

(* Delete this one after https://github.com/math-comp/analysis/pull/1891 is in a released mathcomp-analysis *)
Global Instance is_derive_mx (M : V -> 'M[R]_(m, n))
    (dM : 'M[R]_(m, n)) (x v : V) :
  (forall i j, is_derive x v (fun x => M x i j) (dM i j)) ->
  is_derive x v M dM.
Proof.
move=> MdM; apply: DeriveDef; first exact/derivable_mxP.
apply/matrixP => i j.
have [_ <-] := MdM i j.
rewrite derive_mx//.
  by rewrite mxE.
apply/derivable_mxP => i0 j0.
by have [] := MdM i0 j0.
Qed.

End pointwise_derivable.
(* end details *)

(** ** A whole bunch of supporting lemmas and proof-automation tactics *)

Ltac prove_continuously_differentiable :=
let j := fresh "j" in 
intro j; ord_enum_cases j;
lazymatch goal with
  | |- continuously_differentiable ?f =>
      let g := fresh "g" in let y := fresh "y" in 
      match type of f with ?t => evar (g: t) end;
     replace f with g; [ subst g |
      subst g; extensionality y;
      match goal with |- _ = fun_of_matrix (?f y) _ _ => unfold f end;
      try lazymatch goal with |- context [fun_of_matrix (?f (row _ _))] => unfold f end;
     simplify_ordinals;
      rewrite_matrix;
      reflexivity
    ]
end;
apply multivariate_polynomial_continuously_differentiable;
   repeat constructor.

Ltac derivable := 
repeat
match goal with
  | |- derivable (fun _ => ?a) _ _ => apply derivable_cst
  | |- derivable (fun _ => mul _ _) _ _ => apply derivableM 
  | |- derivable (fun _ => add _ _) _ _ => apply derivableD
  | |- derivable (fun _ => opp _) _ _ => apply derivableN 
  | |- derivable (fun _ => add _ (opp _)) _ _ => apply derivableB
  | |- derivable (fun _ => fun_of_matrix _ _ _) _ _ => apply derivable_mxP
  | |- derivable (fun x => x) _ _ => apply derivable_id
end.

Ltac compute_addn := 
repeat match goal with |- context C [addn ?x ?y] => let b := constr:(addn x y) in let c := eval compute in b in
   change b with c end.

Lemma trmxE : forall [T: Type] [m n: nat] (A: 'M[T]_(m,n)) i j, trmx A i j = A j i.
Proof. intros. apply mxE. Qed.

Lemma row__0: forall [T] [m n: nat] (A: 'M[T]_(m,n)) i j z, row j A z i = A j i.
Proof. intros. apply mxE. Qed.

Lemma col__0: forall [T] [m n: nat] (A: 'M[T]_(m,n)) i j z, col j A i z = A i j.
Proof. intros. apply mxE. Qed.

Section S.
Context {R : realType}.

Lemma is_derive_row: forall [n](x: 'cV_n.+1) (i j: 'I_n.+1),
  is_derive x (delta_mx i 0) (fun y: 'cV[R]_n.+1 => fun_of_matrix (row j y) 0 0) (if i==j then 1 else 0).
(* begin details *)
Proof.
intros.
replace (fun _ => _) with (fun A: 'cV[R]_n.+1 => A j ord0).
2: extensionality A; symmetry; apply row__0.
split.
-
apply diff_derivable.
apply differentiable_coord.
-
rewrite deriveE; [ | apply differentiable_coord].
have @f : {linear 'cV[R]_n.+1 -> R}.
  by exists (fun N : 'cV[R]_( _) => N j ord0); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
change (fun _ => fun_of_matrix _ _ _) with (Linear.sort f).
rewrite diff_lin.
simpl. rewrite mxE. simpl.
rewrite eq_sym. destruct (_ == _); auto.
apply (@coord_continuous (Real.sort R)).
Qed.
(* end details *)

Lemma is_derive_coord_simple:
 forall [n] (x: 'cV[R]_n) i j (z: 'I_1), is_derive x (delta_mx j 0) (fun y => y i z) (if i==j then 1 else 0).
(* begin details *)
Proof.
intros.
simpl.
split.
apply diff_derivable.
apply differentiable_coord.
-
rewrite deriveE; [ | apply differentiable_coord].
have @f : {linear 'cV[R]_n -> R}.
  by exists (fun N : 'cV[R]_( _) => N i z); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
change (fun _ => fun_of_matrix _ _ _) with (Linear.sort f).
rewrite diff_lin; [ | apply (@coord_continuous (Real.sort R))].
simpl. rewrite mxE. clear.
rewrite ?ord1.
simpl.
destruct (i==j); auto.
Qed.
(* end details *)
End S.

Ltac is_derive := repeat
( try simple apply is_derive_cst;
  match goal with
  | |- is_derive _ _ (fun _ => mul _ _) _ => apply is_deriveM  (* This takes longer than we might like *)
  | |- is_derive _ _ (fun _ => add _ (opp _)) _ => apply is_deriveB
  | |- is_derive _ _ (fun _ => add _ _) _ => apply is_deriveD
  | |- is_derive _ _ (fun _ => opp _) _ => apply is_deriveN
  | |- is_derive _ _ (fun=> _) _ =>  apply is_derive_cst
  | |- is_derive ?x _ (fun _ => fun_of_matrix (col _ _) _ _) _ => apply (is_derive_row x)
  | |- is_derive _ (delta_mx (Ordn _ 0) _)  _ _ => apply is_derive_coord_simple
  | |- is_derive _ (delta_mx _ (Ordn _ 0)) _ _ => apply is_derive_coord_simple
  | |- is_derive _ 'e__ _ _ => apply is_derive_coord_simple
 end).

Ltac test_I_n i := 
match type of i with
 | 'I_?n => let n := eval compute in n in is_ground_nat n
 | ?t =>  fail "Type of" i "is" t "but should be 'I_n where n is a constant"
end.

Ltac prove_lagrangian :=
let i := fresh "i" in let j := fresh "j" in intros i j;
test_I_n i; test_I_n j;
try match goal with 
| |- fun_of_matrix (?F (col i ?V)) 0 j =  if  i==j then _ else _ => rewrite /F /V
end;
simplify_ordinals;
rewrite_matrix;
ord_enum_cases i; rewrite_matrix;
 ord_enum_cases j; rewrite_matrix;
simpl; lra.

Ltac prove_deriv :=
let x := fresh "x" in intro x; symmetry;
compute_addn;
let i := fresh "i" in let j := fresh "j" in 
apply matrixP => i j; simpl in i, j;
match goal with |- _ ?A  => let a := fresh "a" in set a := A; rewrite mxE; subst a end;
repeat match goal with |- context [fun_of_matrix (?F (row _ _)) _ _] => unfold F end;
let f := fresh "f" in let g := fresh "g" in 
set (f := fun _ => _); simpl size in f;
match goal with |- _ = fun_of_matrix ?G _ _ =>
   assert (DERIV: is_derive x (delta_mx j 0) f (trmx (col j G)));
     [ | destruct DERIV as [_ Hval]; rewrite Hval trmxE col__0 //]
end;
subst f;
simplify_ordinals;
ord_enum_cases j;
rewrite_matrix; rewrite_matrix_under;
try (ord_enum_cases i; rewrite_matrix; rewrite_matrix_under);
try (ord_enum_cases j; rewrite_matrix; rewrite_matrix_under);
simpl map; simpl size;
  apply is_derive_mx; intros i j; compute in i,j; ord1;
 rewrite ?trmxE;
  ord_enum_cases j; rewrite_matrix; rewrite_matrix_under;
  simpl NormedModule.sort;
  (eapply is_derive_eq; [is_derive | simpl; repeat (progress change (scale ?A ?B) with (mul A B); simpl); lra]).

(** * Instances: shape-function-sets of various dimensions and degrees *)
Section S.
Context {R : realType}.

(** ** 1dP1:  1-dimension, degree 1 *)

(** The one-dimensional finite element with degree-1 polynomials has just two nodes:
<<
      -1                +1
      [0]--------------[1]
>>
*)

(** To make a shape-function-package, we first define the θ and dθ functions
     and the list of vertices.*)
Definition shapes1dP1_θ (xm: 'cV_1) : 'rV_(1 + 1) :=
    let x : R := xm 0 0 in rowmx_of_list [::   (1/2)*(1-x) ;   (1/2)*(1+x)].
Definition shapes1dP1_vertices : 'M[R]_(1,2) := mx_of_list [:: [:: -1; 1]].
Definition shapes1dP1_dθ (xm: 'cV[R]_1) : 'M[R]_(2,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: -1/2];  [:: 1/2]] : list (list (R))).

(**  Recall that a Shape.shape (defined above) starts with its dimension d, number of vertices nsh,
    then θ, dθ, and vtx; after that there are the proofs of its properties.  The [apply] here installs
    the data values, leaving the properties as proof obligations. *)
Definition shapes1dP1 : @Shape.shape R.
 (* begin show *)
  apply (Shape.Build_shape 1 2 shapes1dP1_θ shapes1dP1_dθ shapes1dP1_vertices).
(**  The individual proofs (lagrangian, cont. differentiable, and that dθ is actually the derivative of θ, are 
   all proved by Ltac scripts.  The scripts tend to do case analysis over 0..d and 0..nsh, sometimes
   nested 2 or 3 deep; so the proofs go very fast for 1dP1 but take much longer for 2dP2. *)
- abstract prove_lagrangian.   (* 0.064 seconds on Mac M2 *)
- abstract prove_continuously_differentiable.   (* 0.022 seconds *)
- abstract (unfold shapes1dP1_θ, shapes1dP1_dθ; prove_deriv).  (* 0.411 seconds*)
Defined.
 (* end show *)

(** ** 1dP2:  1-dimension, degree 2 *)
(**
<<
      -1                +1
      [0]------[1]------[2]
>>
*)
Definition shapes1dP2_vertices : 'M[R]_(1,3) := mx_of_list [:: [:: -1; 0; 1] ].
Definition shapes1dP2_θ (xm: 'rV_1) : 'rV_3 :=
    let x : R := xm 0 0 in rowmx_of_list [::   -(1/2)*(1-x)*x ;  (1-x)*(1+x);   (1/2)*x*(1+x)].
Definition shapes1dP2_dθ (xm: 'rV[R]_1) : 'M[R]_(3,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: -1/2*(1-2*x)];  [:: -2*x]; [:: 1/2*(1+2*x)]] : list (list (R))).

Definition shapes1dP2 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 1 3 shapes1dP2_θ shapes1dP2_dθ shapes1dP2_vertices).
- 
(**   There are three subgoals, the first of which is,
  [ forall i j : 'I_3, shapes1dP2_θ (col i shapes1dP2_vertices) 0 j = (if i == j then 1 else 0) ]
 which is the "Lagrangian" property.
 
 To demonstrate how these proofs go, this time we'll skip using the fully automated tactics,
  so instead of, [abstract prove_lagrangian]  we will do, *)
intros i j.
unfold shapes1dP2_θ, shapes1dP2_vertices.
simplify_ordinals.
(** Current proof goal, in which (Ordn 1 0) means, value 0 in the ordinal type ['I_1]:
<<
 i, j : 'I_3 
 ______________________________________(1/1)
 rowmx_of_list
   [:: - (1 / 2) * (1 - col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0)) *
      col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0);
      (1 - col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0)) *
      (1 + col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0))%E;
      1 / 2 * col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0) *
      (1 + col i (mx_of_list [:: [:: -1; 0; 1]]) (Ordn 1 0) (Ordn 1 0))%E]
  (Ordn 1 0) j =
( if i == j then 1 else 0)
>>
*)
rewrite_matrix.
(** Current proof goal: 
<<
i, j : 'I_3
______________________________________(1/1)
rowmx_of_list
  [:: - (1 / 2) * (1 - mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i) *
      mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i;
      (1 - mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i) *
      (1 + mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i)%E;
      1 / 2 * mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i *
      (1 + mx_of_list [:: [:: -1; 0; 1]] (Ordn 1 0) i)%E]
  (Ordn 1 0) j =
(if i == j then 1 else 0)
>>
*)
ord_enum_cases i; rewrite_matrix.
(** Now three subgoals, of which the first is,
<<
j : 'I_3
______________________________________(1/3)
rowmx_of_list [:: - (1 / 2) * (1 - -1) * -1; (1 - -1) * (1 - 1); 1 / 2 * -1 * (1 - 1)] (Ordn 1 0) j =
   (if Ordn 3 0 == j then 1 else 0)
>>
*)
all: ord_enum_cases j; rewrite_matrix.
(** Now nine subgoals, of which number 6 is,
<<
______________________________________(6/9)
1 / 2 * 0 * (1 + 0)%E = (if Ordn 3 1 == Ordn 3 2 then 1 else 0)
>>  
*)
all: simpl.
(** Now that subgoal is, [1 / 2 * 0 * (1 + 0) = 0]  *)
all: lra.  (* Solve these with the Linear Real Arithmetic decision procedure *)

-
(** The second goal is,
   [forall j : 'I_3, continuously_differentiable (fun i : 'cV_1 => shapes1dP2_θ i 0 j)]

  Now, we show the proof steps for,
     [ prove_continuously_differentiable.   ]  *)
unfold shapes1dP2_θ; 
intro j; ord_enum_cases j.
(**  Three subgoals, of which the first is,
<<
______________________________________(1/3)
continuously_differentiable
  (fun i : 'cV_1 =>
   rowmx_of_list
     [:: - (1 / 2) * (1 - i 0 0) * i 0 0; (1 - i 0 0) * (1 + i 0 0)%E;
         1 / 2 * i 0 0 * (1 + i 0 0)%E]
     0 (Ordn 3 0))
>>
*)
all: simplify_ordinals; rewrite_matrix_under.
(** Now the first subgoal is,
<<
 continuously_differentiable
    (fun y : 'cV_1 => - (1 / 2) * (1 - y (Ordn 1 0) (Ordn 1 0)) * y (Ordn 1 0) (Ordn 1 0))
>>
*)
all: apply multivariate_polynomial_continuously_differentiable.
(** Now the first subgoal is,
<<
 is_multivariate_polynomial
    (fun y : 'cV_1 => - (1 / 2) * (1 - y (Ordn 1 0) (Ordn 1 0)) * y (Ordn 1 0) (Ordn 1 0))
>>
 Finally, since [is_multivariate_polynomial] is an inductive predicate designed for
 proof automation, we can just write, *)
all: repeat constructor.

-  (** The third goal is,  [ is_shape_deriv shapes1dP2_θ shapes1dP2_dθ ]
  and let's see now the [prove_deriv] automation works. 
*)
unfold shapes1dP2_θ, shapes1dP2_dθ.
intro x; symmetry.
apply matrixP => i j; simpl in i, j.
rewrite mxE.
set (f := fun _ => _); simpl size in f.
(** Now we have the goal,
<<
i : 'I_3
j : 'I_1
f := fun x : 'cV_1 => 
    rowmx_of_list [:: - (1 / 2) * (1 - x 0 0) * x 0 0; (1 - x 0 0) * (1 + x 0 0); 1 / 2 * x 0 0 * (1 + x 0 0)]
______________________________________(1/1)
('D_(delta_mx j 0) f x) 0 i =
mx_of_list [:: [:: -1 / 2 * (1 - 2 * x 0 0)]; [:: -2 * x 0 0]; [:: 1 / 2 * (1 + (2 * x 0 0))%E]] i j
>>
*)
match goal with |- _ = fun_of_matrix ?G _ _ =>
   assert (DERIV: is_derive x (delta_mx j 0) f (trmx (col j G)))
end.
(** The mathcomp.analysis library's [is_derive x d f g] says that g is the first derivative of f,
  in the 'd' direction, evaluated at x.  In the current case, the "direction" is (delta_mx j 0), 
   meaning, the partial derivative along the j'th coordinate.
*)
+
(**  The assertion we have to prove is,
<<
 is_derive x (delta_mx j 0) f
  (col j  (mx_of_list [:: [:: -1 / 2 * (1 - 2 * x 0 0)]; 
                          [:: -2 * x 0 0];
                          [:: 1 / 2 * (1%R + (2 * x 0 0))]]))^T
>>
 with [f] defined as above.  We will prove this by case analysis on i and j.
  The case analysis on j is trivial, since j must be 0.
*)
subst f;
simplify_ordinals;
ord_enum_cases j; rewrite_matrix; rewrite_matrix_under;
ord_enum_cases i; rewrite_matrix; rewrite_matrix_under;
simpl map; simpl size.
(** Now, each of the three cases (for i=0,1,2) is a claim about the derivative of a 1x3 matrix:
<<
x : 'cV_1
______________________________________(1/3)
is_derive x (delta_mx (Ordn 1 0) (Ordn 1 0))
  (fun x : 'cV_1 =>
   rowmx_of_list
     [:: - (1 / 2) * (1 - x (Ordn 1 0) (Ordn 1 0)) * x (Ordn 1 0) (Ordn 1 0);
         (1 - x (Ordn 1 0) (Ordn 1 0)) * (1 + x (Ordn 1 0) (Ordn 1 0))%E;
         1 / 2 * x (Ordn 1 0) (Ordn 1 0) * (1 + x (Ordn 1 0) (Ordn 1 0))%E])
  ((rowmx_of_listn
      [:: -1 / 2 * (1 - 2 * x (Ordn 1 0) (Ordn 1 0)); -2 * x (Ordn 1 0) (Ordn 1 0);
          1 / 2 * (1 + (2 * x (Ordn 1 0) (Ordn 1 0)))%E])^T)^T
>>
We use a lemma to break this down into its 1x3 components:
*)
all: apply is_derive_mx.
(** Now, in each of our 3 subgoals, do case analysis on the 3 components: *)
all: intros i j; rewrite trmxE; ord_enum_cases i; ord_enum_cases j; rewrite_matrix; rewrite_matrix_under.
(** Now the typical subgoal looks like this,
<<
______________________________________(1/9)
is_derive x (delta_mx (Ordn 1 0) (Ordn 1 0))
  (fun y : matrix_matrix__canonical__normed_module_NormedModule R 1 1 =>
   - (1 / 2) * (1 - y (Ordn 1 0) (Ordn 1 0)) * y (Ordn 1 0) (Ordn 1 0))
  ((rowmx_of_listn
      [:: -1 / 2 * (1 - 2 * x (Ordn 1 0) (Ordn 1 0)); -2 * x (Ordn 1 0) (Ordn 1 0);
          1 / 2 * (1 + (2 * x (Ordn 1 0) (Ordn 1 0)))%E])^T
     (Ordn 3 0) (Ordn 1 0))
>>
*)

(** In each of the 9 cases, we can use the [is_derive] proof automation to calculate
 the derivative: *)
all: eapply is_derive_eq; [ is_derive |  simpl; rewrite_matrix; rewrite_matrix_under ].
(* This leaves subgoals like, 
<<
______________________________________(1/9)
((- (1 / 2) * (1 - x (Ordn 1 0) (Ordn 1 0)))%:A +
 x (Ordn 1 0) (Ordn 1 0) *:
 (- (1 / 2) *: (0 - 1) + (1 - x (Ordn 1 0) (Ordn 1 0)) *: - (1 *: 0 + 2^-1 *: 0)%E)%E)%E =
-1 / 2 * (1 - 2 * x (Ordn 1 0) (Ordn 1 0))
>>
We can see it more clearly after,
*)
all: set x00 := x _ _; clearbody x00; clear x; simpl in x00.
Check scale.
(** The notation  [a *: b] is for scaling ring-element [b] by scalar [a].  Since in this case the ring is just the reals,
   that's the same as ordinary multiplication, so let's change it that way: *)
all: repeat change (scale ?A ?B) with (mul A B); simpl.
(** Finally, all of these 9 equations can be solved by the decision procedure for Linear Real Arithmetic *)
all: lra.
+
(** We have finished proving the [assert (DERIV:  is_derive x (delta_mx j 0) f (trmx (col j G)))].
  Now it's time to use that assertion to prove the main goal, which is, 
<<
  ('D_(delta_mx j 0) f x) 0 i =
    mx_of_list [:: [:: -1 / 2 * (1 - 2 * x 0 0)]; [:: -2 * x 0 0]; [:: 1 / 2 * (1 + (2 * x 0 0))%E]] i j
>>
*)
destruct DERIV as [_ Hval].
(** Now we have,
<<
 i: 'I_3
 j: 'I_1
 Hval :
  'D_(delta_mx j 0) f x =
  (col j  (mx_of_list
        [:: [:: -1 / 2 * (1 - 2 * x 0 0)]; [:: -2 * x 0 0]; [:: 1 / 2 * (1 + (2 * x 0 0))%E]]))^T 
>>
Clearly this is quite useful in proving the goal:
*)
rewrite Hval trmxE col__0 //.
(** And we're done proving all the properties of shapes1dP2 *)
Defined.
 (* end show *)

(** ** 1dP3:  1-dimension, degree 3 *)

(**
<<
      -1                      +1
      [0]-----[1]-----[2]-----[3]
>>
*)

Definition shapes1dP3_vertices : 'M[R]_(1,4) := mx_of_list [::  [:: -1; -1/3; 1/3; 1]].
Definition shapes1dP3_θ (xm: 'rV_1) : 'rV_4 :=
  let x: R := xm 0 0 in
   rowmx_of_list [::  -(1/16)*(1-x)*(1-3*x)*(1+3*x);  
                                   9/16*(1-x)*(1-3*x)*(1+x); 
                                   9/16*(1-x)*(1+3*x)*(1+x);
                                -(1/16)*(1-3*x)*(1+3*x)*(1+x) ].
Definition shapes1dP3_dθ (xm: 'rV[R]_1) : 'M[R]_(4,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: 1/16 * (1 + x*(18 + x*(-27)) )];  
                          [:: 9/16 * (-3 + x*(-2 + x*9)) ]; 
                          [:: 9/16 * (3 + x*(-2 + x*(-9))) ]; 
                          [:: 1/16 * (-1 + x*(18 + x*27) )]] : list (list (R))).

Definition shapes1dP3 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 1 4 shapes1dP3_θ shapes1dP3_dθ shapes1dP3_vertices).
- abstract prove_lagrangian.  (* 0.407 seconds *)
- abstract prove_continuously_differentiable.  (* 0.081 seconds *)
- abstract (unfold shapes1dP3_θ, shapes1dP3_dθ; prove_deriv).  (* 4.339 seconds *)
Defined.
 (* end show *)

(** ** 2dP1:  2-dimensional cuboid, degree 1 #<a id=2dP1># *)
(** A two-dimensional equilateral cuboid is also known as a "square".
<<
      -1            +1
+1   [3]-----------[2]
      |             |
      |             |
      |             |
-1   [0]-----------[1]
>>
*)

Definition shapes2dP1_vertices : 'M[R]_(2,4) :=
   mx_of_list ([:: [:: -1; 1; 1; -1];
                        [:: -1; -1; 1; 1]]: list (list R)).

Definition shapes2dP1_θ (xy: 'cV[R]_2) : 'rV[R]_4 :=
   let Nx : 'rV_2 := shapes1dP1_θ (row 0 xy) in
   let Ny : 'rV_2 := shapes1dP1_θ (row 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 1 * Ny 0 1 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dP1_dθ (xm: 'cV[R]_2) : 'M[R]_(4,2) :=
  let Nx := shapes1dP1_θ (row 0 xm) in
  let dNx := shapes1dP1_dθ (row 0 xm) in
  let Ny := shapes1dP1_θ (row 1 xm) in
  let dNy := shapes1dP1_dθ (row 1 xm) in
  let x := xm 0 0 in let y := xm 1 0 in
  mx_of_list ([:: [:: dNx 0 0 * Ny 0 0 ; Nx 0 0 * dNy 0 0 ];
                         [:: dNx 1 0 * Ny 0 0 ; Nx 0 1 * dNy 0 0 ];
                         [:: dNx 1 0 * Ny 0 1 ; Nx 0 1 * dNy 1 0 ];
                         [:: dNx 0 0 * Ny 0 1 ; Nx 0 0 * dNy 1 0 ]]: list (list R)).

(** Real-valued functional model of 2dP1 element *)
Definition shapes2dP1 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 2 4 shapes2dP1_θ shapes2dP1_dθ shapes2dP1_vertices).
- abstract (unfold shapes2dP1_θ, shapes1dP1_θ, shapes2dP1_vertices; 
                  prove_lagrangian).  (* 0.4 seconds *)
- abstract prove_continuously_differentiable. (* 0.249 seconds *)
- time "prove_deriv 2dP1" abstract (unfold shapes2dP1_θ, shapes2dP1_dθ, shapes1dP1_θ, shapes1dP1_dθ;
                     prove_deriv).  (* 7.07 seconds *)
Defined. 
 (* end show *)

(** ** 2dT1:  2-dimensional simplex, degree 1 *)
(** A two-dimensional simplex is also known as a "triangle".
<<
      0      1
1   [2]
      | \
      |   \
      |     \
0   [0]-----[1]
>>
*)

Definition shapes2dT1_vertices : 'M[R]_(2,3) := 
    mx_of_list [:: [:: 0; 1; 0];
                          [:: 0; 0; 1]].

Definition shapes2dT1_θ (xy: 'cV[R]_2) : 'rV[R]_3 :=
   let x : R := xy 0 0 in
   let y : R := xy 1 0 in
   rowmx_of_list [:: 1-x-y; x; y]. 

Definition shapes2dT1_dθ (xm: 'cV[R]_2) : 'M[R]_(3,2) :=
  let x := xm 0 0 in let y := xm 1 0 in
  mx_of_list ([:: [:: -1 ; -1 ];
                         [:: 1 ; 0 ];
                         [:: 0 ; 1]]: list (list R)).

Definition shapes2dT1 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 2 3 shapes2dT1_θ shapes2dT1_dθ shapes2dT1_vertices).
- abstract prove_lagrangian.  (* 0.128 seconds *)
- abstract prove_continuously_differentiable.  (* 0.129 seconds *)
- abstract (unfold shapes2dT1_θ, shapes2dT1_dθ; prove_deriv).  (* 0.566 seconds *)
Defined.
 (* end show *)

(** ** 2dP2:  2-dimensional cuboid, degree 2, with center vertix *)
(**
<<
      -1            +1
+1   [6]----[5]----[4]
      |      |      |
     [7]----[8]----[3]
      |      |      |
-1   [0]----[1]----[2]
>>
*)

Definition shapes2dP2_vertices : 'M[R]_(2,9) := 
   mx_of_list [:: [:: -1; 0; 1; 1; 1; 0; -1; -1; 0];
                         [:: -1; -1; -1; 0; 1; 1; 1; 0; 0]].

Definition shapes2dP2_θ (xy: 'cV[R]_2) : 'rV[R]_9 :=
   let Nx : 'rV_3 := shapes1dP2_θ (row 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_θ (row 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ; Nx 0 1 * Ny 0 1 ].

Definition shapes2dP2_dθ (xy: 'cV[R]_2) : 'M[R]_(9,2) :=
   let Nx : 'rV_3 := shapes1dP2_θ (row 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_θ (row 1 xy) in
   let dNx : 'cV_3 := shapes1dP2_dθ (row 0 xy) in
   let dNy : 'cV_3 := shapes1dP2_dθ (row 1 xy) in
  mx_of_list [:: [:: dNx 0 0 * Ny 0 0; Nx 0 0 * dNy 0 0];
                        [:: dNx 1 0 * Ny 0 0; Nx 0 1 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 0; Nx 0 2 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 1; Nx 0 2 * dNy 1 0];
                        [:: dNx 2 0 * Ny 0 2; Nx 0 2 * dNy 2 0];
                        [:: dNx 1 0 * Ny 0 2; Nx 0 1 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 2; Nx 0 0 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 1; Nx 0 0 * dNy 1 0];
                        [:: dNx 1 0 * Ny 0 1; Nx 0 1 * dNy 1 0]].

Definition shapes2dP2 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 2 9 shapes2dP2_θ shapes2dP2_dθ shapes2dP2_vertices).
- time "lagrangian" abstract (unfold shapes2dP2_θ,  shapes1dP2_θ, shapes2dP2_vertices;
                                           prove_lagrangian).   (* 6.756 seconds *)
- time "cont_diff" abstract prove_continuously_differentiable.  (* 2.197 seconds *)
- time "is_deriv" abstract (unfold shapes2dP2_θ, shapes2dP2_dθ, shapes1dP2_θ, shapes1dP2_dθ;
                  prove_deriv).  (* 70.085 seconds *)
Defined.
 (* end show *)

(** ** 2dS2:  2-dimensional cuboid, degree 2, without center vertix (Serendipity element) *)(**
<<
      -1            +1
+1   [6]----[5]----[4]
      |             |
     [7]           [3]
      |             |
-1   [0]----[1]----[2]
>>
*)
Definition shapes2dS2_vertices : 'M[R]_(2,8) := 
   mx_of_list [:: [:: -1; 0; 1; 1; 1; 0; -1; -1];
                         [:: -1; -1; -1; 0; 1; 1; 1; 0]].

Definition shapes2dS2_θ (xy: 'cV[R]_2) : 'rV[R]_8 :=
   let Nx : 'rV_3 := shapes1dP2_θ (row 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_θ (row 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dS2_dθ (xy: 'cV[R]_2) : 'M[R]_(8,2) :=
   let Nx : 'rV_3 := shapes1dP2_θ (row 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_θ (row 1 xy) in
   let dNx : 'cV_3 := shapes1dP2_dθ (row 0 xy) in
   let dNy : 'cV_3 := shapes1dP2_dθ (row 1 xy) in
  mx_of_list [:: [:: dNx 0 0 * Ny 0 0; Nx 0 0 * dNy 0 0];
                        [:: dNx 1 0 * Ny 0 0; Nx 0 1 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 0; Nx 0 2 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 1; Nx 0 2 * dNy 1 0];
                        [:: dNx 2 0 * Ny 0 2; Nx 0 2 * dNy 2 0];
                        [:: dNx 1 0 * Ny 0 2; Nx 0 1 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 2; Nx 0 0 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 1; Nx 0 0 * dNy 1 0]].

Definition shapes2dS2 : @Shape.shape R.
 (* begin show *)
apply (Shape.Build_shape 2 8 shapes2dS2_θ shapes2dS2_dθ shapes2dS2_vertices).
- time "lagrangian 2dS2" abstract (unfold shapes2dS2_θ,  shapes1dP2_θ, shapes2dS2_vertices;
                                           prove_lagrangian).  (* 3.941 seconds *)
- time "cont_diff 2dS2" abstract prove_continuously_differentiable.  (* 1.718 seconds *)
- time "is_deriv 2dS2" abstract (unfold shapes2dS2_θ, shapes2dS2_dθ, shapes1dP2_θ, shapes1dP2_dθ;
                  prove_deriv).   (* 51.687 seconds *)
Defined.
 (* end show *)

End S.
