 (** * CFEM.shape:  Lagrange shape functions, and some supporting theory *)

(** Right now, this file has a melange of supporting definitions, useful lemmas, proof automation,
  as well as the real-valued functional models of some shape functions from ../src/shapes.c 
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum archimedean finfun.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory.
From CFEM Require Import matrix_util.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

From mathcomp.algebra_tactics Require Import ring lra.

Section S.  
Context {R : realType}.

Definition continuously_differentiable [n] (f: 'rV[R]_n -> R) : Prop :=
  (forall x, differentiable f x) /\ forall i, continuous (derive f ^~ ('e_i)).

Definition convex_combination' [d n] (vtx: 'M[R]_(d,n)) (y: 'cV_d) : Prop :=
   exists x: 'cV_n, (forall i, x i 0 >= 0) 
                              /\  \sum_i x i 0 = 1
                              /\  vtx *m x = y.

Definition convex_combination [d n] (vtx: 'M[R]_(d,n)) (y: 'cV_d) : Prop :=
   exists x: 'cV_n, (forall i, x i 0 >= 0)
  /\   col_mx vtx (const_mx (m:=1) 1)  *m x = col_mx y (const_mx 1).

Lemma convex_combination_e: forall d n vtx y, 
   @convex_combination d n vtx y <-> @convex_combination' d n vtx y.
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

Definition convex_hull [n d] (vtx: 'M[R]_(d,n)) := sig (convex_combination vtx).


Definition is_shape_deriv [d n] (θ : 'rV[R]_d -> 'rV[R]_n) (dθ: 'rV_d -> 'M[R]_(n,d)) :=
   forall x, dθ x =  \matrix_(i<n,j<d) 'D_('e_j) θ x 0 i.

End S.

Import GRing.

Module Shape.
Section S.
Context {R : realType}.

Record shape : Type := {
  d : nat;
  nsh: nat;
  θ: 'rV_d -> 'rV_nsh;  (* nsh shape functions, each R^d->R *)
  dθ: 'rV_d -> 'M[R]_(nsh,d);
  vtx: 'M[R]_(nsh,d); 
  K  := convex_hull vtx;
  lagrangian: forall i j, θ (row i vtx) 0 j  = if i==j then 1 else 0;
  diff: forall j: 'I_nsh, continuously_differentiable (fun i => θ i 0 j);
  deriv: is_shape_deriv θ dθ
}.

End S.
End Shape.

From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Lemma eq_differentiable: forall {K: numDomainType} {V W: normedModType K} 
   (f g: NormedModule.sort V -> NormedModule.sort W) x,
   f =1 g -> differentiable f x = differentiable g x.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.

Lemma eq_continuously_differentiable: forall {R: realType} [n]  (f g: ('rV_n -> Real.sort R) ),
   f =1 g -> continuously_differentiable f = continuously_differentiable g.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.


Lemma eq_locked_continuously_differentiable: forall {R: realType} [n] (f g: ('rV_n -> Real.sort R) ),
   f =1 g -> locked continuously_differentiable n f  = locked continuously_differentiable n g.
Proof.
intros.
assert (f=g) by (apply functional_extensionality; auto).
subst; auto.
Qed.

Section S.
Context {R : realType}.

Lemma derive_comp_mx: forall [n] (f: R -> Real.sort R), 
   (forall x, differentiable f x) ->
  forall i : 'I_n.+1, 
   'D_('e_i) (f \o (fun m : 'rV[R]_n.+1 => m 0 i)) = ('D_1 f) \o  (fun m: 'rV[R]_n.+1 => m 0 i).
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
rewrite (deriveE ('e_i) (Hfg z)).
rewrite diff_comp; auto.
rewrite /comp.
rewrite -(deriveE ('e_i) (Hg z)).
replace ('D_('e_i) g z) with (1: Real.sort R).
congruence.
clear - g Hg.
have @f : {linear 'rV[R]_n.+1 -> R}.
  by exists (fun N : 'rV[R]_( _) => N 0 i); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
rewrite deriveE //.
change g with ( Linear.sort f).
rewrite diff_lin //.
subst f. simpl. rewrite mxE //.
simpl. rewrite eq_refl. reflexivity.
apply (@coord_continuous (Real.sort R)).
Qed.

Lemma derive_comp_mx_neq: forall [n] (f: R -> Real.sort R), 
   (forall x, differentiable f x) ->
  forall i j : 'I_n.+1, 
   j != i ->
   'D_('e_i) (f \o (fun m : 'rV[R]_n.+1 => m 0 j)) = (fun=>0).
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
rewrite (deriveE ('e_i) (Hfg z)).
rewrite diff_comp; auto.
rewrite /comp.
rewrite -(deriveE ('e_i) (Hg z)).
replace ('D_('e_i) g z) with (0: Real.sort R).
2:{
rewrite deriveE; auto.
clear - g Hg H0.
have @f : {linear 'rV[R]_n.+1 -> R}.
  by exists (fun N : 'rV[R]_( _) => N 0 j); do 2![eexists]; do ?[constructor];
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


Definition at00 (m: 'cV[R]_1) := m 0 0.

Lemma derive_comp_mx1: forall (f: Real.sort R -> Real.sort R), 
   (forall x, differentiable f x) ->
   'D_(1%:M) (f \o at00) = ('D_1 f) \o  at00.
Proof.
intros.
etransitivity; [ etransitivity; [ | apply (@derive_comp_mx 0 f H ord0)] | reflexivity ].
extensionality x. f_equal. apply matrixP. intros i j; rewrite !ord1 !mxE; auto.
Qed.

Inductive is_multivariate_polynomial [d] : ('rV[R]_d -> R) -> Prop :=
| IMP_const: forall (c: R), is_multivariate_polynomial (fun _ => c)
| IMP_sum: forall a b, is_multivariate_polynomial a -> is_multivariate_polynomial b ->
            is_multivariate_polynomial (fun x => a x + b x)
| IMP_opp: forall a, is_multivariate_polynomial a -> 
            is_multivariate_polynomial (fun x => - a x)
| IMP_prod: forall a b, is_multivariate_polynomial a -> is_multivariate_polynomial b ->
            is_multivariate_polynomial (fun x => a x * b x)
| IMP_mono1: forall i j, is_multivariate_polynomial (fun x => x i j)
| IMP_mono: forall i j (k: nat), is_multivariate_polynomial (fun x => x i j ^ k).

Lemma continuously_differentiable_cst: forall [d] c, @continuously_differentiable R d.+1 (fun=>c).
Proof.
split.
simpl. intro. apply differentiable_cst.
intro.
set j := ('D_ _ _). simpl in j.
replace j with (fun _:'rV[R]_d.+1 => @zero  (Real_sort__canonical__normed_module_NormedModule R)).
intro.
apply differentiable_continuous.
apply differentiable_cst.
symmetry.
simpl in i.
subst j.
change (fun=>c) with ((fun _: R => c) \o (fun m: 'rV[R]_d.+1 => m 0 i)).
change (('D_1 (fun _:R =>c)) \o (fun r: 'rV[R]_d.+1 => r 0 i) = fun=>0).
set f := (fun=>c).
assert (forall y, is_derive y (1:R) f 0%R).
move=> y;  apply: is_derive_eq.  auto.
extensionality x.
rewrite /comp.
specialize (H (x 0 i)).
apply derive_val.
Qed.

Lemma continuously_differentiable_vacuous: forall f, @continuously_differentiable R O f.
intros.
assert (exists c, f = fun=>c).
  pose m := @const_mx R 1 O (0:R).
  exists (f m).
  extensionality x. destruct x. destruct m. f_equal. apply matrixP. intros i j. destruct j. lia.
destruct H as  [c H].
subst f.
split.  intro.
apply differentiable_cst.
simpl. intro. destruct i. lia.
Qed.

Lemma continuously_differentiable_add:
  forall [d] (a b: 'rV_d.+1 -> Real.sort R),
   continuously_differentiable a ->
   continuously_differentiable b ->
   continuously_differentiable (a \+ b)%E.
Proof.
intros.
destruct H as [Da Ca].
destruct H0 as [Db Cb].
simpl in *.
split; simpl; intros.
apply differentiableD; auto.
pose proof @derive_comp_mx d.
replace (fun _ => _) with (fun z : matrix (Real.sort R) 1 (S d) => add (derive a z (delta_mx zero i)) (derive b z (delta_mx zero i))).
2: extensionality z; rewrite deriveD //; apply diff_derivable; auto.
apply (@continuousD _ _ _ _ _ _ (Ca i x) (Cb i x)).
Qed.

Lemma continuously_differentiable_mul:
  forall [d] (a b: 'rV_d.+1 -> Real.sort R),
   continuously_differentiable a ->
   continuously_differentiable b ->
   continuously_differentiable (fun x => a x * b x).
Proof.
intros.
destruct H as [Da Ca].
destruct H0 as [Db Cb].
simpl in *.
split; simpl; intros.
apply differentiableM; auto.
pose proof @derive_comp_mx d.
replace (fun _ => _) with (fun z : matrix (Real.sort R) 1 (S d) =>  (a z *: 'D_'e_i b z + b z *: 'D_'e_i a z)%E).
2: extensionality z; rewrite deriveM //; apply diff_derivable; auto.
apply (@continuousD (reals_Real__to__Num_NumField R) (Real_sort__canonical__normed_module_NormedModule R)
  (@normed_module_NormedModule__to__topology_structure_Topological
     (Num_NumField__to__Num_NumDomain (reals_Real__to__Num_NumField R))
     (matrix_matrix__canonical__normed_module_NormedModule (reals_Real__to__Num_NumField R) (S O) (S d)))).
unfold scale.
simpl.
apply (@continuousM _ _ _ _ _ (differentiable_continuous (Da x)) (Cb i x)).
apply (@continuousM _ _ _ _ _ (differentiable_continuous (Db x)) (Ca i x)).
Qed.

Lemma continously_differentiable_coord: 
  forall [d] (i: 'I_1) (j: 'I_d.+1),
continuously_differentiable (fun x : 'rV[R]_d.+1 => fun_of_matrix x i j).
Proof.
intros.
rewrite ord1. clear i.
rename j into i.
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

Lemma multivariate_polynomial_continuously_differentiable: 
  forall [d] (f: 'rV[R]_d -> R),
  is_multivariate_polynomial f ->
  continuously_differentiable f.
Proof.
destruct d; [ intros; apply continuously_differentiable_vacuous | ].
induction 1.
- apply continuously_differentiable_cst.
- apply continuously_differentiable_add; auto.
- replace (fun _ => _) with (fun x: 'rV[R]_d.+1 => -1 * a x).
  apply continuously_differentiable_mul; auto.
  apply continuously_differentiable_cst.
  extensionality x. lra.
- apply continuously_differentiable_mul; auto.
- apply continously_differentiable_coord.
- induction k.
 +
  replace (fun _ => _) with (fun _: 'rV[R]_d.+1 => one R). 
  apply continuously_differentiable_cst.
  extensionality x. rewrite expr0z //.
 + 
 rewrite [continuously_differentiable]lock;
 under eq_locked_continuously_differentiable do [ rewrite exprSzr ];
 rewrite -lock.
 apply continuously_differentiable_mul; auto.
 apply continously_differentiable_coord.
Qed.

End S.

Ltac rewrite_matrix_under :=
 let f := fresh "f" in let g := fresh "g" in let y := fresh "y" in 
 try
  (lazymatch goal with
   | |- context [fun _ => fun_of_matrix _ _ _] =>  set f := (fun _ => fun_of_matrix _ _ _)
   | |- context [fun _ => row_mx _ _] =>  set f := (fun _ => row_mx _ _)
   | |- context [fun _ => rowmx_of_list _] =>  set f := (fun _ => rowmx_of_list _)
  end;
  lazymatch type of f with ?t => evar (g: t) end;
    replace f with g by (subst f g; extensionality y; rewrite_matrix1; rewrite_matrix; reflexivity);
    subst g; clear f).

Ltac simplify_ordinals :=
      repeat match goal with
      | |- context [fun_of_matrix _ ?i _] => simplify_ordinal i
      | |- context [fun_of_matrix _ _ ?j] => simplify_ordinal j
      | |- context [col ?i _] => simplify_ordinal i
      | |- context [row ?i _] => simplify_ordinal i
     end.

Ltac prove_continuously_differentiable :=
let j := fresh "j" in 
intro j; ord_enum_cases j; clear j;
lazymatch goal with
  | |- continuously_differentiable ?f =>
      let g := fresh "g" in let y := fresh "y" in 
      match type of f with ?t => evar (g: t) end;
     replace f with g; [ subst g |
      subst g; extensionality y;
      match goal with |- _ = fun_of_matrix (?f y) _ _ => unfold f end;
      try lazymatch goal with |- context [fun_of_matrix (?f (col _ _))] => unfold f end;
     simplify_ordinals;
      rewrite_matrix;
      reflexivity
    ]
end;
apply multivariate_polynomial_continuously_differentiable;
   repeat constructor.

Ltac test_I_n i := 
match type of i with
 | 'I_?n => let n := eval compute in n in is_ground_nat n
 | ?t =>  fail "Type of" i "is" t "but should be 'I_n where n is a constant"
end.

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
Proof.
intros. apply mxE.
Qed.

Lemma row__0: forall [T] [m n: nat] (A: 'M[T]_(m,n)) i j z, row j A z i = A j i.
Proof.
intros.
apply mxE.
Qed.

Lemma col__0: forall [T] [m n: nat] (A: 'M[T]_(m,n)) i j z, col j A i z = A i j.
Proof.
intros.
apply mxE.
Qed.

Section S.
Context {R : realType}.

Lemma is_derive_col: forall [n](x: 'rV_n.+1) (i j: 'I_n.+1),
  is_derive x 'e_i (fun y: 'rV[R]_n.+1 => fun_of_matrix (col j y) 0 0) (if i==j then 1 else 0).
Proof.
intros.
replace (fun _ => _) with (fun A: 'rV[R]_n.+1 => A ord0 j).
2: extensionality A; symmetry; apply col__0.
split.
-
apply diff_derivable.
apply differentiable_coord.
-
rewrite deriveE; [ | apply differentiable_coord].
have @f : {linear 'rV[R]_n.+1 -> R}.
  by exists (fun N : 'rV[R]_( _) => N ord0 j); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
change (fun _ => fun_of_matrix _ _ _) with (Linear.sort f).
rewrite diff_lin.
simpl. rewrite mxE. simpl.
rewrite eq_sym. destruct (_ == _); auto.
apply (@coord_continuous (Real.sort R)).
Qed.


Lemma is_derive_coord_simple:
 forall [n] (x: 'rV[R]_n) i j (z: 'I_1), is_derive x 'e_j (fun y => y z i) (if i==j then 1 else 0).
Proof.
intros.
simpl.
split.
apply diff_derivable.
apply differentiable_coord.
-
rewrite deriveE; [ | apply differentiable_coord].
have @f : {linear 'rV[R]_n -> R}.
  by exists (fun N : 'rV[R]_( _) => N z i); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
change (fun _ => fun_of_matrix _ _ _) with (Linear.sort f).
rewrite diff_lin; [ | apply (@coord_continuous (Real.sort R))].
simpl. rewrite mxE. clear.
rewrite ?ord1.
simpl.
destruct (i==j); auto.
Qed.
End S.

Ltac showgoal := 
 match goal with |- is_derive _ _ ?A _ => idtac "Showgoal:" A end.

Ltac is_derive := repeat
( try simple apply is_derive_cst;
  match goal with
  | |- is_derive _ _ (fun _ => mul _ _) _ => 
       (* time "M" *) apply is_deriveM  (* This takes longer than we might like *)
  | |- is_derive _ _ (fun _ => add _ (opp _)) _ => apply is_deriveB
  | |- is_derive _ _ (fun _ => add _ _) _ => apply is_deriveD
  | |- is_derive _ _ (fun _ => opp _) _ => apply is_deriveN
  | |- is_derive _ _ (fun=> _) _ =>  apply is_derive_cst
  | |- is_derive ?x _ (fun _ => fun_of_matrix (col _ _) _ _) _ => apply (is_derive_col x)
  | |- is_derive _ (delta_mx (Ordn _ 0) _)  _ _ => apply is_derive_coord_simple
  | |- is_derive _ 'e__ _ _ => apply is_derive_coord_simple
 end).

Section S.
Context {R : realType}.
Definition shapes1dP1_function (xm: 'rV_1) : 'rV_(1 + 1) :=
    let x : R := xm 0 0 in rowmx_of_list [::   (1/2)*(1-x) ;   (1/2)*(1+x)].
Definition shapes1dP1_vertices : 'cV[R]_2 := mx_of_list [:: [:: -1:R] ; [:: 1]].
Definition shapes1dP1_deriv (xm: 'rV[R]_1) : 'M[R]_(2,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: -1/2];  [:: 1/2]] : list (list (R))).

Ltac prove_lagrangian :=
let i := fresh "i" in let j := fresh "j" in intros i j;
test_I_n i; test_I_n j;
try match goal with 
| |- fun_of_matrix (?F (row i ?V)) 0 j =  if  i==j then _ else _ => rewrite /F /V
end;
simplify_ordinals;
rewrite_matrix;
ord_enum_cases i; clear i; rewrite_matrix;
 ord_enum_cases j; clear j; rewrite_matrix;
simpl; lra.

Ltac prove_deriv := 
let x := fresh "x" in intro x; symmetry;
compute_addn;
let i := fresh "i" in let j := fresh "j" in 
apply matrixP => i j; simpl in i, j;
match goal with |- _ ?A  => let a := fresh "a" in set a := A; rewrite mxE; subst a end;
repeat match goal with |- context [fun_of_matrix (?F (col _ _)) _ _] => unfold F end;
let f := fresh "f" in let g := fresh "g" in 
set (f := fun _ => _); simpl size in f;
match goal with |- _ = fun_of_matrix ?G _ _ => rewrite -(trmxK G); set g := trmx G end;
assert (DERIV: is_derive x 'e_j f (row j g)); [ | destruct DERIV as [_ Hval]; rewrite Hval  trmxE row__0 //];
subst f g;
simplify_ordinals;
ord_enum_cases j; clear j;
rewrite_matrix; rewrite_matrix_under;
try (ord_enum_cases i; clear i; rewrite_matrix; rewrite_matrix_under);
try (ord_enum_cases j; clear j; rewrite_matrix; rewrite_matrix_under);
simpl map; simpl size;
  apply is_derive_mx; intros i j; compute in i,j; ord1; (*rewrite ?trmxE; *)
  ord_enum_cases j; clear j; rewrite_matrix; rewrite_matrix_under;
  (eapply is_derive_eq; [ is_derive | simpl; repeat (progress change (scale ?A ?B) with (mul A B); simpl); lra]).

Definition shapes1dP1 : @Shape.shape R.
apply (Shape.Build_shape 1 2 shapes1dP1_function shapes1dP1_deriv shapes1dP1_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
- abstract (unfold shapes1dP1_function, shapes1dP1_deriv; prove_deriv).
Defined.

Definition shapes1dP2_vertices : 'cV[R]_3 := mx_of_list [:: [:: -1:R] ; [:: 0]; [:: 1] ].
Definition shapes1dP2_function (xm: 'rV_1) : 'rV_3 :=
    let x : R := xm 0 0 in rowmx_of_list [::   -(1/2)*(1-x)*x ;  (1-x)*(1+x);   (1/2)*x*(1+x)].
Definition shapes1dP2_deriv (xm: 'rV[R]_1) : 'M[R]_(3,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: -1/2*(1-2*x)];  [:: -2*x]; [:: 1/2*(1+2*x)]] : list (list (R))).

Definition shapes1dP2 : @Shape.shape R.
apply (Shape.Build_shape 1 3 shapes1dP2_function shapes1dP2_deriv shapes1dP2_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
- abstract (unfold shapes1dP2_function, shapes1dP2_deriv; prove_deriv).
Defined.

Definition shapes1dP3_vertices : 'cV[R]_4 := mx_of_list [::  [:: -1:R]; [:: -1/3]; [:: 1/3]; [:: 1]].
Definition shapes1dP3_function (xm: 'rV_1) : 'rV_4 :=
  let x: R := xm 0 0 in
   rowmx_of_list [::  -(1/16)*(1-x)*(1-3*x)*(1+3*x);  
                                   9/16*(1-x)*(1-3*x)*(1+x); 
                                   9/16*(1-x)*(1+3*x)*(1+x);
                                -(1/16)*(1-3*x)*(1+3*x)*(1+x) ].
Definition shapes1dP3_deriv (xm: 'rV[R]_1) : 'M[R]_(4,1) :=
   let x := xm 0 0 in
   mx_of_list ([:: [:: 1/16 * (1 + x*(18 + x*(-27)) )];  
                          [:: 9/16 * (-3 + x*(-2 + x*9)) ]; 
                          [:: 9/16 * (3 + x*(-2 + x*(-9))) ]; 
                          [:: 1/16 * (-1 + x*(18 + x*27) )]] : list (list (R))).

Definition shapes1dP3 : @Shape.shape R.
apply (Shape.Build_shape 1 4 shapes1dP3_function shapes1dP3_deriv shapes1dP3_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
- abstract (unfold shapes1dP3_function, shapes1dP3_deriv; prove_deriv).
Defined.

Definition shapes2dP1_vertices : 'M[R]_(4,2) := 
   mx_of_list [:: [:: -1:R; -1]; [:: 1; -1]; [:: 1;1]; [:: -1;1]].

Definition shapes2dP1_function (xy: 'rV[R]_2) : 'rV[R]_4 :=
   let Nx : 'rV_2 := shapes1dP1_function (col 0 xy) in
   let Ny : 'rV_2 := shapes1dP1_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 1 * Ny 0 1 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dP1_deriv (xm: 'rV[R]_2) : 'M[R]_(4,2) :=
  let Nx := shapes1dP1_function (col 0 xm) in
  let dNx := shapes1dP1_deriv (col 0 xm) in
  let Ny := shapes1dP1_function (col 1 xm) in
  let dNy := shapes1dP1_deriv (col 1 xm) in
  let x := xm 0 0 in let y := xm 0 1 in
  mx_of_list ([:: [:: dNx 0 0 * Ny 0 0 ; Nx 0 0 * dNy 0 0 ];
                         [:: dNx 1 0 * Ny 0 0 ; Nx 0 1 * dNy 0 0 ];
                         [:: dNx 1 0 * Ny 0 1 ; Nx 0 1 * dNy 1 0 ];
                         [:: dNx 0 0 * Ny 0 1 ; Nx 0 0 * dNy 1 0 ]]: list (list R)).

Definition shapes2dP1 : @Shape.shape R.
apply (Shape.Build_shape 2 4 shapes2dP1_function shapes2dP1_deriv shapes2dP1_vertices).
- abstract (unfold shapes2dP1_function, shapes1dP1_function, shapes2dP1_vertices; 
                  prove_lagrangian).
- abstract prove_continuously_differentiable.
- abstract (unfold shapes2dP1_function, shapes2dP1_deriv, shapes1dP1_function, shapes1dP1_deriv;
                  prove_deriv).
Defined. 

Definition shapes2dT1_vertices : 'M[R]_(3,2) := 
    mx_of_list [:: [:: 0:R; 0]; [:: 1; 0]; [:: 0; 1]].
Definition shapes2dT1_function (xy: 'rV[R]_2) : 'rV[R]_3 :=
   let x : R := xy 0 0 in
   let y : R := xy 0 1 in
   rowmx_of_list [:: 1-x-y; x; y]. 

Definition shapes2dT1_deriv (xm: 'rV[R]_2) : 'M[R]_(3,2) :=
  let x := xm 0 0 in let y := xm 0 1 in
  mx_of_list ([:: [:: -1 ; -1 ];
                         [:: 1 ; 0 ];
                         [:: 0 ; 1]]: list (list R)).

Definition shapes2dT1 : @Shape.shape R.
apply (Shape.Build_shape 2 3 shapes2dT1_function shapes2dT1_deriv shapes2dT1_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
- abstract (unfold shapes2dT1_function, shapes2dT1_deriv; prove_deriv).
Defined.

Definition shapes2dP2_vertices : 'M[R]_(9,2) := 
   mx_of_list [:: [:: -1:R;-1]; [:: 0; -1]; [:: 1;-1]; [:: 1;0]; [:: 1;1]; [:: 0;1]; [:: -1;1]; [:: -1;0]; [:: 0;0]].

Definition shapes2dP2_function (xy: 'rV[R]_2) : 'rV[R]_9 :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ; Nx 0 1 * Ny 0 1 ].

Definition shapes2dP2_deriv (xy: 'rV[R]_2) : 'M[R]_(9,2) :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
   let dNx : 'cV_3 := shapes1dP2_deriv (col 0 xy) in
   let dNy : 'cV_3 := shapes1dP2_deriv (col 1 xy) in
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
apply (Shape.Build_shape 2 9 shapes2dP2_function shapes2dP2_deriv shapes2dP2_vertices).
- time "lagrangian" abstract (unfold shapes2dP2_function,  shapes1dP2_function, shapes2dP2_vertices;
                                           prove_lagrangian).
- time "cont_diff" abstract prove_continuously_differentiable.
- time "is_deriv" abstract (unfold shapes2dP2_function, shapes2dP2_deriv, shapes1dP2_function, shapes1dP2_deriv;
                  prove_deriv).
Defined.

Definition shapes2dS2_vertices : 'M[R]_(8,2) := 
   mx_of_list [:: [:: -1:R;-1]; [:: 0; -1]; [:: 1;-1]; [:: 1;0]; [:: 1;1]; [:: 0;1]; [:: -1;1]; [:: -1;0]].

Definition shapes2dS2_function (xy: 'rV[R]_2) : 'rV[R]_8 :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dS2_deriv (xy: 'rV[R]_2) : 'M[R]_(8,2) :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
   let dNx : 'cV_3 := shapes1dP2_deriv (col 0 xy) in
   let dNy : 'cV_3 := shapes1dP2_deriv (col 1 xy) in
  mx_of_list [:: [:: dNx 0 0 * Ny 0 0; Nx 0 0 * dNy 0 0];
                        [:: dNx 1 0 * Ny 0 0; Nx 0 1 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 0; Nx 0 2 * dNy 0 0];
                        [:: dNx 2 0 * Ny 0 1; Nx 0 2 * dNy 1 0];
                        [:: dNx 2 0 * Ny 0 2; Nx 0 2 * dNy 2 0];
                        [:: dNx 1 0 * Ny 0 2; Nx 0 1 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 2; Nx 0 0 * dNy 2 0];
                        [:: dNx 0 0 * Ny 0 1; Nx 0 0 * dNy 1 0]].

Definition shapes2dS2 : @Shape.shape R.
apply (Shape.Build_shape 2 8 shapes2dS2_function shapes2dS2_deriv shapes2dS2_vertices).
- time "lagrangian" abstract (unfold shapes2dS2_function,  shapes1dP2_function, shapes2dS2_vertices;
                                           prove_lagrangian).
- time "cont_diff" abstract prove_continuously_differentiable.
- time "is_deriv" abstract (unfold shapes2dS2_function, shapes2dS2_deriv, shapes1dP2_function, shapes1dP2_deriv;
                  prove_deriv).
Defined.

End S.
