(** * CFEM.shape:  Lagrange shape functions, and some supporting theory *)

(** Right now, this file has a melange of supporting definitions, useful lemmas, proof automation,
  as well as the real-valued functional models of some shape functions from ../src/shapes.c 
*)
From mathcomp Require Import all_ssreflect ssralg ssrnum archimedean finfun.
From mathcomp Require Import all_algebra all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory.
Require Import CFEM.matrix_util.

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
End S.

Import GRing.

Module Shape.
Section S.
Context {R : realType}.

Record shape : Type := {
  d : nat;
  nsh: nat;
  θ: 'rV_d -> 'rV_nsh;  (* nsh shape functions, each R^d->R *)
  vtx: 'M[R]_(nsh,d); 
  K  := convex_hull vtx;
  lagrangian: forall i j, θ (row i vtx) 0 j  = if i==j then 1 else 0;
  diff: forall j: 'I_nsh, continuously_differentiable (fun i => θ i 0 j)
}.

End S.
End Shape.

Definition single {R: realType} (x: R) := @const_mx R 1 1 x.

From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Ltac case_splitP j :=  (* this is copied from LAProof somewhere *)
  tryif clearbody j then fail "case_splitP requires a variable, but got  a local definition" j
  else tryif is_var j then idtac else fail "case_splitP requires a variable, but got" j;
 match type of j with 'I_(addn ?a ?b) =>
  let i := fresh "j" in let H := fresh in 
  destruct (splitP j) as [i H | i H];
 [replace j with (@lshift a b i); [ | apply ord_inj; simpl; lia]
 |replace j with (@rshift a b i); [ | apply ord_inj; simpl; lia]];
 clear j H; rename i into j
 end.

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
| IMP_mono1: forall i (k: nat), is_multivariate_polynomial (fun x => x 0 i)
| IMP_mono: forall i (k: nat), is_multivariate_polynomial (fun x => x 0 i ^ k).

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
  forall [d] (i: 'I_d.+1),
continuously_differentiable (fun x : 'rV[R]_d.+1 => fun_of_matrix x 0 i).
Proof.
intros.
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
assert (forall y, is_derive y (1 : R(*^o*)) id 1).
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

Ltac prove_continuously_differentiable :=
let j := fresh "j" in 
intro j;
lazymatch goal with
  |  j: 'I_?n |- continuously_differentiable (fun i => fun_of_matrix (?f i) 0 j) => try unfold f
  | |- _ => fail "prove_continuously_differentiable must be applied to a goal of the form, continuously_differentiable (fun i => ...)"
end;
repeat match type of j with context [S (S ?A)] => change  (S (S ?A)) with (1 + S A)%nat in j end;
repeat case_splitP j; rewrite !ord1 /=;
rewrite [continuously_differentiable]lock;
repeat (under eq_locked_continuously_differentiable do [ rewrite /single /at00 ?mxE /split /= ];
            repeat (destruct (ltnP _ _); try discriminate));
rewrite -lock;
apply multivariate_polynomial_continuously_differentiable; repeat constructor.

Ltac prove_lagrangian_old_and_slow := 
let i := fresh "i" in let j := fresh "j" in 
intros i j;
rewrite /single /at00 !mxE;
repeat match type of i with context [S (S ?A)] => change  (S (S ?A)) with (1 + S A)%nat in i end;
repeat match type of j with context [S (S ?A)] => change  (S (S ?A)) with (1 + S A)%nat in j end;
repeat case_splitP j; repeat case_splitP i; 
repeat (rewrite ?ord1 ?mxE /= /split; repeat (destruct (ltnP _ _); try discriminate));
rewrite ?mxE /=; try nra.

Ltac split_I_n := 
repeat 
match goal with i: 'I_(S (S ?A)) |- _ => 
  change (S (S A)) with (1 + S A) in i;
  let i' := fresh i in rename i into i'; 
   destruct (split_ordP i') as [i Hi | i Hi]; subst i'
end;
rewrite ?ord1; repeat match goal with i: 'I__ |- _ => clear i end. 

Ltac is_ground_nat n := lazymatch n with O => idtac | S ?n' => is_ground_nat n' end.

Ltac test_I_n i := 
match type of i with
 | 'I_?n => let n := eval compute in n in is_ground_nat n
 | ?t =>  fail "Type of" i "is" t "but should be 'I_n where n is a constant"
end.


Ltac prove_lagrangian :=
let i := fresh "i" in let j := fresh "j" in intros i j;
test_I_n i; test_I_n j;
try match goal with 
| |- fun_of_matrix (?F (row i ?V)) 0 j =  if  i==j then _ else _ => rewrite /F /V
end;
try match goal with |- context [ fun_of_matrix (?F (col _ (row _ _))) _ _ ] => rewrite /F end;
revert j;
repeat match goal with |- context [fun_of_matrix (rowmx_of_list ?A) _ _] =>
  let x := fresh "x" in set x := fun_of_matrix (rowmx_of_list A) _ _; unfold rowmx_of_list in x; simpl x
end;
repeat match goal with x := fun_of_matrix _ _ _ |- _ => revert x end;
split_I_n;
row_col_matrix_tac;
rewrite ?mxE;
cbv zeta;
intro;
split_I_n; simpl;
row_col_matrix_tac;
try (rewrite ?mulr1 ?mul1r ?mulr0 ?mul0r ?addrN; auto; nra).


Section S.
Context {R : realType}.

Definition shapes1dP1_function (xm: 'rV_1) : 'rV_(1 + 1) :=
    let x : R := xm 0 0 in rowmx_of_list [::   (1/2)*(1-x) ;   (1/2)*(1+x)].
Definition shapes1dP1_vertices : 'cV[R]_2 := mx_of_list [:: [:: -1:R] ; [:: 1]].

Definition shapes1dP1 : @Shape.shape R.
apply (Shape.Build_shape 1 2 shapes1dP1_function shapes1dP1_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes1dP2_vertices : 'cV[R]_3 := mx_of_list [:: [:: -1:R] ; [:: 0]; [:: 1] ].
Definition shapes1dP2_function (xm: 'rV_1) : 'rV_3 :=
    let x : R := xm 0 0 in rowmx_of_list [::   -(1/2)*(1-x)*x ;  (1-x)*(1+x);   (1/2)*x*(1+x)].

Definition shapes1dP2 : @Shape.shape R.
apply (Shape.Build_shape 1 3 shapes1dP2_function shapes1dP2_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes1dP3_vertices : 'cV[R]_4 := mx_of_list [::  [:: -1:R]; [:: -1/3]; [:: 1/3]; [:: 1]].
Definition shapes1dP3_function (xm: 'rV_1) : 'rV_4 :=
  let x: R := xm 0 0 in
   rowmx_of_list [::  -(1/16)*(1-x)*(1-3*x)*(1+3*x);  
                                   9/16*(1-x)*(1-3*x)*(1+x); 
                                   9/16*(1-x)*(1+3*x)*(1+x);
                                -(1/16)*(1-3*x)*(1+3*x)*(1+x) ].

Definition shapes1dP3 : @Shape.shape R.
apply (Shape.Build_shape 1 4 shapes1dP3_function shapes1dP3_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes2dP1_vertices : 'M[R]_(4,2) := 
   mx_of_list [:: [:: -1:R; -1]; [:: 1; -1]; [:: 1;1]; [:: -1;1]].

Definition shapes2dP1_function (xy: 'rV[R]_2) : 'rV[R]_4 :=
   let Nx : 'rV_2 := shapes1dP1_function (col 0 xy) in
   let Ny : 'rV_2 := shapes1dP1_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 1 * Ny 0 1 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dP1 : @Shape.shape R.
apply (Shape.Build_shape 2 4 shapes2dP1_function shapes2dP1_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes2dP2_vertices : 'M[R]_(9,2) := 
   mx_of_list [:: [:: -1:R;-1]; [:: 0; -1]; [:: 1;-1]; [:: 1;0]; [:: 1;1]; [:: 0;1]; [:: -1;1]; [:: -1;0]; [:: 0;0]].

Definition shapes2dP2_function (xy: 'rV[R]_2) : 'rV[R]_9 :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ; Nx 0 1 * Ny 0 1 ].

Definition shapes2dP2 : @Shape.shape R.
apply (Shape.Build_shape 2 9 shapes2dP2_function shapes2dP2_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes2dS2_vertices : 'M[R]_(8,2) := 
   mx_of_list [:: [:: -1:R;-1]; [:: 0; -1]; [:: 1;-1]; [:: 1;0]; [:: 1;1]; [:: 0;1]; [:: -1;1]; [:: -1;0]].

Definition shapes2dS2_function (xy: 'rV[R]_2) : 'rV[R]_8 :=
   let Nx : 'rV_3 := shapes1dP2_function (col 0 xy) in
   let Ny : 'rV_3 := shapes1dP2_function (col 1 xy) in
  rowmx_of_list [:: Nx 0 0 * Ny 0 0 ; Nx 0 1 * Ny 0 0 ; Nx 0 2 * Ny 0 0;
                              Nx 0 2 * Ny 0 1 ; Nx 0 2 * Ny 0 2 ; Nx 0 1 * Ny 0 2;
                              Nx 0 0 * Ny 0 2 ; Nx 0 0 * Ny 0 1 ].

Definition shapes2dS2 : @Shape.shape R.
apply (Shape.Build_shape 2 8 shapes2dS2_function shapes2dS2_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

Definition shapes2dT1_vertices : 'M[R]_(3,2) := 
    mx_of_list [:: [:: 0:R; 0]; [:: 1; 0]; [:: 0; 1]].
Definition shapes2dT1_function (xy: 'rV[R]_2) : 'rV[R]_3 :=
   let x : R := xy 0 0 in
   let y : R := xy 0 1 in
   rowmx_of_list [:: 1-x-y; x; y].

Definition shapes2dT1 : @Shape.shape R.
apply (Shape.Build_shape 2 3 shapes2dT1_function shapes2dT1_vertices).
- abstract prove_lagrangian.
- abstract prove_continuously_differentiable.
Defined.

End S.

(** some experiments with mathcomp.algebra's Lagrange polynomials *)

From mathcomp Require Import algebra.qpoly.


Ltac simpl_bigop_index_enum :=
match goal with |- context [@bigop.body ?t1 ?t2 ?idx (index_enum ?s) ?f] => pattern (@bigop.body t1 t2 idx (index_enum s) f)  end;
match goal with |- ?hideme _ => let hide := fresh "hide" in
   set hide := hideme;
   rewrite bigop.unlock locked_withE Finite.enum.unlock /= /ord_enum /= /reducebig /Option.apply !insubT /Sub /=;
   subst hide; cbv beta
end.

Lemma bigop_2_1: forall [R] [op: R -> R -> R] [idx: R] (f: 'I_2 -> R), \big[op/idx]_(i < 2 | i != 0) f i = op (f 1) idx.
Proof.
intros.
simpl_bigop_index_enum.
f_equal. f_equal.
apply ord_inj; reflexivity.
Qed.

Lemma bigop_2_0: forall [R] [op: R -> R -> R] [idx: R] (f: 'I_2 -> R), \big[op/idx]_(i < 2 | i != 1) f i = op (f 0) idx.
Proof.
intros.
simpl_bigop_index_enum.
f_equal. f_equal.
apply ord_inj; reflexivity.
Qed.

Section S.
Context {R : realType}.

Definition R_of_nat : nat ->  R  := @natmul  (Num_NumDomain__to__Algebra_BaseAddUMagma R) 1.

Lemma injective_R_of_nat : injective R_of_nat.
Proof.
apply (@mulrIn R).
apply lt0r_neq0.
change (is_true ((0 : Num.NumDomain.sort R) < (1 : Num.NumDomain.sort R))).
apply ltr01.
Qed.

Hint Resolve injective_R_of_nat : core.

Definition the_points : nat -> Nmodule.sort R  := fun i => -1 + natmul 2 i.
Lemma injective_the_points: injective the_points.
Proof.
rewrite /the_points.
move => x y.
set a := natmul 2 x.
set b := natmul 2 y.
move => H.
assert (a = b).
clearbody a; clearbody b.
lra.
subst a b; revert H0; clear. revert x y.
apply mulrIn.
apply lt0r_neq0.
change (is_true ((0 : Num.NumDomain.sort R) < (2 : Num.NumDomain.sort R))).
lra.
Qed.

Hint Resolve injective_the_points : core.

Definition lagrange_2 := lagrange 2 the_points.
Definition lagrange_2_0 : {poly_2 R} := tnth lagrange_2 0.

Lemma sub_natmulE1: forall (x: R) (i j: nat), is_true (j<=i)%N -> add (natmul x i) (opp (natmul x j)) = (natmul x (subn i j)).
Proof.
intros.
rewrite mulrnBr //.
Qed.

Lemma sub_natmulE2: forall (x: R) (i j: nat), is_true (i<=j)%N -> add (natmul x i) (opp (natmul x j)) = opp (natmul x (subn j i)).
Proof.
intros.
rewrite mulrnBr //. lra.
Qed.

Ltac rsimpl := 
   repeat (rewrite ?opprK ?invrN ?subr0 ?invr1 ?subr0 ?mul1r ?mulr1 ?mulN1r ?opprB ?addSn ?add0n ?mulN1r;
                try (rewrite modn_small; [ | lia]);
                try (rewrite sub_natmulE1; [ | lia]);
                try (rewrite sub_natmulE2; [ | lia])).

Goal forall x, horner (tnth lagrange_2 0) x = (2^-1) * (1 - x).
Proof.
move => x.
rewrite lagrangeE // /the_points /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
rewrite addNr add0r -opprB invrN mulNr -mulrN.
f_equal; try lra.
f_equal.
lra.
Qed.

Goal forall x, horner (tnth lagrange_2 1) x =  (2^-1) * (1 + x).
Proof.
move => x.
rewrite lagrangeE // /the_points /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
rewrite addNr add0r.
f_equal.
lra.
Qed.


Goal forall i j : 'I_2, horner (tnth lagrange_2 i) (the_points j) = (i==j)%:R.
Proof.
move => i j.
apply lagrange_sample; auto.
Qed.

Goal forall x, horner (tnth (lagrange 1 R_of_nat) 0) x = 1.
Proof.
move => x.
rewrite lagrangeE // /R_of_nat /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
auto.
Qed.



Goal forall x, horner (tnth (lagrange 3 R_of_nat) 0) x = 2^-1 * (x - 1) * (x - 2) .
Proof.
move => x.
rewrite lagrangeE // /R_of_nat /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
auto.
Qed.


Goal forall x, horner (tnth (lagrange 3 R_of_nat) 1) x = - x * (x - 2).
Proof.
move => x.
rewrite lagrangeE // /R_of_nat /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
auto.
Qed.

Goal forall x, horner (tnth (lagrange 3 R_of_nat) 2) x = 2^-1 * x * (x - 1).
Proof.
move => x.
rewrite lagrangeE // /R_of_nat /=.
simpl_bigop_index_enum.
rewrite !hornerE /=.
rsimpl.
auto.
Qed.

   

Fail Lemma poly_continuously_differentiable: forall p : {poly R}, continuously_differentiable (horner p).

End S.


