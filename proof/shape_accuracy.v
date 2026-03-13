From CFEM Require Import shape shapefloat.
From mathcomp Require Import Rstruct.
Import matrix matrix_util fintype.

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Stdlib.Lists.List ListNotations.
From LAProof Require Import matrix_model.

Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Ltac prove_roundoff_bound2 ::=
 (* Remove this when we are using a VCFloat in which https://github.com/VeriNum/vcfloat/issues/34
   is fixed. *)
match goal with
| P: prove_rndval ?bmap ?vmap ?e |- prove_roundoff_bound ?bmap' ?vmap' ?e' _ =>
  constr_eq bmap bmap'; constr_eq vmap vmap'; constr_eq e e';
  revert P
| _ => fail "not the right kind of proof goal for prove_roundoff_bound2"
end;

let BMD := fresh "BMD" in
let H2 := fresh "H2" in let H3 := fresh "H3" in let FIN := fresh "FIN" in
   let e := fresh "e" in let r := fresh "r" in let s := fresh "s" in
 intros [[r s] [H2 H3]] BMD;
specialize (H3 BMD);
red;
match goal with |- ?G => let GG := fresh "GG" in set (GG := G);
  revert H2; compute_fshift_div; cbv_fcval; intro H2; subst GG
 end;
inversion H2; clear H2; subst;
fold Tsingle in H3; fold Tdouble in H3;
apply rndval_with_cond_result1_e in H3;
destruct H3 as [errors [H0 H2]];
 match type of H2 with context [fval ?env ?ee] =>
   set (e := fval env ee) in H2|-*;
  let e1 := eval hnf in ee in change ee with e1 in e
end;
 destruct H2 as [FIN H2]; split; [assumption  | ]; clear FIN;
 clearbody e;
 simpl in e;
 try change (B2R _ _ e) with (FT2R e) in H2;
 match goal with H2 : _ = @FT2R ?t1 e |- context [@FT2R ?t2 e] =>
  change t2 with t1
 end;
 rewrite <- H2; clear H2 e;

 match goal with |- context [rval ?env ?x] =>
   let a := constr:(rval env x) in let b := eval red in a in change a with b
 end;
 cbv_reval;
 simpl ff_args;
  let j := fresh "j" in repeat (set (j := ff_realfunc _); simpl in j; subst j);
(* unfold  env_; *)
 process_boundsmap_denote;

 repeat change (B2R (fprec ?t) _) with (@FT2R t);
 rewrite <- ?B2R_float_of_ftype in * by auto with typeclass_instances; (* NEW *)

 repeat (let E := fresh "E" in
            assert (E := Forall_inv H0);
            cbv delta [Maps.PTree.prev Maps.PTree.prev_append] in E;
            simpl in E;
           rewrite ?(Rabs_pos_eq _ (error_bound_nonneg _ _)) in E;
          match type of E with
           |  Rle (Rabs ?a) (error_bound _ Normal') =>
                let d := fresh "d" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal') =>
                let d := fresh "e" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal2') =>
                   let d := fresh "e" in set (d := a) in *; clearbody d
           | Rle (Rabs ?a) _ =>
                   let d := fresh "e" in set (d := a) in *; clearbody d
           end;
            try (eapply adjust_bound in E; [ | compute; reflexivity]);
           apply Forall_inv_tail in H0);
 try match type of H0 with Forall _ (Maps.PTree.elements Maps.PTree.Empty) => clear H0 end;
 try match type of H0 with Forall _ nil => clear H0 end;
 try clear errors;
 repeat match goal with B: context [FT2R ?v] |- _ =>
  is_var v; let u := fresh "u" in set (u := FT2R v) in *;
  clearbody u; clear v; rename u into v
 end;

 concrete_env_variables;
 abstract_env_variables;

 (* Clean up all FT2R constants *)
 repeat (change (FT2R ?x) with (B2R _ _ x) in *);
 simpl B2R in *;
(*
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
*)
 rewrite <- ?(F2R_eq Zaux.radix2);
 repeat match goal with |- context [F2R _ ?x] => unfold x end;
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end.


Existing Instance FPCompCert.nans.


Definition firstn_canon_idents (n: nat) := map Pos.of_succ_nat (seq 0 n).

Definition cuboid_bounds (i: ident) := Build_varinfo Tdouble i (-1) 1.
Definition simplex_bounds (i: ident) := Build_varinfo Tdouble i 0 1.

Ltac compute_boundsmap one_d_bound dim :=
 let bmlist := constr:(boundsmap_of_list (map one_d_bound (firstn_canon_idents dim))) in
 let a := eval cbv beta fix match delta 
    [ cuboid_bounds simplex_bounds 
     boundsmap_of_list firstn_canon_idents
      map seq Pos.of_succ_nat Pos.succ  fold_left] in bmlist
  in let b := compute_PTree a in
   exact b.

Definition cuboid_boundsmap_1d := ltac:(compute_boundsmap cuboid_bounds 1%nat).
Definition cuboid_boundsmap_2d := ltac:(compute_boundsmap cuboid_bounds 2%nat).
Definition simplex_boundsmap_2d := ltac:(compute_boundsmap simplex_bounds 2%nat).

Ltac changeStdLibToCore f :=
 lazymatch f with 
 | @FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble => constr:(@BMULT FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble => constr:(@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble => constr:(@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble)
 | @FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble => constr:(@BOPP FPCompCert.nans Tdouble is_standard_Tdouble)
 | ?A ?B => let a := changeStdLibToCore A in let b := changeStdLibToCore B in constr:(a b)
 | _ => constr:(f)
 end.

Ltac red_to_rowmx f := 
lazymatch f with
 | col_mx _ _ => f
 | rowmx_of_list _ => f
 | row_mx _ _ => f
 | _ => let g := eval red in f in red_to_rowmx g
end.

Ltac translate_matrix f := 
let x := fresh "x" in 
let g := fresh "g" in 
evar (g: ftype Tdouble -> ftype Tdouble);
let H := fresh in 
let prop := constr:(forall x : ftype Tdouble, f x = g x) in let prop := eval cbv beta in prop in 
assert (H: prop);  [
  intro x;
 match goal with |- fun_of_matrix _ ?i ?j = _ =>  try simplify_ordinal i; try simplify_ordinal j end;
 repeat
  lazymatch goal  with
  | |- fun_of_matrix (rowmx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix (mx_of_list_def _) _ _ = _ => fail
  | |- fun_of_matrix ?a _ _ = _ => let b := eval red in a in change a with b
  end;
 simpl seq.size;
 rewrite_matrix;
 change (@FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble) with (@BMULT FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble) with (@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble) with (@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble) with (@BOPP FPCompCert.nans Tdouble is_standard_Tdouble);
 subst g; reflexivity
 | subst g;  exact H].

Ltac realify := 
try change (@nmodule.Algebra.add _) with Rplus;
try change (@nmodule.Algebra.opp _) with Ropp;
try change (@ssralg.GRing.mul _) with Rmult;
try change (@ssralg.GRing.inv _) with Rinv;
try change (ssralg.GRing.one _) with 1;
change (ssralg.GRing.one
        (ssralg.GRing.PzRing.Exports.join_GRing_PzRing_between_Algebra_BaseZmodule_and_GRing_PzSemiRing
           (reals.Real.Exports.reals_Real__to__GRing_PzRing
              RbaseSymbolsImpl_R__canonical__reals_Real))) with 1;
try change (@nmodule.Algebra.zero _) with 0;
repeat change (nmodule.Algebra.natmul _ ?i) with (INR i).

Lemma rowmx_of_list_1: forall [T] (x: 'M[T]_1), rowmx_of_list [x ord0 ord0] = x.
Proof.
intros.
unfold rowmx_of_list; apply matrixP; intros ? ?. simpl in y.
unfold row_mx, const_mx; rewrite !mxE.
unfold fintype.split. rewrite ord1. simpl.
destruct (ssrnat.ltnP 0 1); try lia.
rewrite mxE.
f_equal. apply ord_inj; simpl. rewrite ord1. auto.
Qed.

Definition vmap_of_rV_list [n] (x: 'rV[ftype Tdouble]_n) :=
      map (fun i => (Pos.of_succ_nat (nat_of_ord i), existT ftype _ (fun_of_matrix x ord0 i))) (ord_enum n).

Lemma vmap_of_rV_list_valid: forall [n] (x: 'rV[ftype Tdouble]_n),
  @valmap_valid empty_collection (valmap_of_list' (@vmap_of_rV_list n x)).
Proof.
intros.
unfold vmap_of_rV_list.
unfold valmap_valid.
intros.
destruct ty as [t a].
simpl.
unfold valmap_of_list' in H.
rewrite <- fold_left_rev_right in H.
rewrite <- map_rev in H.
revert H.
induction (rev (ord_enum n)); intros.
inversion H.
simpl in H.
destruct (Pos.eq_dec id  (Pos.of_succ_nat (@nat_of_ord n a0))).
subst id.
rewrite Maps.PTree.gss in H.
assert (t = Tdouble) by congruence.
subst; hnf; auto.
rewrite Maps.PTree.gso in H by auto.
apply IHl; auto.
Qed.

Definition  vmap_of_rV [n](x: 'rV[ftype Tdouble]_n) : valmap :=
   @valmap_of_list empty_collection (vmap_of_rV_list x) (vmap_of_rV_list_valid x).

Ltac simplify_vmap_of_rV :=
let u := fresh "u" in set (u := @vmap_of_rV _ _ );
  pattern u; subst u;
  let G := fresh "G" in 
  match goal with |- ?A _ => set (G:=A) end;
  cbv [vmap_of_rV rowmx_of_list valmap_of_list valmap_of_list'
                               vmap_of_rV_list make_valmap]; simpl seq.size;
let b := fresh "b" in 
evar (b: Maps.PTree.tree {x : type & ftype x});
let H := fresh in 
match goal with |- G (exist valmap_valid ?L _) => assert (H: L=b); [
 match L with fold_left _ (map _ (ord_enum ?n)) _ => 
  pattern (ord_enum n);
  match goal with |- ?F _ => 
    let f := fresh "f" in set (f:=F);
      let c := constr:(ord_enum n) in let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with (eq_refl true) by apply proof_irr; clear e | try (contradiction e; reflexivity)]);
     subst f; cbv beta
  end
end;
cbv [fold_left map Pos.of_succ_nat Pos.succ nat_of_ord];
rewrite_matrix;
cbv [Maps.PTree.set Maps.PTree.set0 Maps.PTree.set' Maps.PTree.empty];
subst b;
reflexivity
|
let VALID := fresh "VALID" in 
assert (VALID: valmap_valid b) by (apply compute_valmap_valid; repeat split; apply Logic.I);
rewrite (boolp.eq_exist _ VALID)  by apply H; clear H;
subst b G; cbv beta;
let vmap := fresh "vmap" in set (vmap := exist valmap_valid _ VALID: valmap);
change (exist valmap_valid _ VALID) with vmap
 ]
end.

Definition x_vmap_list (x : ftype Tdouble) :=
   [(1%positive, existT ftype _ x)].

Definition x_vmap (x : ftype Tdouble) : valmap :=
 ltac:(make_valmap_of_list (x_vmap_list x)).


Goal vmap_of_rV (rowmx_of_list [ Zconst Tdouble 3; Zconst Tdouble 4]) = x_vmap (Zconst Tdouble 0).
   simplify_vmap_of_rV.
Abort.

Ltac related_matrix f := let x :=
     fresh "x" in intro x;
    match type of (f x) with _ = ?t => let b := eval cbv beta in t in exact b end.
 
Definition relate_1dP1_0  
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (rowmx_of_list [x]) ord0 (Ordn 2 0))).
Definition f_1dP1_0 := ltac:(related_matrix relate_1dP1_0).

Goal f_1dP1_0 = fun x : ftype Tdouble => (0.5 * (1 - x))%F64.  reflexivity. Abort.  
Definition   relate_1dP1_1
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (rowmx_of_list [x]) ord0 (Ordn 2 1))).

Definition f_1dP1_1 := ltac:(related_matrix relate_1dP1_1).

Local Ltac function_arity t :=
  lazymatch t with _ -> ?B => let n := function_arity B in constr:(S n) | _ => constr:(O) end.

Ltac reify_function f := 
   match type of f with ?t => let n := function_arity t in
        let vars := constr:(firstn_canon_idents n) in let vars := eval compute in vars in 
        let e' := HO_reify_float_expr vars f 
        in exact e'
   end.

Derive acc_1dP1_0
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_0)  acc_1dP1_0)
 as derive_roundoff_bound_1dP1_0.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_1dP1_0).  (* 1.1102230246251587e-16%F64 *)

Definition acc_1dP1 : R := 12 / IZR (Z.pow_pos 10 17).

Lemma prove_roundoff_bound_1dP1_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_0) acc_1dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_1dP1_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_1) acc_1dP1.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Definition relate_1dP1deriv_0 := 
   ltac:(translate_matrix (fun x => shapes1dP1_fderiv (rowmx_of_list [x]) (Ordn 2 0) ord0)).
Definition f_1dP1deriv_0 := ltac:(related_matrix relate_1dP1deriv_0).

Definition relate_1dP1deriv_1 := 
   ltac:(translate_matrix (fun x => shapes1dP1_fderiv (rowmx_of_list [x]) (Ordn 2 1) ord0)).
Definition f_1dP1deriv_1 := ltac:(related_matrix relate_1dP1deriv_1).

Definition acc_1dP1d : R := 0.

Lemma prove_roundoff_bound_1dP1deriv_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1deriv_0) acc_1dP1d.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma prove_roundoff_bound_1dP1deriv_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1deriv_1) acc_1dP1d.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Definition relate_1dP2_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (Ordn 3 0))).
Definition f_1dP2_0 := ltac:(related_matrix relate_1dP2_0).

Definition relate_1dP2_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (Ordn 3 1))).
Definition f_1dP2_1 := ltac:(related_matrix relate_1dP2_1).

Definition relate_1dP2_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (@Ordn 3 2))).
Definition f_1dP2_2 := ltac:(related_matrix relate_1dP2_2).

Derive acc_1dP2_1
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_1)  acc_1dP2_1)
 as derive_roundoff_bound_1dP_1.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_1dP2_1). (* 1.3322676295501908e-15%F64 *)


Definition acc_1dP2: R := 14 / IZR (Z.pow_pos 10 14).

Lemma prove_roundoff_bound_1dP2_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_0) acc_1dP2.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_1dP2_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_1) acc_1dP2.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.


Lemma prove_roundoff_bound_1dP2_2:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_2) acc_1dP2.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.



Definition relate_1dP2deriv_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (Ordn 3 0) ord0)).
Definition f_1dP2deriv_0 := ltac:(related_matrix relate_1dP2deriv_0).

Definition relate_1dP2deriv_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (Ordn 3 1) ord0)).
Definition f_1dP2deriv_1 := ltac:(related_matrix relate_1dP2deriv_1).

Definition relate_1dP2deriv_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (Ordn 3 2) ord0)).
Definition f_1dP2deriv_2 := ltac:(related_matrix relate_1dP2deriv_2).


Definition acc_1dP2deriv : R := 4 / IZR (Z.pow_pos 10 16).

Lemma prove_roundoff_bound_1dP2deriv_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2deriv_0) acc_1dP2deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_1dP2deriv_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2deriv_1) acc_1dP2deriv.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.


Lemma prove_roundoff_bound_1dP2deriv_2:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2deriv_2) acc_1dP2deriv.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Ltac translate_matrix2 f := 
let x := fresh "x" in let y := fresh "y" in 
let g := fresh "g" in 
evar (g: ftype Tdouble -> ftype Tdouble -> ftype Tdouble);
let H := fresh in 
let prop := constr:(forall x y : ftype Tdouble, f x y = g x y) in let prop := eval cbv beta in prop in 
assert (H: prop);  [
  intros x y;
 match goal with |- fun_of_matrix _ ?i ?j = _ =>  try simplify_ordinal i; try simplify_ordinal j end;
 repeat
  lazymatch goal  with
  | |- fun_of_matrix (rowmx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix (mx_of_list_def _) _ _ = _ => fail
  | |- fun_of_matrix ?a _ _ = _ => let b := eval red in a in change a with b
  end;
 unfold shapes1dP1_float, shapes1dP1_fderiv, shapes1dP2_float, shapes1dP2_fderiv;
 repeat match goal with |- context [col ?i _] =>  try simplify_ordinal i end;
 repeat match goal with |- context [fun_of_matrix _ ?i _] =>  simplify_ordinal i end;
 repeat match goal with |- context [fun_of_matrix _ _ ?j] =>  simplify_ordinal j end;
 simpl seq.size;
 rewrite_matrix;
 change (@FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble) with (@BMULT FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble) with (@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble) with (@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble) with (@BOPP FPCompCert.nans Tdouble is_standard_Tdouble);
  subst g; reflexivity
 | subst g;  exact H].

Ltac related_matrix2 f := let x := fresh "x" in intro x; let y := fresh "y" in intro y;
    match type of (f x y) with _ = ?t => let b := eval cbv beta in t in exact b end.

Definition relate_2dP1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (Ordn 4 0))).
Definition f_2dP1_0 := ltac:(related_matrix2 relate_2dP1_0).

Definition relate_2dP1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (Ordn 4 1))).
Definition f_2dP1_1 := ltac:(related_matrix2 relate_2dP1_1).

Definition relate_2dP1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (Ordn 4 2))).
Definition f_2dP1_2 := ltac:(related_matrix2 relate_2dP1_2).

Definition relate_2dP1_3 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (Ordn 4 3))).
Definition f_2dP1_3 := ltac:(related_matrix2 relate_2dP1_3).

Derive acc_2dP1_1
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1_1)  acc_2dP1_1)
 as derive_roundoff_bound_2dP1_1.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_2dP1_1). (* 3.33066907387548e-16%F64 *)

Definition acc_2dP1: R := 4 / IZR (Z.pow_pos 10 16).

Lemma prove_roundoff_bound_2dP1_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1_0) acc_2dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1_1) acc_2dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1_2:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1_2) acc_2dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1_3:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1_3) acc_2dP1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.


Definition relate_2dP1deriv_0_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 0) (Ordn 2 0))).
Definition f_2dP1deriv_0_0 := ltac:(related_matrix2 relate_2dP1deriv_0_0).

Definition relate_2dP1deriv_0_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 0) (Ordn 2 1))).
Definition f_2dP1deriv_0_1 := ltac:(related_matrix2 relate_2dP1deriv_0_1).

Definition relate_2dP1deriv_1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 1) (Ordn 2 0))).
Definition f_2dP1deriv_1_0 := ltac:(related_matrix2 relate_2dP1deriv_1_0).

Definition relate_2dP1deriv_1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 1) (Ordn 2 1))).
Definition f_2dP1deriv_1_1 := ltac:(related_matrix2 relate_2dP1deriv_1_1).

Definition relate_2dP1deriv_2_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 2) (Ordn 2 0))).
Definition f_2dP1deriv_2_0 := ltac:(related_matrix2 relate_2dP1deriv_2_0).

Definition relate_2dP1deriv_2_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 2) (Ordn 2 1))).
Definition f_2dP1deriv_2_1 := ltac:(related_matrix2 relate_2dP1deriv_2_1).

Definition relate_2dP1deriv_3_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 3) (Ordn 2 0))).
Definition f_2dP1deriv_3_0 := ltac:(related_matrix2 relate_2dP1deriv_3_0).

Definition relate_2dP1deriv_3_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (Ordn 4 3) (Ordn 2 1))).
Definition f_2dP1deriv_3_1 := ltac:(related_matrix2 relate_2dP1deriv_3_1).

Derive acc_2dP1deriv
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_0_0)  acc_2dP1deriv)
 as derive_roundoff_bound_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_2dP1deriv). (* 1.11022302462516%F64 *)

Lemma prove_roundoff_bound_2dP1deriv_0_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_0_0) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_0_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_0_1) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_1_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_1_0) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_1_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_1_1) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_2_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_2_0) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_2_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_2_1) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_3_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_3_0) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dP1deriv_3_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_3_1) acc_2dP1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Definition relate_2dT1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (Ordn 3 0))).
Definition f_2dT1_0 := ltac:(related_matrix2 relate_2dT1_0).

Definition relate_2dT1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (Ordn 3 1))).
Definition f_2dT1_1 := ltac:(related_matrix2 relate_2dT1_1).

Definition relate_2dT1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (Ordn 3 2))).
Definition f_2dT1_2 := ltac:(related_matrix2 relate_2dT1_2).

Derive acc_2dT1_0
 in  (forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1_0)  acc_2dT1_0)
 as derive_roundoff_bound_2dT1_0.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
match goal with |- 0 <= ?acc - ?A => assert (acc = A) by (unfold acc; reflexivity) end.
lra.
Qed.

Check ltac:(ShowBound acc_2dT1_0). (* 5.551115123125793e-16%F64 *)


Definition acc_2dT1: R := 6 / IZR (Z.pow_pos 10 16).

Lemma prove_roundoff_bound_2dT1_0:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1_0) acc_2dT1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dT1_1:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1_1) acc_2dT1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Lemma prove_roundoff_bound_2dT1_2:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1_2) acc_2dT1.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

Definition relate_2dT1deriv_0_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 0) (Ordn 2 0))).
Definition f_2dT1deriv_0_0 := ltac:(related_matrix2 relate_2dT1deriv_0_0).

(*
Definition foo: False.
let f := constr:(fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 0) (Ordn 2 1)) in 
let x := fresh "x" in let y := fresh "y" in 
let g := fresh "g" in 
evar (g: ftype Tdouble -> ftype Tdouble -> ftype Tdouble);
let H := fresh in 
let prop := constr:(forall x y : ftype Tdouble, f x y = g x y) in let prop := eval cbv beta in prop in 
assert (H: prop);  [
  intros x y;
 unfold FShape.θ, FShape.dθ; simpl;
 match goal with |- fun_of_matrix ?a _ _ = _ => 
        let b := eval red in a in change a with b 
  end;
 unfold shapes1dP1_float, shapes1dP1_fderiv;
 unfold rowmx_of_list; simpl seq.size;
  match goal with |- ?A => let b := changeStdLibToCore A in change b end;
idtac (*
 rewrite_matrix;
  subst g; reflexivity *)
 | subst g].
{
rewrite_matrix.
Import Base ssrnat ssrfun ssrbool.

Ltac foo :=
match goal with
  | |- context [fun_of_matrix (@row_mx ?T ?m ?n1 ?n2 ?A ?B) ?i ?j ] => is_const_ordinal j;
    let j' := constr:(nat_of_ord j) in
     let j' := eval compute in j' in  
     let a := fresh "a" in let b := fresh "b" in let H := fresh in
     destruct (ssrnat.leq (S j') n1) eqn:H;
  [ try discriminate H;
    clear H; 
    pose (b:=B); 
    change (fun_of_matrix (@row_mx T m n1 n2 A B) i j) with (fun_of_matrix  (@row_mx T m n1 n2 A b) i j);
    clearbody b;
    rewrite(@row_mxEl' T m n1 n2 A b i j isT); clear b; try change (nat_of_ord j) with j'
  | try discriminate H;
    clear H; 
    pose (a:=A); 
    change (fun_of_matrix (@row_mx T m n1 n2 A B) i j) with (fun_of_matrix  (@row_mx T m n1 n2 a B) i j);
    clearbody a;
    let k := constr:(subn j' n1) in let k := eval compute in k in 
    generalize (@row_mxEr' T m n1 n2 a B i j isF  k erefl isT);
    set (b := B)  at 1 3; clearbody b; intro H; rewrite H; clear H a b
 ]
end.
foo.
foo.

intro H.
rewrite H.

fold b at 1.
intro H; rewrite H.



translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 0) (Ordn 2 1)).
*)

Definition relate_2dT1deriv_0_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 0) (Ordn 2 1))).
Definition f_2dT1deriv_0_1 := ltac:(related_matrix2 relate_2dT1deriv_0_1).

Definition relate_2dT1deriv_1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 1) (Ordn 2 0))).
Definition f_2dT1deriv_1_0 := ltac:(related_matrix2 relate_2dT1deriv_1_0).

Definition relate_2dT1deriv_1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 1) (Ordn 2 1))).
Definition f_2dT1deriv_1_1 := ltac:(related_matrix2 relate_2dT1deriv_1_1).

Definition relate_2dT1deriv_2_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 2) (Ordn 2 0))).
Definition f_2dT1deriv_2_0 := ltac:(related_matrix2 relate_2dT1deriv_2_0).

Definition relate_2dT1deriv_2_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (rowmx_of_list [x;y]) (Ordn 3 2) (Ordn 2 1))).
Definition f_2dT1deriv_2_1 := ltac:(related_matrix2 relate_2dT1deriv_2_1).

Definition acc_2dT1deriv : R := 0.

Lemma prove_roundoff_bound_2dT1deriv_0_0:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_0_0) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

(*
Ltac HO_reify_float_expr names E :=
  lazymatch names with
  | ?n :: ?names' =>
      lazymatch type of E with
      | ftype ?ty -> _ => let Ev := constr:((E (placeholder ty n))) in
                          HO_reify_float_expr names' Ev
      | ?foo => fail 100 "could not reify" E foo
      end
  | [] => reify_float_expr E
  end.

*)
Definition r_2dT1_deriv_0_1 : expr Tdouble.
   match type of f_2dT1deriv_0_1 with ?t => let n := function_arity t in
        let vars := constr:(firstn_canon_idents n) in let vars := eval compute in vars in 
        let e' := HO_reify_float_expr vars f_2dT1deriv_0_1
       in exact e'
   end.


Show Proof.
Defined.

Lemma prove_roundoff_bound_2dT1deriv_0_1:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_0_1) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma prove_roundoff_bound_2dT1deriv_1_0:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_1_0) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma prove_roundoff_bound_2dT1deriv_1_1:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_1_1) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma prove_roundoff_bound_2dT1deriv_2_0:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_2_0) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Lemma prove_roundoff_bound_2dT1deriv_2_1:  
    forall vmap,  prove_roundoff_bound simplex_boundsmap_2d vmap ltac:(reify_function f_2dT1deriv_2_1) acc_2dT1deriv.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.



Definition roundoff_bound_lemma (s: Shape.shape) (bounds: boundsmap)
    (Fθ: 'rV[ftype Tdouble]_(Shape.d s) -> 'rV_(Shape.nsh s)) (acc: R)
    (Fdθ: 'rV[ftype Tdouble]_(Shape.d s) -> 'M[ftype Tdouble]_(Shape.nsh s, Shape.d s)) (accd: R)
 :=
  forall (x: 'rV[ftype Tdouble]_(Shape.d s)),
       boundsmap_denote bounds (vmap_of_rV x) -> 
     (forall (j: 'I_(Shape.nsh s)),
       @FPCore.is_finite Tdouble (Fθ x ord0 j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (Fθ x)) (oppmx (Shape.θ s (map_mx FT2R x))) ord0 j) <= acc)
 /\  (forall i j, @FPCore.is_finite Tdouble (Fdθ x i j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (Fdθ x)) (oppmx (Shape.dθ s (map_mx FT2R x))) i j) <= accd).

(*
Definition dθ_ [d n: nat] (F: 'rV[R]_d -> 'rV[R]_n) (x: 'rV[R]_d) :  'M[R]_(n, d):=
     \matrix_(i<n,j<d) 'D_('e_j) F x 0 i.
*)

Ltac prove_vmaps_equal := 
apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;
cbv beta match fix delta [ vmap_of_rV_list ord_enum seq.iota seq.pmap eqtype.insub ];
 repeat (destruct (@ssrbool.idP _); [ | lia]);
cbv beta match fix zeta iota delta [ valmap_of_list' fold_left Maps.PTree.set Maps.PTree.set0 Maps.PTree.empty map ];
simpl;
repeat f_equal; apply ord_inj; auto.


Ltac simplify_ordinal i ::=  (* Why is this redefinition necessary? *)
   (* If i reduces to a constant ordinal, replace it with the canonical   @Ordinal n i (eq_refl true)  *)
      lazymatch i with @Ordinal _ _ ssrbool.isT => fail | _ => idtac end;
      let j := eval hnf in i in
      let n := constr:(nat_of_ord j) in let n1 := eval hnf in n in 
         is_ground_nat n1; 
         match type of j with ?t => let t' := eval hnf in t in match t' with ordinal ?k => 
             replace i with (Ordn k n1) by (apply ord_inj; reflexivity)
        end end.

Ltac compute_ord_enum n ::=   (* Why is this redefinition necessary? *)
  tryif is_ground_nat n then idtac 
      else  fail "compute_ord_enum: Need a ground term natural number, but got" n; 
  pattern (ord_enum n); 
  match goal with |- ?F ?c => 
    let f := fresh "f" in set (f:=F);
      let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with (eq_refl true) by apply proof_irr; clear e | try (contradiction e; reflexivity)]);
     subst f
  end.

Lemma roundoff_bound_1dP1: roundoff_bound_lemma shapes1dP1 
        cuboid_boundsmap_1d
        (FShape.θ shapes1dP1F) acc_1dP1
        (FShape.dθ shapes1dP1F) acc_1dP1d.
Proof.
red; simpl; intro x.
rewrite shapes1dP1_deriv.
simplify_vmap_of_rV.
intro H; split; intros; revert H.
-
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap.
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord_enum_cases j;
[ generalize (prove_roundoff_bound_1dP1_0 _ H); clear H
| generalize (prove_roundoff_bound_1dP1_1 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
-
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap.
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
rewrite ord1. clear j.
ord_enum_cases i; rewrite_matrix;
[ generalize (prove_roundoff_bound_1dP1deriv_0 _ H); clear H
| generalize (prove_roundoff_bound_1dP1deriv_1 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
Qed.


Lemma roundoff_bound_1dP2: roundoff_bound_lemma shapes1dP2 
        cuboid_boundsmap_1d
        (FShape.θ shapes1dP2F) acc_1dP2
        (FShape.dθ shapes1dP2F) acc_1dP2deriv.
Proof.
red; simpl; intro x.
rewrite shapes1dP2_deriv.
simplify_vmap_of_rV.
intro H; split; intros; revert H.
-
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap;
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord_enum_cases j;
[ generalize (prove_roundoff_bound_1dP2_0 _ H); clear H
| generalize (prove_roundoff_bound_1dP2_1 _ H); clear H
| generalize (prove_roundoff_bound_1dP2_2 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
-
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap.
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord1.
ord_enum_cases i; rewrite_matrix;
[ generalize (prove_roundoff_bound_1dP2deriv_0 _ H); clear H
| generalize (prove_roundoff_bound_1dP2deriv_1 _ H); clear H
| generalize (prove_roundoff_bound_1dP2deriv_2 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
Qed.

Lemma roundoff_bound_2dP1: roundoff_bound_lemma shapes2dP1 
        cuboid_boundsmap_2d
        (FShape.θ shapes2dP1F) acc_2dP1
       (FShape.dθ shapes2dP1F) acc_2dP1deriv.
Proof.
red; simpl; intro x.
rewrite shapes2dP1_deriv.
simplify_vmap_of_rV.
intro H; split; intros; revert H.
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let f := eval unfold shapes1dP1_float in f in (* new *)
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in let g := eval unfold shapes1dP1_function in g in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
repeat match goal with | |- context [col ?i _ ] => simplify_ordinal i end; unfold col; rewrite ?mxE; (* new *)
realify; rewrite Rplus_opp.
revert VALID vmap;
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord_enum_cases j;
[ generalize (prove_roundoff_bound_2dP1_0 _ H); clear H
| generalize (prove_roundoff_bound_2dP1_1 _ H); clear H
| generalize (prove_roundoff_bound_2dP1_2 _ H); clear H
| generalize (prove_roundoff_bound_2dP1_3 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
-
unfold shapes2dP1_fderiv, shapes2dP1_deriv', shapes1dP1_float, shapes1dP1_fderiv, shapes1dP1_deriv', shapes1dP1_function, rowmx_of_list.
simpl seq.size.
replace  (@nmodule.Algebra.zero
                                       (zmodp.fintype_ordinal__canonical__Algebra_BaseAddUMagma 1))with (@Ordinal 2 0 ssrbool.isT); [ | apply ord_inj; reflexivity].
replace  (@nmodule.Algebra.zero
                                       (zmodp.fintype_ordinal__canonical__Algebra_BaseAddUMagma 0)) with (@Ordinal 1 0 ssrbool.isT); [ | apply ord_inj; reflexivity].
replace  (ssralg.GRing.one
                                    (zmodp.fintype_ordinal__canonical__GRing_PzSemiRing 0)) with (Ordn 2 1); [ | apply ord_inj; reflexivity].


match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
(*  let f := eval hnf in F in*)
  let fx := constr:(F x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
idtac (*   let g := eval hnf in G in change G with g *)
end.
unfold addmx, oppmx, map2_mx, map_mx.
 rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap.
rewrite_matrix.
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord_enum_cases j; clear j.
+
ord_enum_cases i; clear i; rewrite_matrix;
 [ generalize (prove_roundoff_bound_2dP1deriv_0_0 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_1_0 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_2_0 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_3_0 _ H); clear H
 ];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
+
ord_enum_cases i; clear i; rewrite_matrix;
 [ generalize (prove_roundoff_bound_2dP1deriv_0_1 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_1_1 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_2_1 _ H); clear H
 | generalize (prove_roundoff_bound_2dP1deriv_3_1 _ H); clear H
 ];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
Qed.

(*
Definition acc_2dP1_deriv : R := 1.  (* Placeholder! *)

Lemma roundoff_bound_2dP2: roundoff_bound_lemma shapes2dP2 
        cuboid_boundsmap_2d
        (FShape.θ shapes2dP2F) acc_2dP2
        (FShape.dθ shapes2dP2F) acc_2dP2_deriv.
Proof.
intros x j.
simpl in x; simpl in j.
simplify_vmap_of_rV.
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let f := eval unfold shapes1dP1_float, shapes1dP2_float in f in (* new *)
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in let g := eval unfold shapes1dP1_function, shapes1dP2_function in g in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
repeat match goal with | |- context [col ?i _ ] => simplify_ordinal i end; unfold col; rewrite ?mxE. (* new *)
realify; rewrite Rplus_opp.
revert VALID vmap;
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
try (  (* these prove_roundoff_bound lemmas all exist, but in a different .v file *)
ord_enum_cases j;
[ generalize (prove_roundoff_bound_2dP2_0 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_1 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_2 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_3 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_4 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_5 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_6 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_7 _ H); clear H
| generalize (prove_roundoff_bound_2dP2_8 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra).
Abort.
*)

Lemma roundoff_bound_2dT1: roundoff_bound_lemma shapes2dT1 
        simplex_boundsmap_2d
        (FShape.θ shapes2dT1F) acc_2dT1
        (FShape.dθ shapes2dT1F) acc_2dT1deriv.
Proof.
red; simpl; intro x.
rewrite shapes2dT1_deriv.
simplify_vmap_of_rV.
intro H; split; intros; revert H.
-
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
  let f := eval hnf in F in
  let f := eval unfold shapes1dP1_float in f in (* new *)
  let fx := constr:(f x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
  let g := eval hnf in G in let g := eval unfold shapes1dP1_function in g in change G with g
end.
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
repeat match goal with | |- context [col ?i _ ] => simplify_ordinal i end; unfold col; rewrite ?mxE; (* new *)
realify; rewrite Rplus_opp.
revert VALID vmap;
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
rewrite_matrix.
ord_enum_cases j;
[ generalize (prove_roundoff_bound_2dT1_0 _ H); clear H
| generalize (prove_roundoff_bound_2dT1_1 _ H); clear H
| generalize (prove_roundoff_bound_2dT1_2 _ H); clear H
];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
unfold rowmx_of_list;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite_matrix; rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
-
unfold shapes2dT1_fderiv, shapes2dT1_deriv', rowmx_of_list.
simpl seq.size.
replace  (@nmodule.Algebra.zero
                                       (zmodp.fintype_ordinal__canonical__Algebra_BaseAddUMagma 1))with (@Ordinal 2 0 ssrbool.isT); [ | apply ord_inj; reflexivity].
replace  (@nmodule.Algebra.zero
                                       (zmodp.fintype_ordinal__canonical__Algebra_BaseAddUMagma 0)) with (@Ordinal 1 0 ssrbool.isT); [ | apply ord_inj; reflexivity].
replace  (ssralg.GRing.one
                                    (zmodp.fintype_ordinal__canonical__GRing_PzSemiRing 0)) with (Ordn 2 1); [ | apply ord_inj; reflexivity].
match goal with |- _ -> _ /\ Rabs (fun_of_matrix (addmx (map_mx _ (?F ?x )) (oppmx (?G _))) _ _) <= _ => 
(*  let f := eval hnf in F in*)
  let fx := constr:(F x) in  
  let y := eval cbv beta zeta in fx in
  let z := changeStdLibToCore y in
   change (F x) with z;
idtac (*   let g := eval hnf in G in change G with g *)
end.
unfold addmx, oppmx, map2_mx, map_mx.
 rewrite !mxE.
realify; rewrite Rplus_opp.
revert VALID vmap.
repeat match goal with
 | |- context [fun_of_matrix x ?i _ ] => simplify_ordinal i
 | |- context [fun_of_matrix x  _ ?j ] => simplify_ordinal j
end;
intros VALID vmap H.
ord_enum_cases j; clear j.
+
ord_enum_cases i; clear i; rewrite_matrix;
 [ generalize (prove_roundoff_bound_2dT1deriv_0_0 _ H); clear H
 | generalize (prove_roundoff_bound_2dT1deriv_1_0 _ H); clear H
 | generalize (prove_roundoff_bound_2dT1deriv_2_0 _ H); clear H
 ];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
+
ord_enum_cases i; clear i; rewrite_matrix;
 [ generalize (prove_roundoff_bound_2dT1deriv_0_1 _ H); clear H
 | generalize (prove_roundoff_bound_2dT1deriv_1_1 _ H); clear H
 | generalize (prove_roundoff_bound_2dT1deriv_2_1 _ H); clear H
 ];
unfold prove_roundoff_bound, roundoff_error_bound;
match goal with |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
  replace F' with F; [replace X' with X; [tauto | ] | ]
end;
simpl;
cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec];
simpl;
rewrite ?mxE;
unfold Defs.F2R; simpl;
try reflexivity; try nra.
Qed.


