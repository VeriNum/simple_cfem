(** * CFEM.shape_accuracy:  Roundoff-error bounds for shape functions *)

(**  We prove:
  - Within the bounding box, each of the floating-point shape functions approximates the real-valued shape functions within specified error bounds
  - Wiithin the bounding box, each of the floating-point shape-derivative functions approximates the real-valued ones within specified bounds
  - The vertices of the Shape all fit within the bounding box of the FShape.
*)

(* begin details : Require Imports and Open Scope, etc. *)
From CFEM Require Import shape shapefloat.
From mathcomp Require Import Rstruct.
Import matrix matrix_util fintype.
Import shapefloat.Bounds.

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Stdlib.Lists.List ListNotations.
From LAProof Require Import matrix_model.

Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.
(* end details *)

(* begin hide *)
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
(* end hide *)

(** Not-a-number propagation rules:  Use the same ones that CompCert uses (on this target architecture) *)
Existing Instance FPCompCert.nans.

(** * The Shape Accuracy Property *)

(** First, let's get some supporting definitions out of the way: *)
Definition vmap_of_cV_list [n] (x: 'cV[ftype Tdouble]_n) :=
      map (fun i => (Pos.of_succ_nat (nat_of_ord i), existT ftype _ (fun_of_matrix x i ord0))) (ord_enum n).

Lemma vmap_of_cV_list_valid: forall [n] (x: 'cV[ftype Tdouble]_n),
  @valmap_valid empty_collection (valmap_of_list' (@vmap_of_cV_list n x)).
(* begin details *)
Proof.
intros.
unfold vmap_of_cV_list.
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
(* end details *)

Definition  vmap_of_cV [n](x: 'cV[ftype Tdouble]_n) : valmap :=
   @valmap_of_list empty_collection (vmap_of_cV_list x) (vmap_of_cV_list_valid x).

(** *** bounds_enclose:
   A given boundsmap (cuboid bounding box) really does contain
   all the vertices of a shape. *)
Definition bounds_enclose (s: Shape.shape) (bm: boundsmap) : Prop :=
 forall i: 'I_(Shape.d s),
  match Maps.PTree.get (Pos.of_succ_nat (nat_of_ord i)) bm with
    | Some {| var_type := t; var_name := i'; var_lobound := lo; var_hibound := hi |} =>
      forall k: 'I_(Shape.nsh s),
         lo <= Shape.vtx s i k <= hi
    | None => False
    end.

(** *** roundoff_bound_lemma: The accuracy proof of a set of shape functions #<a href=RBL># *)

(** Given [s] that is a set of real-valued shape functions (and derivatives, and vertices),
   and given [F] that is a set of float-valued shape functions (and bounding box), then
 - The bounding box of [F] encloses the vertices of [s]
 - The float-valued shape functions approximate the real-valued shape functions within [acc].
 - The float-valued shape derivative functions approximate the real-valued shape derivative functions within [accd].
*)

Definition roundoff_bound_lemma (s: Shape.shape)
    (F: FShape.shape (Shape.d s) (Shape.nsh s) FPStdLib.Tdouble)
    (acc accd: R)
 :=
  bounds_enclose s (FShape.bounds F) /\
  forall (x: 'cV[ftype Tdouble]_(Shape.d s)),
       boundsmap_denote (FShape.bounds F) (vmap_of_cV x) -> 
     (forall (j: 'I_(Shape.nsh s)),
       @FPCore.is_finite Tdouble (FShape.θ F x ord0 j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (FShape.θ F x)) (oppmx (Shape.θ s (map_mx FT2R x))) ord0 j) <= acc)
 /\  (forall i j, @FPCore.is_finite Tdouble (FShape.dθ F x i j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (FShape.dθ F x)) (oppmx (Shape.dθ s (map_mx FT2R x))) i j) <= accd).

(** In the remainder of this file, we develop the lemmas and tactics useful in proving this for each
  of our elements, and then prove it for each element. *)

(** ** Utility tactics and lemmas*)
Ltac change_StdLib_to_Core :=
 change (@FPStdLib.BMULT FPCompCert.nans FPStdLib.Tdouble) with (@BMULT FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BMINUS FPCompCert.nans FPStdLib.Tdouble) with (@BMINUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BPLUS FPCompCert.nans FPStdLib.Tdouble) with (@BPLUS FPCompCert.nans Tdouble is_standard_Tdouble);
 change (@FPStdLib.BOPP FPCompCert.nans FPStdLib.Tdouble) with (@BOPP FPCompCert.nans Tdouble is_standard_Tdouble).

Ltac translate_matrix f := 
let x := fresh "x" in 
let g := fresh "g" in 
evar (g: ftype Tdouble -> ftype Tdouble);
let H := fresh in 
let prop := constr:(forall x : ftype Tdouble, f x = g x) in let prop := eval cbv beta in prop in 
assert (H: prop);  [
  intro x;
(* match goal with |- fun_of_matrix _ ?i ?j = _ =>  try simplify_ordinal i; try simplify_ordinal j end; *)
 repeat
  lazymatch goal  with
  | |- fun_of_matrix (rowmx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix (colmx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix (mx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix ?a _ _ = _ => let b := eval red in a in change a with b
  end;
 simplify_ordinals;
 simpl seq.size;
 rewrite_matrix;
 change_StdLib_to_Core;
 subst g; reflexivity
 | subst g;  exact H].

Ltac related_matrix f := let x :=
     fresh "x" in intro x;
    match type of (f x) with _ = ?t => let b := eval cbv beta in t in exact b end.

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
  | |- fun_of_matrix (mx_of_list _) _ _ = _ => fail
  | |- fun_of_matrix ?a _ _ = _ => let b := eval red in a in change a with b
  end;
 unfold shapes1dP1_float, shapes1dP1_fderiv, shapes1dP2_float, shapes1dP2_fderiv;
 repeat match goal with |- context [col ?i _] =>  try simplify_ordinal i end;
 repeat match goal with |- context [fun_of_matrix _ ?i _] =>  simplify_ordinal i end;
 repeat match goal with |- context [fun_of_matrix _ _ ?j] =>  simplify_ordinal j end;
 simpl seq.size;
 rewrite_matrix;
 change_StdLib_to_Core;
  subst g; reflexivity
 | subst g;  exact H].

Ltac related_matrix2 f := let x := fresh "x" in intro x; let y := fresh "y" in intro y;
    match type of (f x y) with _ = ?t => let b := eval cbv beta in t in exact b end.

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
(* begin details *)
Proof.
intros.
unfold rowmx_of_list; apply matrixP; intros ? ?. simpl in y.
unfold row_mx, const_mx; rewrite !mxE.
unfold fintype.split. rewrite ord1. simpl.
destruct (ssrnat.ltnP 0 1); try lia.
rewrite mxE.
f_equal. apply ord_inj; simpl. rewrite ord1. auto.
Qed.
(* end details *)

Ltac simplify_vmap_of_cV :=
let u := fresh "u" in set (u := @vmap_of_cV _ _ );
  pattern u; subst u;
  let G := fresh "G" in 
  match goal with |- ?A _ => set (G:=A) end;
  cbv [vmap_of_cV rowmx_of_list valmap_of_list valmap_of_list'
                               vmap_of_cV_list make_valmap]; simpl seq.size;
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

Local Ltac function_arity t :=
  lazymatch t with _ -> ?B => let n := function_arity B in constr:(S n) | _ => constr:(O) end.

Ltac reify_function f := 
   match type of f with ?t => let n := function_arity t in
        let vars := constr:(firstn_canon_idents n) in let vars := eval compute in vars in 
        let e' := HO_reify_float_expr vars f 
        in exact e'
   end.

Ltac prove_vmaps_equal := 
apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;
cbv beta match fix delta [ vmap_of_cV_list ord_enum seq.iota seq.pmap eqtype.insub ];
 repeat (destruct (@ssrbool.idP _); [ | lia]);
cbv beta match fix zeta iota delta [ valmap_of_list' fold_left Maps.PTree.set Maps.PTree.set0 Maps.PTree.empty map ];
simpl;
repeat f_equal; apply ord_inj; auto.


Ltac apply_roundoff_bound B := 
 simplify_ordinals; rewrite_matrix;
 try change (ssralg.GRing.one _) with 1; try change (nmodule.Algebra.zero _) with 0;
 let H := fresh in intro H;
 generalize (B _ H); clear H;
 realify; 
 rewrite ?Rplus_opp;
 unfold prove_roundoff_bound, roundoff_error_bound;
 match goal with vmap:= _ : valmap |- _ /\ Rabs (FT2R ?F - ?X) <= _ -> _ /\ Rabs (FT2R ?F' - ?X') <= _  => 
 replace F' with F; [replace X' with X; [tauto | ] | ];
 simpl;
 cbv [env_ vmap proj1_sig Maps.PTree.get Maps.PTree.get' typesize_eq_dec Defs.F2R]; simpl;
 try reflexivity; try nra
end.

Ltac prepare_apply_roundoff_bound := 
 change_StdLib_to_Core;
 try change (ssralg.GRing.one _) with 1; try change (nmodule.Algebra.zero _) with 0;
 match goal with VALID: valmap_valid _, vmap:= _ : valmap  |-  _  => 
   revert VALID vmap; simplify_ordinals; intros VALID vmap
 end;
 rewrite_matrix;
 unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE;
 realify; rewrite Rplus_opp.

Ltac prove_bounds_enclose :=
 let i := fresh "i" in let k := fresh "k" in 
red; simpl; intro i; ord_enum_cases i; simpl; intro k; ord_enum_cases k;
 repeat
  lazymatch goal  with
  | |- _ <= fun_of_matrix (rowmx_of_list _) _ _ <=  _ => fail
  | |- _ <= fun_of_matrix (colmx_of_list _) _ _ <= _ => fail
  | |- _ <= fun_of_matrix (mx_of_list _) _ _ <= _ => fail
  | |- _ <= fun_of_matrix ?a _ _ <= _ => let b := eval red in a in change a with b
 end;
 rewrite_matrix; realify; lra.

(** * Instances: accuracy proofs for all the elements *)

(** ** 1dP1: 1-dimensional, degree 1 *)

(** *** Extracting the floating-point shape functions into "ordinary" floating-point operations *)
(** The VCFloat tool can prove roundoff-error bounds for functions from #\(R^n \rightarrow R\)#,
   or rather, for floating-point functions that are intended to approximate those real-valued functions.
   Since our shape functions are from #\(F^d \rightarrow F^{nsh}\)#, we must first extract each
   of the columns of the row-vector ['cV_nsh] that represents #\(F^{nsh}\)#, and recast it into
   the floating-point operators that VCFloat recognizes.  This is done by the [translate_matrix] tactic.
*)

Definition relate_1dP1_0  (* first shape function *)
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (mx_of_list [[x]]) ord0 (Ordn 2 0))).

(** From the following [Check] command you can see what [translate_matrix] does.
  It has taken the jth shape function (in this case, j=Ordn 2 0, that is, shape function 0 of 2),
   and produced a proof that it's equal to (0.5 * (1-x)), with 0.5, *, and - interpreted as 64-bit float operators *)
Check relate_1dP1_0.  (*
  relate_1dP1_0:  forall x : ftype Tdouble,
       FShape.θ shapes1dP1F (mx_of_list [[x]]) ord0 (Ordn 2 0) = (0.5 * (1 - x))%F64
*)

(** And the [related_matrix] tactic grabs just the function (fun x => 0.5 * (1-x)) without the proof *)
Definition f_1dP1_0 := ltac:(related_matrix relate_1dP1_0).
(** Test that this really worked: *)
Goal f_1dP1_0 = fun x : ftype Tdouble => (0.5 * (1 - x))%F64.  reflexivity. Abort.  

Definition   relate_1dP1_1
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (mx_of_list [[x]]) ord0 (Ordn 2 1))).

Definition f_1dP1_1 := ltac:(related_matrix relate_1dP1_1).

(** *** Calculating the error bound *)

(** VCFloat's basic theorem is 
  [ forall vmap,  prove_roundoff_bound boundsmap vmap F  acc], where
 - [F] is the syntax tree describing a floating-point function of n variables,
 - [vmap] is basically a vector of n variables,
 - [boundsmap] is the lower and upper bounds for each of the n variables,
 - [acc] is a real number giving the accuracy bound.
 The theorem states that for any input [vmap] within the range [boundsmap], the difference between
 [F(vmap)] interpreted as a floating-point function, and [F(vmap)] interpreted as a real function,
  is less than or equal to [acc].

  VCFloat can prove such theorems; and when used with the [Derive] command, it can also 
  calculate the value of [acc].
*)

(** calculate what the 1dP1 bound should be (also prove it, but we'll throw away this proof  *)
Derive acc_1dP1_0
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_0)  acc_1dP1_0)
 as derive_roundoff_bound_1dP1_0.
(* begin show *)
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
(* end show *)

Check ltac:(ShowBound acc_1dP1_0).  (* 1.1102230246251587e-16%F64 *)

(** So, the bound is just under 1.2 * 10^-16.  We'll use 12/(10^17) as the value.
     To keep things simple, we'll use the same bound for all the shape functions in a given element.
     The true bound might be different for the different shape functions, so we'll just use the biggest one.
     The automation shown here doesn't automatically choose the biggest one, we have to figure that out
     by trial and error. *)

Definition acc_1dP1 : R := 12 / IZR (Z.pow_pos 10 17).

(** *** first shape function *)

(** This is the standard recipe for using VCFloat *)
Lemma prove_roundoff_bound_1dP1_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_0) acc_1dP1.
(* begin show *)
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
(* end show *)

(** *** second shape function *)
Lemma prove_roundoff_bound_1dP1_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1_1) acc_1dP1.
(* begin details *)
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
(* end details *)

(** *** derivative function accuracy bounds *)

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

(** *** 1dP1 main result *)
(** Bundle together all the accuracy proofs for 1dP1 into a single theorem *)
Lemma roundoff_bound_1dP1: 
   roundoff_bound_lemma shapes1dP1 shapes1dP1F acc_1dP1 acc_1dP1d.
(* begin show *)
Proof.
split.
prove_bounds_enclose.
simpl; intro x.
simplify_vmap_of_cV.
intro H; split; intros; revert H.
-
unfold shapes1dP1_float, shapes1dP1_θ.
prepare_apply_roundoff_bound.
ord_enum_cases j.
apply_roundoff_bound prove_roundoff_bound_1dP1_0.
apply_roundoff_bound prove_roundoff_bound_1dP1_1.
-
unfold shapes1dP1_fderiv, shapes1dP1_dθ.
prepare_apply_roundoff_bound.
ord_enum_cases i.
apply_roundoff_bound prove_roundoff_bound_1dP1deriv_0.
apply_roundoff_bound prove_roundoff_bound_1dP1deriv_1.
Qed.
(* end show *)

(** ** 1dP2: 1-dimensional, degree 2 *)

(** *** Extracting the floating-point shape functions into "ordinary" floating-point operations *)

Definition relate_1dP2_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (mx_of_list [[x]]) ord0 (Ordn 3 0))).
Definition f_1dP2_0 := ltac:(related_matrix relate_1dP2_0).

Definition relate_1dP2_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (mx_of_list [[x]]) ord0 (Ordn 3 1))).
Definition f_1dP2_1 := ltac:(related_matrix relate_1dP2_1).

Definition relate_1dP2_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (mx_of_list [[x]]) ord0 (@Ordn 3 2))).
Definition f_1dP2_2 := ltac:(related_matrix relate_1dP2_2).

(** calculate what the 1dP2 bound should be (also prove it, but we'll throw away this proof  *)
Derive acc_1dP2_1
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_1)  acc_1dP2_1)
 as derive_roundoff_bound_1dP_1.
(* begin details *)
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
(* end details *)

Check ltac:(ShowBound acc_1dP2_1). (* 1.3322676295501908e-15%F64 *)

Definition acc_1dP2: R := 14 / IZR (Z.pow_pos 10 14).

(** *** first shape function *)
Lemma prove_roundoff_bound_1dP2_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP2_0) acc_1dP2.
(* begin details *)
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
(* end details *)

(** *** second shape function *)
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

(** *** third shape function *)
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

(** *** shape derivative functions *)

Definition relate_1dP2deriv_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (mx_of_list [[x]]) (Ordn 3 0) ord0)).
Definition f_1dP2deriv_0 := ltac:(related_matrix relate_1dP2deriv_0).

Definition relate_1dP2deriv_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (mx_of_list [[x]]) (Ordn 3 1) ord0)).
Definition f_1dP2deriv_1 := ltac:(related_matrix relate_1dP2deriv_1).

Definition relate_1dP2deriv_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (mx_of_list [[x]]) (Ordn 3 2) ord0)).
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

(** *** 1dP2 main result *)
(** Bundle together all the accuracy proofs for 1dP2 into a single theorem *)
Lemma roundoff_bound_1dP2: roundoff_bound_lemma shapes1dP2 
         shapes1dP2F acc_1dP2 acc_1dP2deriv.
(* begin details *)
Proof.
split.
prove_bounds_enclose.
simpl; intro x.
simplify_vmap_of_cV.
intro H; split; intros; revert H.
-
unfold shapes1dP2_float, shapes1dP2_θ.
prepare_apply_roundoff_bound.
ord_enum_cases j.
apply_roundoff_bound prove_roundoff_bound_1dP2_0.
apply_roundoff_bound prove_roundoff_bound_1dP2_1.
apply_roundoff_bound prove_roundoff_bound_1dP2_2.
-
unfold shapes1dP2_fderiv, shapes1dP2_dθ.
prepare_apply_roundoff_bound.
ord_enum_cases i.
apply_roundoff_bound prove_roundoff_bound_1dP2deriv_0.
apply_roundoff_bound prove_roundoff_bound_1dP2deriv_1.
apply_roundoff_bound prove_roundoff_bound_1dP2deriv_2.
Qed.
(* end details *)

(** ** 2dP1: 2-dimensional, degree 1 *)

(** *** Extracting the floating-point shape functions into "ordinary" floating-point operations *)

Definition relate_2dP1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 4 0))).
Definition f_2dP1_0 := ltac:(related_matrix2 relate_2dP1_0).

Definition relate_2dP1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 4 1))).
Definition f_2dP1_1 := ltac:(related_matrix2 relate_2dP1_1).

Definition relate_2dP1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 4 2))).
Definition f_2dP1_2 := ltac:(related_matrix2 relate_2dP1_2).

Definition relate_2dP1_3 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 4 3))).
Definition f_2dP1_3 := ltac:(related_matrix2 relate_2dP1_3).

(** calculate what the 2dP1 bound should be (also prove it, but we'll throw away this proof  *)
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

(** *** four shape functions *)
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

(** *** shape derivative functions *)
Definition relate_2dP1deriv_0_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 0) (Ordn 2 0))).
Definition f_2dP1deriv_0_0 := ltac:(related_matrix2 relate_2dP1deriv_0_0).

Definition relate_2dP1deriv_0_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 0) (Ordn 2 1))).
Definition f_2dP1deriv_0_1 := ltac:(related_matrix2 relate_2dP1deriv_0_1).

Definition relate_2dP1deriv_1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 1) (Ordn 2 0))).
Definition f_2dP1deriv_1_0 := ltac:(related_matrix2 relate_2dP1deriv_1_0).

Definition relate_2dP1deriv_1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 1) (Ordn 2 1))).
Definition f_2dP1deriv_1_1 := ltac:(related_matrix2 relate_2dP1deriv_1_1).

Definition relate_2dP1deriv_2_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 2) (Ordn 2 0))).
Definition f_2dP1deriv_2_0 := ltac:(related_matrix2 relate_2dP1deriv_2_0).

Definition relate_2dP1deriv_2_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 2) (Ordn 2 1))).
Definition f_2dP1deriv_2_1 := ltac:(related_matrix2 relate_2dP1deriv_2_1).

Definition relate_2dP1deriv_3_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 3) (Ordn 2 0))).
Definition f_2dP1deriv_3_0 := ltac:(related_matrix2 relate_2dP1deriv_3_0).

Definition relate_2dP1deriv_3_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (mx_of_list [[x];[y]]) (Ordn 4 3) (Ordn 2 1))).
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

(** *** 2dP1 main result #<a id=2dP1># *)
(** Bundle together all the accuracy proofs for 2dP1 into a single theorem *)
Lemma roundoff_bound_2dP1: roundoff_bound_lemma shapes2dP1 
         shapes2dP1F acc_2dP1 acc_2dP1deriv.
(* begin details *)
Proof.
split.
prove_bounds_enclose.
simpl; intro x.
simplify_vmap_of_cV.
intro H; split; intros; revert H.
-
unfold shapes2dP1_float, shapes2dP1_θ, shapes1dP1_float, shapes1dP1_θ.
prepare_apply_roundoff_bound.
ord_enum_cases j.
apply_roundoff_bound prove_roundoff_bound_2dP1_0.
apply_roundoff_bound prove_roundoff_bound_2dP1_1.
apply_roundoff_bound prove_roundoff_bound_2dP1_2.
apply_roundoff_bound prove_roundoff_bound_2dP1_3.
-
unfold shapes2dP1_fderiv, shapes2dP1_dθ, shapes1dP1_float, shapes1dP1_fderiv, shapes1dP1_dθ, shapes1dP1_θ.
prepare_apply_roundoff_bound.
ord_enum_cases j; ord_enum_cases i.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_0_0.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_1_0.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_2_0.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_3_0.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_0_1.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_1_1.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_2_1.
apply_roundoff_bound prove_roundoff_bound_2dP1deriv_3_1.
Qed.
(* end details *)

(** *** 2dT1 main result *)
(** ** 2dT1: 2-dimensional triangle, degree 1 *)

(** *** Extracting the floating-point shape functions into "ordinary" floating-point operations *)

Definition relate_2dT1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 3 0))).
Definition f_2dT1_0 := ltac:(related_matrix2 relate_2dT1_0).

Definition relate_2dT1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 3 1))).
Definition f_2dT1_1 := ltac:(related_matrix2 relate_2dT1_1).

Definition relate_2dT1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (mx_of_list [[x];[y]]) ord0 (Ordn 3 2))).
Definition f_2dT1_2 := ltac:(related_matrix2 relate_2dT1_2).

(** calculate what the 2dP1 bound should be (also prove it, but we'll throw away this proof  *)
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

(** *** three shape functions *)

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

(** *** shape derivative functions *)
Definition relate_2dT1deriv_0_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 0) (Ordn 2 0))).
Definition f_2dT1deriv_0_0 := ltac:(related_matrix2 relate_2dT1deriv_0_0).

Definition relate_2dT1deriv_0_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 0) (Ordn 2 1))).
Definition f_2dT1deriv_0_1 := ltac:(related_matrix2 relate_2dT1deriv_0_1).

Definition relate_2dT1deriv_1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 1) (Ordn 2 0))).
Definition f_2dT1deriv_1_0 := ltac:(related_matrix2 relate_2dT1deriv_1_0).

Definition relate_2dT1deriv_1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 1) (Ordn 2 1))).
Definition f_2dT1deriv_1_1 := ltac:(related_matrix2 relate_2dT1deriv_1_1).

Definition relate_2dT1deriv_2_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 2) (Ordn 2 0))).
Definition f_2dT1deriv_2_0 := ltac:(related_matrix2 relate_2dT1deriv_2_0).

Definition relate_2dT1deriv_2_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_fderiv (mx_of_list [[x];[y]]) (Ordn 3 2) (Ordn 2 1))).
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

(** *** 2dT1 main result *)
(** Bundle together all the accuracy proofs for 2dT1 into a single theorem *)
Lemma roundoff_bound_2dT1: 
  roundoff_bound_lemma shapes2dT1 shapes2dT1F acc_2dT1 acc_2dT1deriv.
(* begin details *)
Proof.
split.
prove_bounds_enclose.
simpl; intro x.
simplify_vmap_of_cV.
intro H; split; intros; revert H.
-
unfold shapes2dT1_float, shapes2dT1_θ.
prepare_apply_roundoff_bound.
ord_enum_cases j.
apply_roundoff_bound prove_roundoff_bound_2dT1_0.
apply_roundoff_bound prove_roundoff_bound_2dT1_1.
apply_roundoff_bound prove_roundoff_bound_2dT1_2.
-
unfold shapes2dT1_fderiv, shapes2dT1_dθ.
prepare_apply_roundoff_bound.
ord_enum_cases j; ord_enum_cases i.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_0_0.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_1_0.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_2_0.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_0_1.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_1_1.
apply_roundoff_bound prove_roundoff_bound_2dT1deriv_2_1.
Qed.
(* end details *)

(** ** 2dP2: 2-dimensional, degree 2 *)

(** Not yet done *)
(** ** 2dS2: 2-dimensional, degree 2, Serendipity *)

(** Not yet done *)


