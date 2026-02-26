From CFEM Require Import shape shapefloat.
From mathcomp Require Import Rstruct.

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

Definition x_vmap_list (x : ftype Tdouble) :=
   [(1%positive, existT ftype _ x)].

Definition x_vmap (x : ftype Tdouble) : valmap :=
 ltac:(make_valmap_of_list (x_vmap_list x)).

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

Import matrix matrix_util fintype.

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

(*
Ltac nthtac n L :=
 match n with
 | O => match L with ?A :: _ => A end
 | S ?n' => match L with _ :: ?A => nthtac n' A end
 end.
*)

Ltac simplify_mx A :=
 match A with
  |  context C [fun_of_matrix (const_mx ?x) _ _] => 
            let g := context C [x] in
            simplify_mx g 
  | context C [fun_of_matrix ?F ?X] =>
     lazymatch F with (fun _ => _) =>  idtac end;
     let a := constr:(F X) in let a := eval cbv beta in a in 
     let g := context C [a] in
     simplify_mx g
  | context C [fun_of_matrix (rowmx_of_list ?L) _ ?k] =>
     let k' := constr:(nat_of_ord k) in let k' := eval compute in k' in 
     let a := constr:(nth k' L (Zconst Tdouble 0)) in
     let a := eval cbv beta fix match delta [nth] in a in 
     let g := context C [a] in simplify_mx g
  | context C [@row _ ?k _ _ ?E] => unify k 1%nat; let g := context C [E] in simplify_mx g
  | context C [@col _ _ ?k _ ?E] => unify k 1%nat; let g := context C [E] in simplify_mx g
  | context C [row ?k (@col_mx _ ?m1 ?m2 _ ?E ?F)] =>
     let k' := constr:(nat_of_ord k) in let a := constr:(Nat.ltb k' m1) in let a := eval compute in a in 
     match a with
     | true => let i := constr:(@Ordinal m1 k' (eq_refl _)) in let g := context C [row i E] in simplify_mx g
     |false => let i0 := constr:((k'-m1)%nat) in let i0 := eval compute in i0 in
                    let i := constr:(@Ordinal m2 i0 (eq_refl _)) in let g := context C [row i F] in simplify_mx g
    end
  | context C [col ?k (@row_mx _ _ ?n1 ?n2 ?E ?F)] =>
     let k' := constr:(nat_of_ord k) in let a := constr:(Nat.ltb k' n1) in let a := eval compute in a in 
     match a with
     | true => let i := constr:(@Ordinal n1 k' (eq_refl _)) in let g := context C [row i E] in simplify_mx g
     |false => let i0 := constr:((k'-n1)%nat) in let i0 := eval compute in i0 in
                    let i := constr:(@Ordinal n2 i0 (eq_refl _)) in let g := context C [row i F] in simplify_mx g
    end
  | context C [fun_of_matrix (@row_mx _ _ ?n1 ?n2 ?E ?F) ?i ?k] =>
     let k' := constr:(nat_of_ord k) in let k' := eval compute in k' in
      let a := constr:(Nat.ltb k' n1) in let a := eval compute in a in 
     match a with
     | true => let g := context C [E i (@Ordinal n1 k' (eq_refl _))] in simplify_mx g
     |false => let i0 := constr:((k'-n1)%nat) in let i0 := eval compute in i0 in
                     let g := context C [F i (@Ordinal n2 i0 (eq_refl _))] in simplify_mx g
     end
  | context C [fun_of_matrix (@col_mx _ ?m1 ?m2 _ ?E ?F) ?k ?j] =>
     let k' := constr:(nat_of_ord k) in let k' := eval compute in k' in
      let a := constr:(Nat.ltb k' m1) in let a := eval compute in a in 
     match a with
     | true => let g := context C [E (@Ordinal m1 k' (eq_refl _)) j] in simplify_mx g
     |false => let i0 := constr:((k'-m1)%nat) in let i0 := eval compute in i0 in
                     let g := context C [F (@Ordinal m2 i0 (eq_refl _)) j] in simplify_mx g
     end
  |  context C [fun_of_matrix (const_mx ?a) _ ?k] => 
      unify (nat_of_ord k) 0%nat;
       let g := context C [a] in simplify_mx g
  | context [@rowmx_of_list] => let g := eval cbv beta fix match delta [rowmx_of_list] in A in simplify_mx g
  | _ => let f := changeStdLibToCore A in exact f
  end.

Ltac matrix_expression f i j := 
let f := red_to_rowmx f in
let f := eval cbv beta delta [shapes1dP1_float] in f in
let f := eval cbv zeta in f in 
let f := changeStdLibToCore f in
match type of f with @matrix _ ?m ?n => 
 let A := constr:(fun_of_matrix f (@Ordinal m i (eq_refl _)) (@Ordinal n j (eq_refl _))) in
 simplify_mx A
end.

Local Definition test_1dP1_0 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes1dP1_float (rowmx_of_list [x])) 0%nat 0%nat).

Goal test_1dP1_0 = (fun x : ftype Tdouble => (0.5 * (1 - x))%F64). reflexivity. Abort.

Local Definition test_2dP1_0 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dP1_float (rowmx_of_list [x;y])) 0%nat 0%nat).

Goal test_2dP1_0 = (fun x y : ftype Tdouble => (0.5 * (1 - x) * (0.5 * (1 - y)))%F64). reflexivity. Abort.

Lemma ord_enum_cases: forall [n] (P: 'I_n -> Prop),
  Forall P (ord_enum n) ->
  forall i, P i.
Proof.
intros.
rewrite Forall_forall in H.
apply H.
clear.
pose proof @nth_ord_enum' n i i.
rewrite mv_mathcomp.nth_List_nth in H.
rewrite <- H.
apply nth_In.
rewrite size_ord_enum.
pose proof (ltn_ord i); lia.
Qed. 

Ltac is_ground_nat x := lazymatch x with O => idtac | S ?k => is_ground_nat k end.

Ltac compute_ord_enum n := 
  (is_ground_nat n + fail "compute_ord_enum: Need a ground term natural number, but got" n); 
  pattern (ord_enum n); 
  match goal with |- ?F _ => 
    let f := fresh "f" in set (f:=F);
      let c := constr:(ord_enum n) in let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with (eq_refl true) by apply proof_irr; clear e | try (contradiction e; reflexivity)]);
     subst f
  end.

Ltac ord_enum_cases j :=
 lazymatch type of j with ordinal ?n => 
  pattern j; 
  apply ord_enum_cases;
  compute_ord_enum n;
  repeat apply Forall_cons; try apply Forall_nil
 end.

Ltac realify := 
change (@nmodule.Algebra.add _) with Rplus;
change (@nmodule.Algebra.opp _) with Ropp;
change (@ssralg.GRing.mul _) with Rmult;
change (@ssralg.GRing.inv _) with Rinv;
change (ssralg.GRing.one _) with 1;
repeat change (nmodule.Algebra.natmul _ ?i) with (INR i).


Definition f_1dP1_0 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes1dP1_float (rowmx_of_list [x])) 0%nat 0%nat).

Definition f_1dP1_1 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (FShape.θ shapes1dP1F (rowmx_of_list [x])) 0%nat 1%nat).

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

Definition f_1dP1deriv_0 (x: ftype Tdouble) := 
     ltac:(matrix_expression (shapes1dP1_fderiv (rowmx_of_list [x])) 0%nat 0%nat).

Definition f_1dP1deriv_1 (x: ftype Tdouble) := 
     ltac:(matrix_expression (shapes1dP1_fderiv (rowmx_of_list [x])) 1%nat 0%nat).

Lemma prove_roundoff_bound_1dP1deriv_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1deriv_0) 0.
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
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_1d vmap ltac:(reify_function f_1dP1deriv_1) 0.
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval; interval.
-
 prove_roundoff_bound2.
 rewrite Rminus_diag. rewrite Rabs_R0. apply Rle_refl.
Qed.

Definition f_1dP2_0 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes1dP2_float (rowmx_of_list [x])) 0%nat 0%nat).

Definition f_1dP2_1 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes1dP2_float (rowmx_of_list [x]))  0%nat 1%nat).

Definition f_1dP2_2 (x: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes1dP2_float (rowmx_of_list [x])) 0%nat 2%nat).

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


Lemma prove_roundoff_bound_1dP2_3:  
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

Definition f_2dP1_0 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dP1_float (rowmx_of_list [x;y])) 0%nat 0%nat).

Definition f_2dP1_1 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dP1_float (rowmx_of_list [x;y])) 0%nat 1%nat).

Definition f_2dP1_2 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dP1_float (rowmx_of_list [x;y])) 0%nat 2%nat).

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


Definition f_2dT1_0 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dT1_float (rowmx_of_list [x;y])) 0%nat 0%nat).

Definition f_2dT1_1 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dT1_float (rowmx_of_list [x;y])) 0%nat 1%nat).

Definition f_2dT1_2 (x y: ftype Tdouble) : ftype Tdouble
  := ltac:(matrix_expression (shapes2dT1_float (rowmx_of_list [x;y])) 0%nat 2%nat).

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


Lemma roundoff_bound_1dP1 : forall (x: 'rV[ftype Tdouble]_1) (j: 'I_2),
       FPCore.is_finite (x ord0 ord0) = true ->
       -1 <= FT2R (x ord0 ord0) <= 1 ->
       @FPCore.is_finite Tdouble (FShape.θ shapes1dP1F x ord0 j) = true /\
       Rabs (addmx (map_mx (@FT2R Tdouble) (FShape.θ shapes1dP1F x)) 
                    (oppmx (Shape.θ shapes1dP1 (map_mx FT2R x)))
                      ord0 j) <= acc_1dP1.
Proof.
intros.
set (x00 := x ord0 ord0) in *.
assert (boundsmap_denote cuboid_boundsmap_1d (x_vmap x00)). {
 apply boundsmap_denote_i; simpl; auto.
 eexists. split; [  |split]; auto. reflexivity. split; auto.
}
ord_enum_cases j; clear j.
-
destruct (prove_roundoff_bound_1dP1_0 (x_vmap x00) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
set (fx := FShape.θ _ _ _ _); change (FShape.θ _ _ _ _) with fx.
match type of H3 with Rabs (FT2R ?M - _) <= _ => assert (fx = M) end. {
 subst fx. simpl. unfold shapes1dP1_float. unfold rowmx_of_list; row_col_matrix_tac. reflexivity.
}
rewrite H4; clear H4 fx.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
f_equal.
simpl.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
change (x _ _) with x00.
change (env_ _ _ _ 1%positive) with x00.
unfold Defs.F2R; simpl.
nra.
-
destruct (prove_roundoff_bound_1dP1_1 (x_vmap x00) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
set (fx := FShape.θ _ _ _ _); change (FShape.θ _ _ _ _) with fx.
match type of H3 with Rabs (FT2R ?fv - _) <= _ => assert (fx = fv) end. {
 subst fx. simpl. unfold shapes1dP1_float. unfold rowmx_of_list; row_col_matrix_tac. reflexivity.
}
rewrite H4; clear H4 fx.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
f_equal.
simpl.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
change (x _ _) with x00.
change (env_ _ _ _ 1%positive) with x00.
unfold Defs.F2R; simpl; nra.
Qed.


