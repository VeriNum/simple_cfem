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

Lemma split_shift1 [m j]: lt j m -> is_true (ssrnat.leq (S j) m).
Proof. lia. Qed.


Lemma split_shift2 [m n] [j: 'I_(m+n)] : not (lt (nat_of_ord j) m) -> is_true (ssrnat.leq (S (nat_of_ord j - m)) n).
Proof. intros. pose proof (ltn_ord j). lia. Qed.

Definition split_shift [m n] (j: 'I_(m+n)) :=
   match Compare_dec.lt_dec j m
   with left H => @lshift m n (@Ordinal _ (nat_of_ord j) (split_shift1 H))
         | right H => @rshift m n (@Ordinal _ (nat_of_ord j - m) (split_shift2 H))
   end.

Lemma split_shift_eq: forall [m n] (j: 'I_(m+n)), j = split_shift j.
Proof.
intros.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); apply ord_inj; simpl; auto.
lia.
Qed.

Lemma row_mxE: forall [T: Type][m n1 n2: nat] (A1: 'M[T]_(m,n1)) (A2: 'M[T]_(m,n2)) (i: 'I_m) (j: 'I_(n1+n2)),
    row_mx A1 A2 i j = 
    match Compare_dec.lt_dec (nat_of_ord j) n1
    with left H => A1 i  (@Ordinal n1 (nat_of_ord j) (split_shift1 H))
         | right H => A2 i (@Ordinal n2 (nat_of_ord j - n1) (split_shift2 H))
     end.
Proof.
intros.
pose proof (split_shift_eq j).
rewrite H at 1.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
apply row_mxEl.
apply row_mxEr.
Qed.


Lemma col_mxE: forall [T: Type][m1 m2 n: nat] (A1: 'M[T]_(m1,n)) (A2: 'M[T]_(m2,n)) (i: 'I_(m1+m2)) (j: 'I_n),
    col_mx A1 A2 i j = 
    match Compare_dec.lt_dec (nat_of_ord i) m1
    with left H => A1 (@Ordinal m1 (nat_of_ord i) (split_shift1 H)) j
         | right H => A2 (@Ordinal m2 (nat_of_ord i - m1) (split_shift2 H)) j
     end.
Proof.
intros.
pose proof (split_shift_eq i).
rewrite H at 1.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
apply col_mxEu.
apply col_mxEd.
Qed.

Lemma row_0_1: forall [T: Type] [n: nat] (A: 'M[T]_(1,n)) i, row i A = A.
Proof.
intros.
rewrite ord1. clear i.
apply matrixP. intros i j.
unfold row.
rewrite mxE.
f_equal.
symmetry; apply ord1.
Qed.

Lemma col_0_1: forall [T: Type] [n: nat] (A: 'M[T]_(n,1)) j, col j A = A.
Proof.
intros.
rewrite ord1.  clear j.
apply matrixP. intros i j.
unfold col.
rewrite mxE.
f_equal.
symmetry; apply ord1.
Qed.


Lemma row_col_E: forall [T: Type] [m1 m2 n] (A: 'M[T]_(m1,n)) (B: 'M[T]_(m2,n)) (i: 'I_(m1+m2)),
      row i (col_mx A B) =
    match Compare_dec.lt_dec (nat_of_ord i) m1
    with left H => row (@Ordinal m1 (nat_of_ord i) (split_shift1 H)) A
         | right H => row (@Ordinal m2 (nat_of_ord i - m1) (split_shift2 H)) B
     end.
Proof.
intros.
pose proof (split_shift_eq i).
rewrite H at 1.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
rewrite <- row_usubmx, col_mxKu. auto.
rewrite <- row_dsubmx, col_mxKd. auto.
Qed.

Lemma col_row_E: forall [T: Type] [m n1 n2] (A: 'M[T]_(m,n1)) (B: 'M[T]_(m,n2)) (j: 'I_(n1+n2)),
      col j (row_mx A B) =
    match Compare_dec.lt_dec (nat_of_ord j) n1
    with left H => col (@Ordinal n1 (nat_of_ord j) (split_shift1 H)) A
         | right H => col (@Ordinal n2 (nat_of_ord j - n1) (split_shift2 H)) B
     end.
Proof.
intros.
pose proof (split_shift_eq j).
rewrite H at 1.
unfold split_shift.
destruct (Compare_dec.lt_dec _ _); simpl.
rewrite <- col_lsubmx, row_mxKl. auto.
rewrite <- col_rsubmx, row_mxKr. auto.
Qed.

Ltac rewrite_matrix := 
repeat
match goal with
  | |- context [fun_of_matrix (@row_mx ?T ?m ?n1 ?n2 _ _) ?i ?j ] =>
             rewrite (@row_mxE T m n1 n2);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) n1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia); try (replace (@split_shift1 _ _ H) with (eq_refl true) by apply proof_irr; clear H)
              | try (exfalso; clear - H; lia); 
                try (replace (@split_shift2 n1 n2 (@Ordinal _ _ (@eq_refl bool (ssrnat.leq _ _))) H) with (eq_refl true) by apply proof_irr ; clear H)] 
  | |- context [fun_of_matrix (@col_mx ?T ?m1 ?m2 ?n _ _) ?i ?j ] =>
             rewrite (@col_mxE T m1 m2 n);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) m1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia); try (replace (@split_shift1 _ _ H) with (eq_refl true) by apply proof_irr; clear H)
              | try (exfalso; clear - H; lia); 
                try (replace (@split_shift2 m1 m2 (@Ordinal _ _ (@eq_refl bool (ssrnat.leq _ _))) H) with (eq_refl true) by apply proof_irr ; clear H)] 
   | |- context [@col ?T' ?m' ?n' ?j (@row_mx ?T ?m ?n1 ?n2 ?A ?B)] =>
             change m' with m; change n' with (n1+n2)%nat; change T' with T;
             rewrite (@col_row_E T m n1 n2 A B j);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) n1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia); try (replace (@split_shift1 _ _ H) with (eq_refl true) by apply proof_irr; clear H)
              | try (exfalso; clear - H; lia); 
                try (replace (@split_shift2 n1 n2 (@Ordinal _ _ (@eq_refl bool (ssrnat.leq _ _))) H) with (eq_refl true) by apply proof_irr ; clear H)] 
   | |- context [@row ?T' ?m' ?n' ?j (@col_mx ?T ?m1 ?m2 ?n ?A ?B)] =>
             change m' with (m1+m2)%nat; change n' with n; change T' with T;
             rewrite (@row_col_E T m1 m2 n A B j);
              let H := fresh in 
               destruct (Compare_dec.lt_dec (nat_of_ord _) m1) as [H | H];
               simpl in H; simpl nat_of_ord;
               [try (exfalso; clear - H; lia); try (replace (@split_shift1 _ _ H) with (eq_refl true) by apply proof_irr; clear H)
              | try (exfalso; clear - H; lia); 
                try (replace (@split_shift2 m1 m2 (@Ordinal _ _ (@eq_refl bool (ssrnat.leq _ _))) H) with (eq_refl true) by apply proof_irr ; clear H)] 
  | |- _ => rewrite const_mxE
  | |- _ => rewrite row_0_1
  | |- _ => rewrite col_0_1
  | |- _ => rewrite row_col_E
  | |- _ => rewrite col_row_E
  | i: 'I_1 |- _ =>  let H := fresh in assert (H := ord1 i); simpl in H; subst i
  | H: 'I__ |- _ => progress simpl in H
  | H: ~(nat_of_ord _ < _)%nat |- _ => simpl in H
  | _ => lia
       end.

Ltac translate_matrix f := 
let x := fresh "x" in 
let g := fresh "g" in 
evar (g: ftype Tdouble -> ftype Tdouble);
let H := fresh in 
let prop := constr:(forall x : ftype Tdouble, f x = g x) in let prop := eval cbv beta in prop in 
assert (H: prop);  [
  intro x;
 unfold FShape.θ, FShape.dθ; simpl;
 match goal with |- fun_of_matrix ?a _ _ = _ => 
        let b := eval red in a in let b := changeStdLibToCore b in change a with b 
  end;
 unfold rowmx_of_list; simpl seq.size;
 rewrite_matrix;
  subst g; reflexivity
 | subst g;  exact H].

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

Ltac related_matrix f := let x :=
     fresh "x" in intro x;
    match type of (f x) with _ = ?t => let b := eval cbv beta in t in exact b end.
 
Definition relate_1dP1_0  
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (rowmx_of_list [x]) ord0 (@Ordinal 2 0 (eq_refl _)))).
Definition f_1dP1_0 := ltac:(related_matrix relate_1dP1_0).

Goal f_1dP1_0 = fun x : ftype Tdouble => (0.5 * (1 - x))%F64.  reflexivity. Abort.  
Definition   relate_1dP1_1
 := ltac:(translate_matrix (fun x => FShape.θ shapes1dP1F (rowmx_of_list [x]) ord0 (@Ordinal 2 1 (eq_refl _)))).

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
   ltac:(translate_matrix (fun x => shapes1dP1_fderiv (rowmx_of_list [x]) (@Ordinal 2 0 (eq_refl _)) ord0)).
Definition f_1dP1deriv_0 := ltac:(related_matrix relate_1dP1deriv_0).

Definition relate_1dP1deriv_1 := 
   ltac:(translate_matrix (fun x => shapes1dP1_fderiv (rowmx_of_list [x]) (@Ordinal 2 1 (eq_refl _)) ord0)).
Definition f_1dP1deriv_1 := ltac:(related_matrix relate_1dP1deriv_1).

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

Definition relate_1dP2_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (@Ordinal 3 0 (eq_refl _)))).
Definition f_1dP2_0 := ltac:(related_matrix relate_1dP2_0).

Definition relate_1dP2_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (@Ordinal 3 1 (eq_refl _)))).
Definition f_1dP2_1 := ltac:(related_matrix relate_1dP2_1).

Definition relate_1dP2_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_float  (rowmx_of_list [x]) ord0 (@Ordinal 3 2 (eq_refl _)))).
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



Definition relate_1dP2deriv_0 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (@Ordinal 3 0 (eq_refl _)) ord0)).
Definition f_1dP2deriv_0 := ltac:(related_matrix relate_1dP2deriv_0).

Definition relate_1dP2deriv_1 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (@Ordinal 3 1 (eq_refl _)) ord0)).
Definition f_1dP2deriv_1 := ltac:(related_matrix relate_1dP2deriv_1).

Definition relate_1dP2deriv_2 := 
   ltac:(translate_matrix (fun x => shapes1dP2_fderiv (rowmx_of_list [x]) (@Ordinal 3 2 (eq_refl _)) ord0)).
Definition f_1dP2deriv_2 := ltac:(related_matrix relate_1dP2deriv_2).


Definition acc_1dP2deriv : R := 4 / IZR (Z.pow_pos 10 16).

Lemma prove_roundoff_bound_1dP2deriv_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_1dP2deriv_0) acc_1dP2deriv.
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
 unfold FShape.θ, FShape.dθ; simpl;
 match goal with |- fun_of_matrix ?a _ _ = _ => 
        let b := eval red in a in change a with b 
  end;
 unfold shapes1dP1_float, shapes1dP1_fderiv;
 unfold rowmx_of_list; simpl seq.size;
  match goal with |- ?A => let b := changeStdLibToCore A in change b end;
 rewrite_matrix;
  subst g; reflexivity
 | subst g;  exact H].

Ltac related_matrix2 f := let x := fresh "x" in intro x; let y := fresh "y" in intro y;
    match type of (f x y) with _ = ?t => let b := eval cbv beta in t in exact b end.
 
Definition relate_2dP1_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 4 0 (eq_refl _)))).
Definition f_2dP1_0 := ltac:(related_matrix2 relate_2dP1_0).

Definition relate_2dP1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 4 1 (eq_refl _)))).
Definition f_2dP1_1 := ltac:(related_matrix2 relate_2dP1_1).

Definition relate_2dP1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 4 2 (eq_refl _)))).
Definition f_2dP1_2 := ltac:(related_matrix2 relate_2dP1_2).

Definition relate_2dP1_3 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 4 3 (eq_refl _)))).
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


Definition relate_2dP1deriv_0 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (@Ordinal 4 0 (eq_refl _)) ord0)).
Definition f_2dP1deriv_0 := ltac:(related_matrix2 relate_2dP1deriv_0).

Definition relate_2dP1deriv_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (@Ordinal 4 1 (eq_refl _)) ord0)).
Definition f_2dP1deriv_1 := ltac:(related_matrix2 relate_2dP1deriv_1).

Definition relate_2dP1deriv_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (@Ordinal 4 2 (eq_refl _)) ord0)).
Definition f_2dP1deriv_2 := ltac:(related_matrix2 relate_2dP1deriv_2).

Definition relate_2dP1deriv_3 := 
   ltac:(translate_matrix2 (fun x y => shapes2dP1_fderiv (rowmx_of_list [x;y]) (@Ordinal 4 3 (eq_refl _)) ord0)).
Definition f_2dP1deriv_3 := ltac:(related_matrix2 relate_2dP1deriv_3).


Derive acc_2dP1deriv
 in  (forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_0)  acc_2dP1deriv)
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


Lemma prove_roundoff_bound_2dP1deriv_0:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_0) acc_2dP1deriv.
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

Lemma prove_roundoff_bound_2dP1deriv_1:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_1) acc_2dP1deriv.
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


Lemma prove_roundoff_bound_2dP1deriv_2:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_2) acc_2dP1deriv.
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

Lemma prove_roundoff_bound_2dP1deriv_3:  
    forall vmap,  prove_roundoff_bound cuboid_boundsmap_2d vmap ltac:(reify_function f_2dP1deriv_3) acc_2dP1deriv.
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
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 3 0 (eq_refl _)))).
Definition f_2dT1_0 := ltac:(related_matrix2 relate_2dT1_0).

Definition relate_2dT1_1 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 3 1 (eq_refl _)))).
Definition f_2dT1_1 := ltac:(related_matrix2 relate_2dT1_1).

Definition relate_2dT1_2 := 
   ltac:(translate_matrix2 (fun x y => shapes2dT1_float  (rowmx_of_list [x;y]) ord0 (@Ordinal 3 2 (eq_refl _)))).
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

Lemma rowmx_of_list_1: forall [T] (x: 'M[T]_1), rowmx_of_list [x ord0 ord0] = x.
Proof.
intros.
unfold rowmx_of_list; apply matrixP; intros ? ?;  rewrite_matrix; auto.
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
assert (boundsmap_denote cuboid_boundsmap_1d (x_vmap (x ord0 ord0))). {
 apply boundsmap_denote_i; simpl; auto.
 eexists. split; [  |split]; auto. reflexivity. split; auto.
}
ord_enum_cases j; clear j.
-
destruct (prove_roundoff_bound_1dP1_0 (x_vmap (x ord0 ord0)) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
change (FPStdLib.ftype FPStdLib.Tdouble) with (ftype Tdouble).
rewrite <- rowmx_of_list_1 at 1 2.
rewrite relate_1dP1_0.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
simpl.
f_equal.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
set (x2 := x _ _).
change (env_ _ _ _ _) with x2.
unfold Defs.F2R; simpl.
nra.
-
destruct (prove_roundoff_bound_1dP1_1 (x_vmap (x ord0 ord0)) H1).
unfold addmx, oppmx, map2_mx, map_mx; rewrite !mxE.
realify.
rewrite Rplus_opp.
change (FPStdLib.ftype FPStdLib.Tdouble) with (ftype Tdouble).
rewrite <- rowmx_of_list_1 at 1 2.
rewrite relate_1dP1_1.
split; auto.
match goal with H: Rabs ?A <= acc_1dP1 |- Rabs ?B <= _ => replace B with A; auto end.
clear.
simpl.
f_equal.
unfold shapes1dP1_function.
unfold rowmx_of_list; row_col_matrix_tac; rewrite !mxE.
realify.
set (x2 := x _ _).
change (env_ _ _ _ _) with x2.
unfold Defs.F2R; simpl.
nra.
Qed.


