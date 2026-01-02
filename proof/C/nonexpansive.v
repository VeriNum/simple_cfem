(** * Machinery for proving the nonexpansiveness of object-oriented interfaces. *)
(**  All of this should be moved into VST.floyd, and documented in the reference manual or in Software Foundations vol. 5 *)

Require Import VST.floyd.proofauto.

Import rmaps.
Import compcert_rmaps.RML.R.


Lemma approx_approx_S: forall (n: nat) (P: mpred), approx n (approx (S n) P) = approx n P.
Proof.
intros.
change (base.compose (approx n) (approx (S n)) P = approx n P).
rewrite Clight_initial_world.approx_min.
rewrite Nat.min_l by lia. auto.
Qed.


Lemma approx_andp_prop: forall n P Q Q', approx n Q = approx n Q' ->
       approx n (andp (prop P) Q) = approx n (andp (prop P) Q').
Proof.
intros. rewrite !approx_andp. f_equal. auto.
Qed.

Lemma approx_andp': forall n (P P' Q Q': mpred), 
       approx n P = approx n P' -> 
       approx n Q = approx n Q' ->
       approx n (andp P Q) = approx n (andp P' Q').
Proof.
intros. rewrite !approx_andp; f_equal; auto.
Qed.

Lemma approx_sepcon': forall n (P P' Q Q': mpred),
  approx n P = approx n P' ->
  approx n Q = approx n Q' ->
  approx n (sepcon P Q) = approx n (sepcon P' Q').
Proof.
intros. rewrite !approx_sepcon; f_equal; auto.
Qed.

Lemma approx_exp': forall (A: Type) (P1 P2: A -> mpred) (n: nat),
    (forall x, approx n (P1 x) = approx n (P2 x)) ->
    approx n (exp P1) = approx n (exp P2).
Proof. intros; rewrite ?approx_exp; apply exp_congr; auto. Qed.

Lemma approx_func_ptr'': 
  forall n fsig cc A P P' Q Q' v,
   (forall x rho, approx n (P x rho) = approx n (P' x rho)) ->
   (forall x rho, approx n (Q x rho) = approx n (Q' x rho)) ->
   approx (S n) (func_ptr' (NDmk_funspec fsig cc A P Q) v) =
   approx (S n) (func_ptr' (NDmk_funspec fsig cc A P' Q') v).
Proof.
intros.
rewrite approx_func_ptr'; symmetry; rewrite approx_func_ptr'; symmetry.
apply f_equal.
f_equal.
f_equal; extensionality x rho; auto.
Qed.


Create HintDb nonexpansive.

Ltac nonexpansive_prover :=
lazymatch goal with
  |  |- args_super_non_expansive _ => intros ? ? ? ? 
  |  |- super_non_expansive _ => intros ? ? ? ? 
  |  |- approx ?n1 _ = approx ?n2 _ => first [constr_eq n1 n2 | fail 1 "Ltac nonexpansive prover requires equal approximation levels, but" n1"<>"n2]
  | _ => idtac end;
repeat match goal with 
          | |- approx _ ?A = approx _ ?B => constr_eq A B; reflexivity
          | |- approx _ (sepcon _ _) = approx _ (sepcon _ _) => apply approx_sepcon'
          | |- approx _ (andp _ _) = approx _ (andp _ _) => apply approx_andp' 
          | |- approx _ (exp _) = approx _ (exp _) => apply approx_exp'; intro
          | |- approx (S _) (func_ptr' _ _) = approx (S _) (func_ptr' _ _) => apply approx_func_ptr''; intros
          | |- approx ?n (func_ptr' _ _) = approx ?n' (func_ptr' _ _) => 
                 constr_eq n n'; is_var n; destruct n as [ | n]; [rewrite !approx_0; reflexivity | ]
          | |- approx _ (PROPx _ _ _) = approx _ (PROPx _ _ _) => apply approx_andp'
          | |- approx _ (PARAMSx _ _ _) = approx _ (PARAMSx _ _ _) => apply approx_andp'
          | |- approx _ (GLOBALSx _ _ _) = approx _ (GLOBALSx _ _ _) => apply approx_andp'
          | |- approx _ (LOCALx _ _ _) = approx _ (LOCALx _ _ _) => apply approx_andp'
          | |- approx _ (SEPx _ _) = approx _ (SEPx _ _) => apply approx_sepcon'
          | |- approx _ (match ?x with _ => _ end) = _ => destruct x
          | |- approx _ (match ?x with _ => _ end _) = _ => destruct x
          | |- approx _ (match ?x with _ => _ end _ _) = _ => destruct x
          | |- approx _ (match ?x with _ => _ end _ _ _ ) = _ => destruct x
          | |- _ => progress rewrite ?approx_idem, ?approx_approx_S
          | |- _ => progress unfold argsassert2assert
          | |- _ => progress (change (fst (?A,_)) with A; change (snd (_,?B)) with B)
          | H:  functors.MixVariantFunctor._functor _ _ |- _ => progress simpl in H
          | |- context [functors.MixVariantFunctor.fmap ?A ?B] => 
                  let b := constr: (functors.MixVariantFunctor.fmap A B)  in 
                   let b' := eval hnf in b in let b' := eval simpl in b' in  change b with b'; cbv beta match
   end;
 auto with nonexpansive.

