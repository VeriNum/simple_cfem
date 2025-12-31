Require Import VST.floyd.proofauto.
From CFEM.C Require Import assemble.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.accuracy_proofs Require Import solve_model.
From LAProof.C Require Import VSU_densemat spec_alloc floatlib matrix_model.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

(* FIXME: the following definitions & coercion should be factored out of spec_densemat *)
Notation the_type := spec_densemat.the_type.
Notation the_ctype := spec_densemat.the_ctype.
Notation val_of_float := spec_densemat.val_of_float.
Notation frobenius_norm2 := spec_densemat.frobenius_norm.
Coercion Z.of_nat : nat >-> Z.

Definition matrix_rep (t: type): Type := forall (sh: share) (X: { mn &  'M[option (ftype t)]_(fst mn, snd mn)}) (p: val), mpred.

Definition assemble_data_t := Tstruct _assemble_data_t noattr.
Definition assemble_t := Tstruct _assemble_t noattr.

Definition assemble_add_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type, 
             y: ftype the_type, x: ftype the_type
 PRE[ tptr assemble_data_t, tint, tint, the_ctype ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP(writable_share sh; A i j = Some y)
   PARAMS( p; Vint (Int.repr i); Vint (Int.repr j); Vfloat x)
   SEP(instance sh (existT _ (m,n) A) p)
 POST [ tvoid ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (update_mx A i j (Some (BPLUS y x)))) p).

Definition assemble_clear_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) A) p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (@const_mx _ m n (Some (Zconst the_type 0)))) p).


Definition assemble_norm2_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p)
 POST [ the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN(val_of_float (frobenius_norm2 A))
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p).

Definition assemble_print_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p).

Definition assemble_obj (sho sh: share) (instance: matrix_rep the_type)
          (m n: nat) (A: 'M[option (ftype the_type)]_(m,n)) (obj: val) :=
  EX p: val, EX add: val, EX clear: val, EX norm2: val, EX print: val, 
  !! (readable_share sho /\ isptr p) && 
  func_ptr' (assemble_add_spec' instance) add *
  func_ptr' (assemble_clear_spec' instance) clear *
  func_ptr' (assemble_norm2_spec' instance) norm2 *
  func_ptr' (assemble_print_spec' instance) print *
  data_at sho assemble_t (p,(add,(clear,(norm2,print)))) obj * instance sh (existT _ (m,n) A) p.

Lemma assemble_obj_local_facts: forall sho sh instance m n A obj,
   assemble_obj sho sh instance m n A obj |-- !!(isptr obj).
Proof.
intros.
unfold assemble_obj.
Intros p add clear norm2 print.
entailer!.
Qed.
#[export] Hint Resolve assemble_obj_local_facts : saturate_local.

Lemma assemble_obj_valid_pointer: forall sho sh instance m n A obj,
  sepalg.nonidentity sho ->
   assemble_obj sho sh instance m n A obj |-- valid_pointer obj.
Proof.
intros.
unfold assemble_obj.
Intros p add clear norm2 print.
entailer!.
Qed.
#[export] Hint Resolve assemble_obj_valid_pointer : valid_pointer.

Definition matrix_package : Type :=  
  {mn: nat*nat & matrix (option (ftype the_type)) (fst mn) (snd mn)}%type.


Definition matrix_and_indices : Type :=  
  {mn: nat*nat & matrix (option (ftype the_type)) (fst mn) (snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type.


Import rmaps.

Definition matrix_package_typetree : TypeTree := 
  SigType (nat*nat) (fun mn => ConstType ('M[option (ftype the_type)]_(fst mn, snd mn))).

Definition test_typetree (tree: TypeTree) (type: Type) :=
  forall t,  (functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil (AssertTT tree)) t) = (type -> environ -> t).

Goal test_typetree matrix_package_typetree matrix_package. intro; reflexivity. Abort.

Definition matrix_and_indices_typetree: TypeTree :=
  SigType (nat*nat) (fun mn => ConstType ('M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)))).

Goal test_typetree matrix_and_indices_typetree matrix_and_indices. intro; reflexivity. Abort.

Definition matrix_rep_type : TypeTree :=
   ProdType (ConstType share) 
     (ArrowType (ConstType  {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}) (ArrowType (ConstType val) Mpred)).

Definition assemble_add_type := 
  ProdType (ConstType (val * share * share * matrix_and_indices * ftype the_type * ftype the_type))
                   (ArrowType (ConstType share) (ArrowType (ConstType matrix_package) (ArrowType (ConstType val) Mpred))).


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

Ltac nonexpansive_prover :=
lazymatch goal with
  |  |- args_super_non_expansive _ => intros ? ? ? ? 
  |  |- super_non_expansive _ => intros ? ? ? ? 
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
          | H:  functors.MixVariantFunctor._functor _ _ |- _ => progress simpl in H
          | |- _ => progress simpl
   end.

Lemma assemble_obj_super_non_expansive : forall n' sho sh inst m n A obj,
compcert_rmaps.RML.R.approx n' (assemble_obj sho sh inst m n A obj) =
compcert_rmaps.RML.R.approx n'
  (assemble_obj sho sh
     (fun (a : share) (a0 : matrix_package) (a1 : val) => compcert_rmaps.RML.R.approx n' (inst a a0 a1)) m n A obj).
Proof.
intros.
unfold assemble_obj.
nonexpansive_prover.
Qed.

Program Definition assemble_add_spec :=
 DECLARE _assemble_add
 TYPE assemble_add_type
 WITH obj: val, sho: share, sh: share, 
             X: matrix_and_indices, 
             y: ftype the_type, x: ftype the_type,
             inst: matrix_rep the_type
 PRE[ tptr assemble_t, tint, tint, the_ctype ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP(writable_share sh; A i j = Some y)
   PARAMS( obj; Vint (Int.repr i); Vint (Int.repr j); Vfloat x) GLOBALS()
   SEP (assemble_obj sho sh inst m n A obj)
 POST [ tvoid ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP()
   RETURN()
   SEP (assemble_obj sho sh inst m n (update_mx A i j (Some (BPLUS y x))) obj).
Next Obligation.
nonexpansive_prover.
apply assemble_obj_super_non_expansive.
Qed.
Next Obligation.
nonexpansive_prover.
apply assemble_obj_super_non_expansive.
Qed.

Definition dense_matrix_rep : matrix_rep the_type := 
  fun (sh: share) (X: { mn &  'M[option (ftype the_type)]_(fst mn, snd mn)}) (p: val) => 
   spec_densemat.densemat sh (projT2 X) p.

Definition casted_densemat_add_spec :=
 DECLARE _casted_densemat_add (assemble_add_spec' dense_matrix_rep).

Definition casted_densemat_clear_spec :=
 DECLARE _casted_densemat_clear (assemble_clear_spec' dense_matrix_rep).

Definition casted_densemat_norm2_spec :=
 DECLARE _casted_densemat_norm2 (assemble_norm2_spec' dense_matrix_rep).

Definition casted_densemat_print_spec :=
 DECLARE _casted_densemat_print (assemble_print_spec' dense_matrix_rep).

Definition init_assemble_dense_spec :=
 DECLARE _init_assemble_dense
 WITH obj: val, sho: share,  p: val, shp: share, X: { mn &  'M[option (ftype the_type)]_(fst mn, snd mn)}%type, gv: globals
 PRE [ tptr assemble_t , tptr spec_densemat.densemat_t ]
   PROP(writable_share sho)
   PARAMS (obj; p) GLOBALS(gv)
   SEP(data_at_ sho assemble_t obj; spec_densemat.densemat shp (projT2 X) p)
 POST [ tvoid ]
   PROP()
   RETURN()
   SEP(assemble_obj sho shp dense_matrix_rep _ _ (projT2 X) obj).


Definition assemble_ASI: funspecs :=
 [ assemble_add_spec; casted_densemat_add_spec;
   casted_densemat_clear_spec; casted_densemat_norm2_spec; casted_densemat_print_spec;
   init_assemble_dense_spec ].



