Require Import VST.floyd.proofauto.
From CFEM.C Require Import matrix.
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

Require Import CFEM.C.nonexpansive.

Open Scope logic.

(* FIXME: the following definitions & coercion should be factored out of spec_densemat *)
Notation the_type := spec_densemat.the_type.
Notation the_ctype := spec_densemat.the_ctype.
Notation val_of_float := spec_densemat.val_of_float.
Notation frobenius_norm2 := spec_densemat.frobenius_norm2.
Coercion Z.of_nat : nat >-> Z.

Definition matrix_rep (t: type): Type := forall (sh: share) (X: { mn &  'M[option (ftype t)]_(fst mn, snd mn)}) (p: val), mpred.

Definition matrix_data_t := Tstruct _matrix_data_t noattr.
Definition matrix_t := Tstruct _matrix_t noattr.

Definition matrix_add_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type, 
             y: ftype the_type, x: ftype the_type
 PRE[ tptr matrix_data_t, tint, tint, the_ctype ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP(writable_share sh; A i j = Some y)
   PARAMS( p; Vint (Int.repr i); Vint (Int.repr j); Vfloat x)
   SEP(instance sh (existT _ (m,n) A) p)
 POST [ tvoid ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (update_mx A i j (Some (BPLUS y x)))) p).

Definition matrix_clear_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type
 PRE[ tptr matrix_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) A) p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (@const_mx _ m n (Some (Zconst the_type 0)))) p).


Definition matrix_norm2_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr matrix_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p)
 POST [ the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN(val_of_float (frobenius_norm2 A))
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p).

Definition matrix_print_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr matrix_data_t ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh (existT _ (m,n) (map_mx Some A)) p).

Definition matrix_obj (sho sh: share) (instance: matrix_rep the_type)
          (m n: nat) (A: 'M[option (ftype the_type)]_(m,n)) (obj: val) :=
  EX p: val, EX add: val, EX clear: val, EX norm2: val, EX print: val, 
  !! (readable_share sho /\ isptr p) && 
  func_ptr' (matrix_add_spec' instance) add *
  func_ptr' (matrix_clear_spec' instance) clear *
  func_ptr' (matrix_norm2_spec' instance) norm2 *
  func_ptr' (matrix_print_spec' instance) print *
  data_at sho matrix_t (p,(add,(clear,(norm2,print)))) obj * instance sh (existT _ (m,n) A) p.

Lemma matrix_obj_local_facts: forall sho sh instance m n A obj,
   matrix_obj sho sh instance m n A obj |-- !!(isptr obj).
Proof.
intros.
unfold matrix_obj.
Intros p add clear norm2 print.
entailer!.
Qed.
#[export] Hint Resolve matrix_obj_local_facts : saturate_local.

Lemma matrix_obj_valid_pointer: forall sho sh instance m n A obj,
  sepalg.nonidentity sho ->
   matrix_obj sho sh instance m n A obj |-- valid_pointer obj.
Proof.
intros.
unfold matrix_obj.
Intros p add clear norm2 print.
entailer!.
Qed.
#[export] Hint Resolve matrix_obj_valid_pointer : valid_pointer.

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

Lemma matrix_obj_nonexpansive : forall n' sho sh inst m n A obj,
compcert_rmaps.RML.R.approx n' (matrix_obj sho sh inst m n A obj) =
compcert_rmaps.RML.R.approx n'
  (matrix_obj sho sh
     (fun (a : share) (a0 : matrix_package) (a1 : val) => compcert_rmaps.R.approx n' (inst a a0 a1)) m n A obj).
Proof.
intros.
unfold matrix_obj.
nonexpansive_prover.
Qed.
Hint Resolve matrix_obj_nonexpansive : nonexpansive.


Definition matrix_add_type := 
  ProdType (ConstType (val * share * share * matrix_and_indices * ftype the_type * ftype the_type))
                   (ArrowType (ConstType share) (ArrowType (ConstType matrix_package) (ArrowType (ConstType val) Mpred))).

Program Definition matrix_add_spec :=
 DECLARE _matrix_add
 TYPE matrix_add_type
 WITH obj: val, sho: share, sh: share, 
             X: matrix_and_indices, 
             y: ftype the_type, x: ftype the_type,
             inst: matrix_rep the_type
 PRE[ tptr matrix_t, tint, tint, the_ctype ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP(writable_share sh; A i j = Some y)
   PARAMS( obj; Vint (Int.repr i); Vint (Int.repr j); Vfloat x) GLOBALS()
   SEP (matrix_obj sho sh inst m n A obj)
 POST [ tvoid ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP()
   RETURN()
   SEP (matrix_obj sho sh inst m n (update_mx A i j (Some (BPLUS y x))) obj).
Next Obligation.
nonexpansive_prover.
Qed.
Next Obligation.
nonexpansive_prover.
Qed.

Definition matrix_clear_type := 
  ProdType (ConstType (val * share * share * matrix_package))
                   (ArrowType (ConstType share) (ArrowType (ConstType matrix_package) (ArrowType (ConstType val) Mpred))).

Program Definition matrix_clear_spec :=
 DECLARE _matrix_clear
 TYPE matrix_clear_type
 WITH obj: val, sho: share, sh: share, 
             X: matrix_package,
             inst: matrix_rep the_type
 PRE[ tptr matrix_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( obj ) GLOBALS()
   SEP (matrix_obj sho sh inst m n A obj)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP (matrix_obj sho sh inst m n (@const_mx _ m n (Some (Zconst the_type 0))) obj).
Next Obligation.
nonexpansive_prover.
Qed.
Next Obligation.
nonexpansive_prover.
Qed.

Definition matrix_norm2_type := 
  ProdType (ConstType (val * share * share *  {mn: nat*nat & matrix (ftype the_type) (fst mn) (snd mn)}))
                   (ArrowType (ConstType share) (ArrowType (ConstType  matrix_package) (ArrowType (ConstType val) Mpred))).

Program Definition matrix_norm2_spec :=
 DECLARE _matrix_norm2
 TYPE matrix_norm2_type
 WITH obj: val, sho: share, sh: share, 
             X:  {mn: nat*nat & matrix (ftype the_type) (fst mn) (snd mn)}%type,
             inst: matrix_rep the_type
 PRE[ tptr matrix_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( obj ) GLOBALS()
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj)
 POST [ the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN(val_of_float (frobenius_norm2 A))
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj).
Next Obligation.
nonexpansive_prover.
Qed.
Next Obligation.
nonexpansive_prover.
Qed.

Program Definition matrix_norm_spec :=
 DECLARE _matrix_norm
 TYPE matrix_norm2_type
 WITH obj: val, sho: share, sh: share, 
             X:  {mn: nat*nat & matrix (ftype the_type) (fst mn) (snd mn)}%type,
             inst: matrix_rep the_type
 PRE[ tptr matrix_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( obj ) GLOBALS()
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj)
 POST [ the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN(val_of_float (BSQRT (frobenius_norm2 A)))
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj).
Next Obligation.
nonexpansive_prover.
Qed.
Next Obligation.
nonexpansive_prover.
Qed.

Definition matrix_print_type := 
  ProdType (ConstType (val * share * share *  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}))
                   (ArrowType (ConstType share) (ArrowType (ConstType matrix_package) (ArrowType (ConstType val) Mpred))).

Program Definition matrix_print_spec :=
 DECLARE _matrix_print
 TYPE matrix_print_type
 WITH obj: val, sho: share, sh: share, 
             X:  {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)},
             inst: matrix_rep the_type
 PRE[ tptr matrix_t ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( obj ) GLOBALS()
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP (matrix_obj sho sh inst m n (map_mx Some A) obj).
Next Obligation.
nonexpansive_prover.
Qed.
Next Obligation.
nonexpansive_prover.
Qed.

Definition dense_matrix_rep : matrix_rep the_type := 
  fun (sh: share) (X: { mn &  'M[option (ftype the_type)]_(fst mn, snd mn)}) (p: val) => 
   spec_densemat.densemat sh (projT2 X) p.

Definition casted_densemat_add_spec :=
 DECLARE _casted_densemat_add (matrix_add_spec' dense_matrix_rep).

Definition casted_densemat_clear_spec :=
 DECLARE _casted_densemat_clear (matrix_clear_spec' dense_matrix_rep).

Definition casted_densemat_norm2_spec :=
 DECLARE _casted_densemat_norm2 (matrix_norm2_spec' dense_matrix_rep).

Definition casted_densemat_print_spec :=
 DECLARE _casted_densemat_print (matrix_print_spec' dense_matrix_rep).

Definition init_matrix_dense_spec :=
 DECLARE _init_matrix_dense
 WITH obj: val, sho: share,  p: val, shp: share, X: { mn &  'M[option (ftype the_type)]_(fst mn, snd mn)}%type, gv: globals
 PRE [ tptr matrix_t , tptr spec_densemat.densemat_t ]
   PROP(writable_share sho)
   PARAMS (obj; p) GLOBALS(gv)
   SEP(data_at_ sho matrix_t obj; spec_densemat.densemat shp (projT2 X) p)
 POST [ tvoid ]
   PROP()
   RETURN()
   SEP(matrix_obj sho shp dense_matrix_rep _ _ (projT2 X) obj).


Definition casted_bandmat_add_spec : ident*funspec := 
 (_casted_bandmat_add, vacuous_funspec (Internal f_casted_bandmat_add)).
Definition casted_bandmat_clear_spec : ident*funspec := 
 (_casted_bandmat_clear, vacuous_funspec (Internal f_casted_bandmat_clear)).
Definition casted_bandmat_norm2_spec : ident*funspec := 
 (_casted_bandmat_norm2, vacuous_funspec (Internal f_casted_bandmat_norm2)).
Definition casted_bandmat_print_spec : ident*funspec := 
 (_casted_bandmat_print, vacuous_funspec (Internal f_casted_bandmat_print)).
Definition init_matrix_band_spec : ident*funspec := 
 (_init_matrix_band, vacuous_funspec (Internal f_init_matrix_band)).

Definition matrix_ASI: funspecs :=
 [ matrix_add_spec; casted_densemat_add_spec;
   matrix_clear_spec; casted_densemat_clear_spec; 
   matrix_norm2_spec; casted_densemat_norm2_spec; matrix_norm_spec;
   matrix_print_spec; casted_densemat_print_spec;
   init_matrix_dense_spec;
   casted_bandmat_add_spec; casted_bandmat_clear_spec;
   casted_bandmat_norm2_spec; casted_bandmat_print_spec;
   init_matrix_band_spec ].




