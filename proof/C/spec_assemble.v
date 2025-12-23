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

(** The next lines are usual in VST specification files *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

(* FIXME: the following definitions & coercion should be factored out of spec_densemat *)
Notation the_type := spec_densemat.the_type.
Notation the_ctype := spec_densemat.the_ctype.
Notation val_of_float := spec_densemat.val_of_float.
Notation frobenius_norm2 := spec_densemat.frobenius_norm.
Coercion Z.of_nat : nat >-> Z.

Definition matrix_rep (t: type): Type := forall (sh: share) (m n: nat) (M: 'M[option (ftype t)]_(m,n)) (p: val), mpred.

Definition assemble_t := Tstruct _assemble_t noattr.

Definition assemble_add_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type, 
             y: ftype the_type, x: ftype the_type
 PRE[ tptr assemble_t, tint, tint, the_ctype ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP(writable_share sh; A i j = Some y)
   PARAMS( p; Vint (Int.repr i); Vint (Int.repr j); Vfloat x)
   SEP(instance sh m n A p)
 POST [ tvoid ] let '(existT _ (m,n) (A,(i,j))) := X in 
   PROP()
   RETURN()
   SEP(instance sh m n (update_mx A i j (Some (BPLUS y x))) p).


Definition assemble_clear_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_t, tint, tint, the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP(writable_share sh)
   PARAMS( p )
   SEP(instance sh m n A p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh m n (@const_mx _ m n (Some (Zconst the_type 0))) p).


Definition assemble_norm2_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_t, tint, tint, the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh m n (map_mx Some A) p)
 POST [ the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN(val_of_float (frobenius_norm2 A))
   SEP(instance sh m n (map_mx Some A) p).

Definition assemble_print_spec' (instance: matrix_rep the_type) :=
 WITH p: val, sh: share, X: {mn: nat*nat & 'M[ftype the_type]_(fst mn, snd mn)}%type
 PRE[ tptr assemble_t, tint, tint, the_ctype ] let '(existT _ (m,n) A) := X in 
   PROP(readable_share sh)
   PARAMS( p )
   SEP(instance sh m n (map_mx Some A) p)
 POST [ tvoid ] let '(existT _ (m,n) A) := X in 
   PROP()
   RETURN()
   SEP(instance sh m n (map_mx Some A) p).

Compute reptype assemble_t.

Definition assemble_obj (sh: share) (instance: matrix_rep the_type)
          (m n: nat) (A: 'M[option (ftype the_type)]_(m,n)) (obj: val) :=
  EX sho: share, EX p: val, EX add: val, EX clear: val, EX norm2: val, EX print: val, 
  !! readable_share sho && 
  func_ptr' (assemble_add_spec' instance) add *
  func_ptr' (assemble_clear_spec' instance) clear *
  func_ptr' (assemble_norm2_spec' instance) norm2 *
  func_ptr' (assemble_print_spec' instance) print *
  data_at sh assemble_t (p,(add,(clear,(norm2,print)))) obj * instance sh m n A p.

Lemma assemble_obj_local_facts: forall sh instance m n A obj,
   assemble_obj sh instance m n A obj |-- !!(isptr obj).
Proof.
intros.
unfold assemble_obj.
Intros sho p add clear norm2 print.
entailer!.
Qed.
#[export] Hint Resolve assemble_obj_local_facts : saturate_local.





