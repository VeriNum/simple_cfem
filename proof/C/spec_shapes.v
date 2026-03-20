(** * CFEM.C.spec_shapes:  VST function specification for shape *)

(**  For each kind of finite element (1dP1, 1dP2, 2dP1, 2dT1, etc.) the C program has a single
  function that calculates all the shape functions and their derivatives, as matrix values.
  We can give a single, generic specification for all these C functions, calculated from
  the functional model of the FShape. *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From CFEM.C Require Import shapes.
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
Import spec_densemat.

Open Scope logic.

Require Import CFEM.shapefloat.
(* end details *)

(** The C program calculate the shapes, or derivatives (respectively), only if the
  corresponding pointer (at which to store the result) is non-NULL.  So we need a
  function for "optional" memory predicates. *)

Definition ifptr (p: val) (A: mpred) : mpred :=
 match p with Vptr _ _ => A  |  _ => emp  end.

(** The standard boilerplate lemma for any user-defined mpred *)
Lemma ifptr_valid_pointer: forall p (A: val -> mpred), 
    is_pointer_or_null p ->
     (A p |-- valid_pointer p) -> 
    ifptr p (A p) |-- valid_pointer p.
Proof.
intros.
unfold ifptr;
destruct p; try contradiction; auto with valid_pointer.
unfold valid_pointer, valid_pointer'.
red in H.
destruct Archi.ptr64; try contradiction.
change (emp |-- !! (i = Int64.zero)).
apply prop_right.
auto.
Qed.

Hint Resolve ifptr_valid_pointer: valid_pointer.

(** ** [shape_spec]:  VST funspec of C shape function    #<a id=spec_shape>#
 Given [shape], which is a floating-point functional model of shape-functions, 
  specify the C function. *)
Definition shape_spec (d nsh: nat) (shape: FShape.shape d nsh the_type) : funspec :=
   let '({| FShape.θ := θ; FShape.dθ := dθ |}) := shape in  
  WITH shN: share, shxx:share, pN : val, pdN: val, x: 'cV[ftype the_type]_d, pxx: val
  PRE [ tptr the_ctype, tptr the_ctype, tptr the_ctype ]
    PROP(writable_share shN; readable_share shxx; is_pointer_or_null pN; is_pointer_or_null pdN)
    PARAMS( pN; pdN; pxx)
    SEP(ifptr pN (densematn shN (@const_mx (option(ftype the_type)) 1 nsh None) pN);
             ifptr pdN (densematn shN (@const_mx (option(ftype the_type)) nsh d None) pdN);
             densematn shxx (map_mx Some x) pxx)
  POST[ tint ]
    PROP()
    RETURN (Vint (Int.repr nsh))
    SEP(ifptr pN (densematn shN (map_mx Some (θ x)) pN);
             ifptr pdN (densematn shN (map_mx Some (dθ x)) pdN);
             densematn shxx (map_mx Some x) pxx).
(** What this means:
  This spec, when instantiated for a particular dimension [d], number of shape functions [nsh], floating-point
   precision [the_type] and FShape on [n], [d] and [the_type], gives a funspec as follows.
  - For all permission shares [shN] for accessing the shape matrix, and [shxx] for accessing the input vector
  - For all pointers [pN] for where to store the function values, [pdN] for where to store the derivative values, and [pxx] for accessing the vector [x],
  - For all [x] that's a vector of [d] floating-pointer numbers in precision [the_type],
  PRECONDITION: all three function parameters in C have C-language type pointer-to-float,
  - PROP: assume the share [shN] allows write-permission, the share [shxx] allows read-permission,
    and the [pN] value is be either a real pointer or a NULL, ditto the [pdN];
  - PARAMS:  assume the values of the function parameters are pN, pdN, and pxx respectively,
  - SEP: assume there are three memory resources; 
    - the first is either a dense matrix 1 x nsh (if pN!=NULL), or empty (if pN=NULL)
    - the second is either a dense matrix nsh x d (if pdN!=NULL), or empty (if pdN=NULL)
    -  the third is a dense matrix d x 1, containing the floating-point value [x] (which is a matrix value)
  POSTCONDITION: if the function returns, then,
  - PROP: No new mathematical facts hold that didn't before
  - RETURN: The return value is the signed integer representation of [nsh]
  - SEP: 
    - the contents of the [pN] matrix (if [pN!=NULL]) is θ(x)
    - the contents of the [pdN] matrix (if [pdN!=NULL]) is dθ(x)
    - the contents of the [pxx] matrix is still [x]
*)

(** Now we instantiate these  for each of the shapes *)

Definition shapes1dP1_spec := DECLARE _shapes1dP1 (shape_spec _ _ shapes1dP1F).
Definition shapes1dP2_spec := DECLARE _shapes1dP2 (shape_spec _ _ shapes1dP2F).
Definition shapes1dP3_spec := DECLARE _shapes1dP3 (shape_spec _ _ shapes1dP3F).
Definition shapes2dP1_spec := DECLARE _shapes2dP1 (shape_spec _ _ shapes2dP1F).
Definition shapes2dP2_spec := DECLARE _shapes2dP2 (shape_spec _ _ shapes2dP2F).
Definition shapes2dS2_spec := DECLARE _shapes2dS2 (shape_spec _ _ shapes2dS2F).
Definition shapes2dT1_spec := DECLARE _shapes2dT1 (shape_spec _ _ shapes2dT1F).

(** Finally we build an Abstract Specification Interface (ASI) containing all the instantiated specs *)
Definition shapes_ASI: funspecs :=
 [ shapes1dP1_spec; shapes1dP2_spec; shapes1dP3_spec; 
   shapes2dP1_spec; shapes2dP2_spec; shapes2dS2_spec;
   shapes2dT1_spec].





