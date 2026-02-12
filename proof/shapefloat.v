(** * CFEM.shapefloat:  floating-point shape functions*)

From mathcomp Require Import all_boot finfun all_algebra all_analysis all_reals.
Require Import CFEM.matrix_util.
From vcfloat Require Import FPCompCert FPStdLib.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

From mathcomp.algebra_tactics Require Import ring lra.
Import GRing.

Definition BOPP {NANS: Nans} [ty] :  ftype ty -> ftype ty := 
   Binary.Bopp (fprec ty) (femax ty) (FPCore.opp_nan (fprec ty) (femax ty) (fprec_gt_one ty)).

From HB Require Import structures.
HB.instance Definition xx := hasAdd.Build _ (@BPLUS _ Tdouble).
HB.instance Definition yy := hasZero.Build _ (0%F64 : ftype Tdouble).

Module FShape.

Record shape {t: type} : Type := {
  d : nat;
  nsh: nat;
  θ: 'rV[ftype t]_d -> 'rV[ftype t]_nsh;  
  dθ: 'rV[ftype t]_d -> 'M[ftype t]_(nsh,d)
}.

End FShape.  

Definition shapes1dP1_float (xm: 'rV[ftype Tdouble]_1) : 'rV[ftype Tdouble]_2 :=
   let x : ftype Tdouble := xm 0 0 in
   rowmx_of_list [:: 0.5 * (1-x); 0.5 * (1+x)]%F64.

Definition shapes1dP1_fderiv (xm: 'rV[ftype Tdouble]_1) : 'M[ftype Tdouble]_(2,1) :=
   let x : ftype Tdouble := xm 0 0 in
   mx_of_list ([:: [:: -0.5];
                        [:: 0.5]]%F64 : list (list (ftype Tdouble))).


Definition shapes1dP1F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 1 2 shapes1dP1_float shapes1dP1_fderiv.

Definition shapes2dT1_float (xy: 'rV[ftype Tdouble]_2) : 'rV[ftype Tdouble]_3 :=
   let x : ftype Tdouble := xy 0 0 in
   let y : ftype Tdouble := xy 0 1 in
   rowmx_of_list [:: 1-x-y; x; y]%F64.

Definition shapes2dT1_fderiv (xy: 'rV[ftype Tdouble]_2) : 'M[ftype Tdouble]_(3,2) :=
   let x : ftype Tdouble := xy 0 0 in
   let y : ftype Tdouble := xy 0 1 in
   mx_of_list ([:: [:: -1; -1];
                        [:: 1; 0];
                        [:: 0; 1]]%F64 : list (list (ftype Tdouble))).


Definition shapes2dT1F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 2 3 shapes2dT1_float shapes2dT1_fderiv.

