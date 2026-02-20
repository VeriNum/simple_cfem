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

Definition shapes1dP2_float (xm: 'rV[ftype Tdouble]_1) : 'rV[ftype Tdouble]_3 :=
   let x : ftype Tdouble := xm 0 0 in
   rowmx_of_list [:: -0.5*(1-x)*x; (1-x)*(1+x); 0.5*x*(1+x)]%F64.

Definition shapes1dP2_fderiv (xm: 'rV[ftype Tdouble]_1) : 'M[ftype Tdouble]_(3,1) :=
   let x : ftype Tdouble := xm 0 0 in
   mx_of_list ([:: [:: -0.5*(1-2*x)]; [:: -2*x]; [:: 0.5*(1+2*x)]]%F64 : list (list (ftype Tdouble))).

Definition shapes1dP2F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 1 3 shapes1dP2_float shapes1dP2_fderiv.


Definition shapes1dP3_float (xm: 'rV[ftype Tdouble]_1) : 'rV[ftype Tdouble]_4 :=
   let x : ftype Tdouble := xm 0 0 in
   rowmx_of_list [:: (-1.0/16)*(1-x)*(1-3*x)*(1+3*x);
                               (9.0/16)*(1-x)*(1-3*x)*(1+x);
                               (9.0/16)*(1-x)*(1+3*x)*(1+x);
                              (-1.0/16)*(1-3*x)*(1+3*x)*(1+x)]%F64.

Definition shapes1dP3_fderiv (xm: 'rV[ftype Tdouble]_1) : 'M[ftype Tdouble]_(4,1) :=
   let x : ftype Tdouble := xm 0 0 in
   mx_of_list ([:: [:: 1.0/16 * (1+x*(18+x*(-27)))]; 
                          [:: 9.0/16 * (-3+x*(-2+x* 9))]; 
                          [:: 9.0/16 * (3+x*(-2+x*(-9)))]; 
                          [:: 1.0/16 * (-1+x*(18+x* 27))]]%F64 : list (list (ftype Tdouble))).

Definition shapes1dP3F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 1 4 shapes1dP3_float shapes1dP3_fderiv.

Definition shapes2dP1_float (xm: 'rV[ftype Tdouble]_2) : 'rV[ftype Tdouble]_4 :=
   let Nx := shapes1dP1_float (col 0 xm) 0 in
   let Ny := shapes1dP1_float (col 1 xm) 0 in
   rowmx_of_list [:: Nx 0%R * Ny 0%R; Nx 1%R * Ny 0%R; 
                              Nx 1%R * Ny 1%R; Nx 0%R * Ny 1%R]%F64.

Definition shapes2dP1_fderiv (xm: 'rV[ftype Tdouble]_2) : 'M[ftype Tdouble]_(4,2) :=
   let Nx := shapes1dP1_float (col 0 xm) 0 in
   let Ny := shapes1dP1_float (col 1 xm) 0 in
   let dNx i := shapes1dP1_fderiv (col 0 xm) i 0 in
   let dNy i := shapes1dP1_fderiv (col 1 xm) i 0 in
    mx_of_list ([:: [:: dNx 0%R * Ny 0%R; Nx 0%R * dNy 0%R];
                           [:: dNx 1%R * Ny 0%R; Nx 1%R * dNy 0%R];
                           [:: dNx 1%R * Ny 1%R; Nx 1%R * dNy 1%R];
                           [:: dNx 0%R * Ny 1%R; Nx 0%R * dNy 1%R]]%F64 : list (list (ftype Tdouble))).
 
Definition shapes2dP1F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 2 4 shapes2dP1_float shapes2dP1_fderiv.

Definition shapes2dP2_float (xm: 'rV[ftype Tdouble]_2) : 'rV[ftype Tdouble]_9 :=
   let Nx := shapes1dP2_float (col 0 xm) 0 in
   let Ny := shapes1dP2_float (col 1 xm) 0 in
   rowmx_of_list [:: Nx 0%R * Ny 0%R; Nx 1%R * Ny 0%R;  Nx 2%R * Ny 0%R; 
                              Nx 2%R * Ny 1%R; Nx 2%R * Ny 2%R; Nx 1%R * Ny 2%R;
                              Nx 0%R * Ny 2%R; Nx 0%R * Ny 1%R; Nx 1%R * Ny 1%R]%F64.

Definition shapes2dP2_fderiv (xm: 'rV[ftype Tdouble]_2) : 'M[ftype Tdouble]_(9,2) :=
   let Nx := shapes1dP2_float (col 0 xm) 0 in
   let Ny := shapes1dP2_float (col 1 xm) 0 in
   let dNx i := shapes1dP2_fderiv (col 0 xm) i 0 in
   let dNy i := shapes1dP2_fderiv (col 1 xm) i 0 in
    mx_of_list ([:: [:: dNx 0%R * Ny 0%R; Nx 0%R * dNy 0%R];
                           [:: dNx 1%R * Ny 0%R; Nx 1%R * dNy 0%R];
                           [:: dNx 2%R * Ny 0%R; Nx 2%R * dNy 0%R];
                           [:: dNx 2%R * Ny 1%R; Nx 2%R * dNy 1%R];
                           [:: dNx 2%R * Ny 2%R; Nx 2%R * dNy 2%R];
                           [:: dNx 1%R * Ny 2%R; Nx 1%R * dNy 2%R];
                           [:: dNx 0%R * Ny 2%R; Nx 0%R * dNy 2%R];
                           [:: dNx 0%R * Ny 1%R; Nx 0%R * dNy 1%R];
                           [:: dNx 1%R * Ny 1%R; Nx 1%R * dNy 1%R]]%F64 : list (list (ftype Tdouble))).
 
Definition shapes2dP2F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 2 9 shapes2dP2_float shapes2dP2_fderiv.

Definition shapes2dS2_float (xm: 'rV[ftype Tdouble]_2) : 'rV[ftype Tdouble]_8 :=
   let Nx := shapes1dP2_float (col 0 xm) 0 in
   let Ny := shapes1dP2_float (col 1 xm) 0 in
   rowmx_of_list [:: Nx 0%R * Ny 0%R; Nx 1%R * Ny 0%R;  Nx 2%R * Ny 0%R; 
                              Nx 2%R * Ny 1%R; Nx 2%R * Ny 2%R; Nx 1%R * Ny 2%R;
                              Nx 0%R * Ny 2%R; Nx 0%R * Ny 1%R]%F64.

Definition shapes2dS2_fderiv (xm: 'rV[ftype Tdouble]_2) : 'M[ftype Tdouble]_(8,2) :=
   let Nx := shapes1dP2_float (col 0 xm) 0 in
   let Ny := shapes1dP2_float (col 1 xm) 0 in
   let dNx i := shapes1dP2_fderiv (col 0 xm) i 0 in
   let dNy i := shapes1dP2_fderiv (col 1 xm) i 0 in
    mx_of_list ([:: [:: dNx 0%R * Ny 0%R; Nx 0%R * dNy 0%R];
                           [:: dNx 1%R * Ny 0%R; Nx 1%R * dNy 0%R];
                           [:: dNx 2%R * Ny 0%R; Nx 2%R * dNy 0%R];
                           [:: dNx 2%R * Ny 1%R; Nx 2%R * dNy 1%R];
                           [:: dNx 2%R * Ny 2%R; Nx 2%R * dNy 2%R];
                           [:: dNx 1%R * Ny 2%R; Nx 1%R * dNy 2%R];
                           [:: dNx 0%R * Ny 2%R; Nx 0%R * dNy 2%R];
                           [:: dNx 0%R * Ny 1%R; Nx 0%R * dNy 1%R]]%F64 : list (list (ftype Tdouble))).
 
Definition shapes2dS2F : @FShape.shape Tdouble :=
      FShape.Build_shape Tdouble 2 8 shapes2dS2_float shapes2dS2_fderiv.


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

