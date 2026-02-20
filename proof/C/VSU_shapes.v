From CFEM Require Import C.verif_shapes_base C.verif_shapes1d C.verif_shapes2d verif_shapes2dP2.
Require Import VST.floyd.VSU.

Definition shapesVSU: @VSU NullExtension.Espec
         shapes_E shapes_imported_specs 
         ltac:(QPprog prog) shapes_ASI (fun _ => TT).
  Proof.
    mkVSU prog shapes_internal_specs.
    - solve_SF_internal body_shapes1dP1.
    - solve_SF_internal body_shapes1dP2.
    - solve_SF_internal body_shapes1dP3.
    - solve_SF_internal body_shapes2dP1.
    - solve_SF_internal body_shapes2dP2.
    - solve_SF_internal body_shapes2dS2.
    - solve_SF_internal body_shapes2dT1.
  Qed.
