(** * CFEM.C.spec_quadrature:  VST function specification for quadrules *)


(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From CFEM.C Require Import quadrules.
From vcfloat Require Import FPStdCompCert FPStdLib.
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

Require Import CFEM.quadrature CFEM.polyroots.
(* end details *)


Definition gauss_pts_list : list (ftype Tdouble) :=
  [      (* One point *)
         0.0;

        (* Two points *)
        -0.577350269189626;
        0.577350269189626;

        (* Three points *)
        -0.774596669241483;
        0.0;
        0.774596669241483;

        (* Four points *)
        -0.861136311594053;
        -0.339981043584856;
        0.339981043584856;
        0.861136311594053;

        (* Five points *)
        -0.906179845938664;
        -0.538469310105683;
        0.0;
        0.538469310105683;
        0.906179845938664;

        (* Six points *)
        -0.932469514203152;
        -0.661209386466265;
        -0.238619186083197;
        0.238619186083197;
        0.661209386466265;
        0.932469514203152;

        (* Seven points *)
        -0.949107912342759;
        -0.741531185599394;
        -0.405845151377397;
        0.0;
        0.405845151377397;
        0.741531185599394;
        0.949107912342759;

        (* Eight points *)
        -0.960289856497536;
        -0.796666477413627;
        -0.525532409916329;
        -0.183434642495650;
        0.183434642495650;
        0.525532409916329;
        0.796666477413627;
        0.960289856497536;

        (* Nine points *)
        -0.968160239507626;
        -0.836031107326636;
        -0.613371432700590;
        -0.324253423403809;
        0.0;
        0.324253423403809;
        0.613371432700590;
        0.836031107326636;
        0.968160239507626;

        (* Ten points *)
        -0.973906528517172;
        -0.865063366688985;
        -0.679409568299024;
        -0.433395394129247;
        -0.148874338981631;
        0.148874338981631;
        0.433395394129247;
        0.679409568299024;
        0.865063366688985;
        0.973906528517172
  ]%F64.

Definition gauss_pts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_pts_list)) 
          (map Vfloat gauss_pts_list)
         (gv _gauss_pts).
 
Instance Inh_poly_and_roots: Inhabitant (poly_and_roots Tdouble) :=
  Build_poly_and_roots (fun x:R => 1) nil eq_refl.

Fixpoint is_nth {T: Type} (al: list T) (i: nat) (X: T) :=
 match al, i with
 | Y::al', O => Y=X
 | _::al', S j => is_nth al' j X
 | _, _  => False
 end.

Instance InhR: Inhabitant R := 0.
Definition gauss_point_spec : ident * funspec :=
  DECLARE _gauss_point
  WITH npts: Z, i: Z, gv: globals
  PRE [ tint, tint ]
    PROP((0 <= i < npts)%Z; (1 <= npts <= 4)%Z)
    PARAMS( Vint (Int.repr i); Vint (Int.repr npts))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv )
  POST[ tdouble]
    EX P : poly_and_roots Tdouble, EX X: root_near (PR_poly P) Tdouble,
    PROP( PR_poly P = legendre (Z.to_nat npts);
                 is_nth (PR_roots P) (Z.to_nat i) X )
    RETURN (Vfloat (fst (proj1_sig X)))
    SEP( gauss_pts_pred gv ).


(** Finally we build an Abstract Specification Interface (ASI) containing all the instantiated specs *)
Definition quadrules_ASI: funspecs :=
 [ gauss_point_spec ].





