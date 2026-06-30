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

(* end details *)


Definition gauss_pts_list : list (ftype Tdouble) :=
  [      (* One point *)
         0.0;

        (* Two points *)
        -0.5773502691896257;
        0.5773502691896257;

        (* Three points *)
        -0.7745966692414834;
        0.0;
        0.7745966692414834;

        (* Four points *)
        -0.8611363115940526;
        -0.33998104358485626;
        0.33998104358485626;
        0.8611363115940526;

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


Definition gauss_wts_list : list (ftype Tdouble) := [
        (* One point *)
        2.0;

        (* Two points *)
        1.0;
        1.0;

        (* Three points *)
        0.5555555555555556;
        0.8888888888888889;
        0.5555555555555556;

        (* Four points *)
        0.34785484513745384;
        0.65214515486254616;
        0.65214515486254616;
        0.34785484513745384;

        (* Five points *)
        0.236926885056189;
        0.478628670499366;
        0.568888888888889;
        0.478628670499366;
        0.236926885056189;

        (* Six points *)
        0.171324492379170;
        0.360761573048139;
        0.467913934572691;
        0.467913934572691;
        0.360761573048139;
        0.171324492379170;

        (* Seven points *)
        0.129484966168870;
        0.279705391489277;
        0.381830050505119;
        0.417959183673469;
        0.381830050505119;
        0.279705391489277;
        0.129484966168870;

        (* Eight points *)
        0.101228536290376;
        0.222381034453374;
        0.313706645877887;
        0.362683783378362;
        0.362683783378362;
        0.313706645877887;
        0.222381034453374;
        0.101228536290376;

        (* Nine points *)
        0.081274388361574;
        0.180648160694857;
        0.260610696402935;
        0.312347077040003;
        0.330239355001260;
        0.312347077040003;
        0.260610696402935;
        0.180648160694857;
        0.081274388361574;

        (* Ten points *)
        0.066671344308688;
        0.149451349150581;
        0.219086362515982;
        0.269266719309996;
        0.295524224714753;
        0.295524224714753;
        0.269266719309996;
        0.219086362515982;
        0.149451349150581;
        0.066671344308688
  ]%F64.


Definition gauss_wts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_wts_list)) 
          (map Vfloat gauss_wts_list)
         (gv _gauss_wts).

Definition gauss_point_spec_lowlevel : ident * funspec :=
  DECLARE _gauss_point
  WITH npts: Z, i: Z, gv: globals
  PRE [ tint, tint ]
    PROP((0 <= i < npts)%Z; (1 <= npts <= 10)%Z)
    PARAMS( Vint (Int.repr i); Vint (Int.repr npts))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv )
  POST[ tdouble]
    PROP( )
    RETURN (Vfloat (Znth (npts*(npts-1)/2+i) gauss_pts_list))
    SEP( gauss_pts_pred gv ).

Definition gauss_weight_spec_lowlevel : ident * funspec :=
  DECLARE _gauss_weight
  WITH npts: Z, i: Z, gv: globals
  PRE [ tint, tint ]
    PROP((0 <= i < npts)%Z; (1 <= npts <= 10)%Z)
    PARAMS( Vint (Int.repr i); Vint (Int.repr npts))
    GLOBALS (gv)
    SEP( gauss_wts_pred gv )
  POST[ tdouble]
    PROP( )
    RETURN (Vfloat (Znth (npts*(npts-1)/2+i) gauss_wts_list))
    SEP( gauss_wts_pred gv ).
 
Require Import CFEM.quadrature CFEM.polyroots. Import MethodB.

Instance Inh_poly_and_roots: Inhabitant (poly_and_roots Tdouble) :=
  Build_poly_and_roots 0 nil Legendre.gauss_weights_0.

Fixpoint is_nth {T: Type} (al: list T) (i: nat) (X: T) :=
 match al, i with
 | Y::al', O => Y=X
 | _::al', S j => is_nth al' j X
 | _, _  => False
 end.

Instance InhR: Inhabitant R := 0.

Definition gauss_point_spec : ident * funspec :=
  DECLARE _gauss_point
  WITH n: nat, i: nat, gv: globals
  PRE [ tint, tint ]
    PROP((i < n <= 4)%nat)
    PARAMS( Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv )
  POST[ tdouble]
    EX P : poly_and_roots Tdouble, EX X: root_near (legendre (PR_n P)) Tdouble,
    PROP(PR_n P =  n; is_nth (PR_roots P) i X)
    RETURN (Vfloat (fst (proj1_sig X)))
    SEP( gauss_pts_pred gv ).

Lemma sub_gauss_point: funspec_sub (snd gauss_point_spec_lowlevel) (snd gauss_point_spec).
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[n i] gv] [? ?]. Exists (Z.of_nat n, Z.of_nat i, gv) emp.
normalize.
unfold_for_go_lower; normalize. simpl; entailer!; intros.
Exists (nth n legendre_roots Inh_poly_and_roots).
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
unfold legendre_roots, nth, PR_n, PR_roots;
EExists;
(normalize; apply andp_right; [apply prop_right | apply derives_refl];
 split; [ reflexivity |];
 split; [split; [reflexivity | auto] | ];
 split3; [ assumption | congruence | auto]).
Qed.

Definition ord_ext [n n'] (H: n=n') :  'I_n -> 'I_n' :=
  eq_rect_r (fun n0 : nat => 'I_n0 -> 'I_n') (fun i0 : ordinal n' => i0) H.

Definition weight_near (r: R) (x: ftype Tdouble) :=
  (Rabs (FT2R x - r) <= Rabs (FT2R x) * FPCore.default_rel (coretype_of_type Tdouble))%R.

Definition gauss_weight_spec : ident * funspec :=
  DECLARE _gauss_weight
  WITH X: { n: nat & 'I_n}, gv: globals
  PRE [ tint, tint ] let '(existT _ n i) := X in 
    PROP((n <= 4)%nat)
    PARAMS( Vint (Int.repr (Z.of_nat (nat_of_ord i))); Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_wts_pred gv )
  POST[ tdouble] let '(existT _ n i) := X in 
    EX P : poly_and_roots Tdouble, EX H: n = PR_n P, EX x: ftype Tdouble,
    PROP(weight_near (tuple.tnth (Legendre.GW_vals _ (PR_weights P)) (ord_ext H i)) x)
    RETURN (Vfloat x)
    SEP( gauss_wts_pred gv ).

Require Import Interval.Tactic.

Lemma sub_gauss_weight: funspec_sub (snd gauss_weight_spec_lowlevel) (snd gauss_weight_spec).
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[n [i Hi]] gv] [? ?]. Exists (Z.of_nat n, Z.of_nat i, gv) emp.
normalize.
unfold_for_go_lower; normalize.
simpl; normalize.
entailer!; intros.
Exists (nth n legendre_roots Inh_poly_and_roots).
assert (Hn: n = PR_n (nth n legendre_roots Inh_poly_and_roots)).
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia; try reflexivity.
Exists Hn.
EExists.
normalize; apply andp_right; [apply prop_right | apply derives_refl].
split3; [ | | split3]; auto; try apply H3; try congruence.
red.
set (d := FPCore.default_rel _); hnf in d; simpl in d; subst d.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
rewrite <- nth_Znth by (rewrite Zlength_correct; simpl; lia);
simpl in Hn|-*;
rewrite (proof_irr Hn eq_refl); clear Hn;
simpl;
unfold tuple.tnth, ord_ext, eq_rect_r, eq_rect, eq_sym;
unfold tuple.tval, reverse_coercion, tuple.cons_tuple, tuple.nil_tuple, tuple.tval;
simpl;
unfold Defs.F2R, Defs.Fnum, Defs.Fexp;
try change nmodule.Algebra.zero with 0%R;
repeat change (ssralg.GRing.mul ?A ?B) with (A*B)%R;
repeat change (nmodule.Algebra.opp ?A) with (- A)%R;
repeat change (nmodule.Algebra.add ?A ?B) with (A + B)%R;
try change (ssralg.GRing.one _) with 1%R;
repeat change (ssralg.GRing.inv ?A) with (/A)%R;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE;
interval with (i_prec(110%positive)).
Qed.

(** Finally we build an Abstract Specification Interface (ASI) containing all the instantiated specs *)
Definition quadrules_ASI: funspecs :=
 [ gauss_point_spec; gauss_weight_spec ].





