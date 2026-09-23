(** * CFEM.C.spec_quadrules:  VST function specification for quadrules *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import Coq.Classes.RelationClasses.
From CFEM Require Import C.nonexpansive quadrature quadrature2 quadmodel.  
Import Legendre Quadmodel_F64.
Import fintype.  (* so we can use the 'I_5 notation *)

Set Bullet Behavior "Strict Subproofs".

From CFEM.C Require Import quadrules.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

(* end details *)

(** The C program has a local static array containing all these values in this order: *)

(** This separation logic predicate describes an array containing those gauss_points values,
   located at the C program's extern variable named gauss_pts. *)
Definition gauss_pts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_pts_list)) 
          (map Vfloat gauss_pts_list)
         (gv _gauss_pts).

(** This separation logic predicate describes an array containing those gauss_weights values,
   located at the C program's extern variable named gauss_wts. *)

Definition gauss_wts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_wts_list)) 
          (map Vfloat gauss_wts_list)
         (gv _gauss_wts).

(** ** Low-level specs *)
(** The C program's gauss_point function just returns an element from the array.
  This low-level spec says just that.  Below, the high-level spec will say that
   the floating-point value is actually appropriate. *)
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

(** The C program's gauss_weight function just returns an element from the array.
  This low-level spec says just that.  Below, the high-level spec will say that
   the floating-point value is actually appropriate. *)
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

(** This function computes integer square roots by case analysis. *) 
Definition gauss2d_npoint1d_spec : ident * funspec :=
  DECLARE _gauss2d_npoint1d
  WITH s: Z
  PRE [ tint ]
    PROP(1 <= s <= 5)
    PARAMS( Vint (Int.repr (s*s)))
    SEP( )
  POST[ tint ]
    PROP( )
    RETURN (Vint (Int.repr s))
    SEP( ).


Definition floatfun_spec (f: ftype Tdouble -> ftype Tdouble) : funspec :=
 WITH x: ftype Tdouble
 PRE [ tdouble ]
   PROP ()
   PARAMS (Vfloat x)
   SEP()
 POST [ tdouble ]
   PROP ()
   RETURN (Vfloat (f x))
   SEP ().

Definition integrate_spec_lowlevel : ident * funspec :=
 DECLARE _integrate
 WITH f: ftype Tdouble -> ftype Tdouble, p: val, n : 'I_5, gv: globals
 PRE [ tptr (Tfunction [tdouble] tdouble cc_default), tint ]
    PROP ()
    PARAMS ( p; Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p)
 POST [ tdouble ]
    PROP()
    RETURN (Vfloat (integrate_model_f Tdouble _ n (gauss_point_f n) (gauss_weight_f _) f))
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p).


Require VSTlib.spec_math.
Require vcfloat.VCFloat.
Definition cos := ltac:(Reify.apply_func (FPCore.Build_floatfunc_package _ _ _ _ spec_math.MF.cos)).

Definition testfun_f (x: ftype Tdouble) := 
   (0.5 * (1-x) * cos x)%F64.

Definition testfun_spec : ident * funspec :=
 DECLARE _testfun
  floatfun_spec testfun_f.

Definition integrate_testfun_spec_lowlevel : ident * funspec :=
 DECLARE _integrate_testfun
 WITH gv: globals
 PRE [ ]
    PROP() PARAMS() GLOBALS (gv)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv)
 POST [ tdouble ]
    PROP()
    RETURN (Vfloat (integrate_model_f Tdouble _ (@Ordinal 5 2 ssrbool.isT) 
                                     (gauss_point_f _) (gauss_weight_f _) 
                                     testfun_f))
    SEP( gauss_pts_pred gv; gauss_wts_pred gv).

(** ** High-level specs *)

(** The high-level specifications of gauss_points() and gauss_weights()
  are based on the theory of Gauss-Legendre quadrature, and then
  we need to prove that certain floating point numbers are accurate
  approximations of the real-valued Gauss points and weights, so 
  we import all the appropriate stuff now. *)

From mathcomp Require Import Rstruct.
(*From Stdlib Require*) Import Reals.

Instance InhR : Inhabitant R := 0%R.

(** *** 2-dimensional gauss points and weights *)
(**  We will take care of these at the "high" level. *) 

(** *** The triangle: Hughes quadrature points and weights, low-level specs only*)
Definition hughes_points: list (R*R) := [ (1/2, 0); (1/2, 1/2); (0, 1/2) ]%R.

Definition hughes_point_spec: ident * funspec :=
  DECLARE _hughes_point
  WITH sh: share, p: val, i: 'I_3
  PRE [ tptr tdouble, tint, tint ]
    PROP(writable_share sh)
    PARAMS(p; Vint (Int.repr (Z.of_nat i)); Vint (Int.repr 3))
    SEP(data_at_ sh (tarray tdouble 2) p )
  POST[ tvoid ]
    EX x: ftype Tdouble, EX y: ftype Tdouble,
    PROP(Znth (Z.of_nat i) hughes_points = (FT2R x, FT2R y))
    RETURN ()
    SEP(data_at sh (tarray tdouble 2) [Vfloat x; Vfloat y] p).

Definition hughes_weight: R := 1/6.

 Definition hughes_weight_spec : ident * funspec :=
  DECLARE _hughes_weight
  WITH i: 'I_3
  PRE [ tint, tint ]
    PROP()
    PARAMS(Vint (Int.repr (Z.of_nat i)); Vint (Int.repr 3))
    SEP()
  POST[ tdouble ]
    EX w: ftype Tdouble,
    PROP(float_near Tdouble hughes_weight w)
    RETURN ( Vfloat w )
    SEP().

Lemma init_data_tarray_tdouble {cs:compspecs} gv sh b: 
   forall xs i (Hi: Z.divide (align_chunk Mfloat64) (Ptrofs.unsigned i)) (Hxs: (Ptrofs.unsigned i + 8 * Zlength xs < Ptrofs.modulus)%Z),
  init_data_list2pred gv (map Init_float64 xs) sh (Vptr b i) |--
  data_at sh (tarray tdouble (Zlength xs)) (map Vfloat xs) (Vptr b i).
Proof. induction xs; intros; simpl.
  - rewrite data_at_zero_array_eq; auto; reflexivity.
  - replace (8 * Zlength (a :: xs))%Z with (8  + (8 * Zlength xs))%Z in Hxs by list_solve.
    specialize (Zlength_nonneg xs); intros L.
    unfold Ptrofs.add. rewrite ! Ptrofs.unsigned_repr; try rep_lia.

    rewrite (split2_data_at_Tarray sh tdouble (Zlength (a :: xs)) 1
            (Vfloat a :: map Vfloat xs) (Vfloat a :: map Vfloat xs)
            (sublist 0 1 (Vfloat a :: map Vfloat xs))
            (sublist 1 (Zlength (a :: xs)) (Vfloat a :: map Vfloat xs)) (Vptr b i)); try list_solve.

   apply sepcon_derives.
   + rewrite (data_at_singleton_array_eq sh tdouble (Vfloat a)) by trivial.
     erewrite mapsto_data_at'; auto; trivial.
     red; simpl; intuition auto with *.
     econstructor. apply predicates_hered.derives_refl. 
     split3; [ | | split3] ; simpl; auto. lia. eapply align_compatible_rec_by_value; try reflexivity; auto.
   + eapply derives_trans. apply IHxs; clear IHxs.
     * rewrite ! Ptrofs.unsigned_repr; try rep_lia.
        apply Z.divide_add_r; auto.
       simpl. first [exists 1%Z; lia | exists 2%Z; lia].
     * rewrite ! Ptrofs.unsigned_repr; rep_lia.
     * rewrite Zlength_cons.
       replace (Z.succ (Zlength xs) - 1)%Z with (Zlength xs) by lia.
       apply derives_refl'. f_equal. list_solve.
       unfold field_address0.  rewrite Coqlib2.if_true; simpl; trivial.
       red; intuition auto with *.
       -- reflexivity.
       -- red. rewrite sizeof_Tarray, Z.max_r. simpl sizeof; rep_lia. list_solve.
       -- eapply align_compatible_rec_Tarray; intros.
          econstructor. reflexivity.
          apply Z.divide_add_r; auto. simpl.
         first [exists i0; lia | exists (2*i0)%Z; lia].
Qed.

Lemma gauss_pts_match: forall gv,
   (exists rho, gv = globals_of_env rho) ->
   init_data_list2pred gv (gvar_init v_gauss_pts) Ers (gv _gauss_pts)
  |-- gauss_pts_pred gv.
Proof.
intros gv [rho Hrho].
unfold gauss_pts_pred.
assert_PROP(exists b, gv _gauss_pts = Vptr b (Ptrofs.repr 0)). {
rewrite Hrho.
simpl gvar_init.
unfold init_data_list2pred. 
match goal with |- ?A * ?B |-- ?C => forget B as foo end.
simpl.
unfold mapsto, globals_of_env; simpl.
destruct (Map.get _ _); simpl; [ | rewrite FF_sepcon; apply FF_left].
rewrite Coqlib2.if_true by auto.
entailer!!.
exists b; reflexivity.
}
destruct H as [b H].
assert (H0: gvar_init v_gauss_pts = map Init_float64 gauss_pts_list).
 simpl; repeat f_equal; with_strategy transparent [Float.of_bits] compute; f_equal; apply proof_irr.
rewrite H0.
rewrite H.
apply init_data_tarray_tdouble; auto.
apply Z.divide_0_r.
simpl. rep_lia.
Qed.

Lemma gauss_wts_match: forall gv,
   (exists rho, gv = globals_of_env rho) ->
   init_data_list2pred gv (gvar_init v_gauss_wts) Ers (gv _gauss_wts)
  |-- gauss_wts_pred gv.
Proof.
intros gv [rho Hrho].
unfold gauss_wts_pred.
assert_PROP(exists b, gv _gauss_wts = Vptr b (Ptrofs.repr 0)). {
rewrite Hrho.
simpl gvar_init.
unfold init_data_list2pred. 
match goal with |- ?A * ?B |-- ?C => forget B as foo end.
simpl.
unfold mapsto, globals_of_env; simpl.
destruct (Map.get _ _); simpl; [ | rewrite FF_sepcon; apply FF_left].
rewrite Coqlib2.if_true by auto.
entailer!!.
exists b; reflexivity.
}
destruct H as [b H].
assert (H0: gvar_init v_gauss_wts = map Init_float64 gauss_wts_list).
 simpl; repeat f_equal; with_strategy transparent [Float.of_bits] compute; f_equal; apply proof_irr.
rewrite H0.
rewrite H.
apply init_data_tarray_tdouble; auto.
apply Z.divide_0_r.
simpl. rep_lia.
Qed.

(*
Definition realfun_spec (f: R -> R) (acc: R) : funspec :=
 WITH x: ftype Tdouble
 PRE [ tdouble ]
   PROP ((-1 <= FT2R x <= 1)%R)
   PARAMS (Vfloat x)
   SEP()
 POST [ tdouble ]
   EX y: ftype Tdouble,
   PROP ((Rabs (FT2R y - f (FT2R x)) <= acc)%R)
   RETURN (Vfloat y)
   SEP ().

Definition δ := @common.default_rel Tdouble.

Definition testfun_spec : ident * funspec := 
 DECLARE _testfun
  (realfun_spec (fun x => (1/2)*(1-x)*(cos x))%R (5*δ)).
*)





