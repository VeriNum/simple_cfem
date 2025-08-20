Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From CFEM Require Import densemat spec_alloc floatlib cholesky_model.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition densemat_t := Tstruct _densemat_t noattr.

Definition the_ctype := ltac:(
    let d := constr:(nested_field_type densemat_t (DOT _data SUB 0))
     in let d := eval compute in d 
     in first [ unify d tdouble; exact tdouble
              | unify d tsingle; exact tsingle
              ]).

Definition the_type := 
  ltac:(first [ unify the_ctype tdouble; exact Tdouble
              | unify the_ctype tsingle; exact Tsingle
              ]).

Definition densemat_data_offset := 
  ltac:(let x := constr:(nested_field_offset densemat_t (DOT _data))
        in let y := eval compute in x in exact y).

Local Lemma check_densemat_layout:
  forall sh m n (x: list val) p, 
    data_at sh (Tstruct _densemat_t noattr) (Vint m,(Vint n,x)) p 
  |-- field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint m) p *
    field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint n) p.
(* This lemma could fail if there's padding between the fields. *)
Proof.
intros.
unfold_data_at (data_at _ _ _ _).
cancel.
entailer!.
rewrite value_fits_eq in H0. simpl in H0. destruct H0 as [? _].
change (unfold_reptype _) with x in H0.
destruct x; [ | list_solve].
unfold field_at. simpl.
entailer!!.
unfold data_at_rec. simpl.
unfold at_offset.
change (unfold_reptype _) with (@nil val).
rewrite array_pred_len_0; auto.
Qed.

Definition mklist {T} (n: Z) (f: Z -> T) : list T :=
 map f (Zrangelist 0 n).

Definition column_major {T} (rows cols: Z) (f: Z -> Z -> T) :=
 concat (mklist cols (fun j => mklist rows (fun i => f i j))).

Definition val_of_float {t} (f: ftype t) : val :=
match type_eq_dec t Tdouble with
     | left e =>
          eq_rect_r (fun t0 : type => ftype t0 -> val)
            (fun f1 : ftype Tdouble => Vfloat f1) e f
     | right _ =>
          match type_eq_dec t Tsingle with
          | left e =>
               eq_rect_r (fun t0 : type => ftype t0 -> val)
                 (fun f1 : ftype Tsingle => Vsingle f1) e f
          | right _ => Vundef
          end
     end.

Definition val_of_optfloat {t} (x: option (ftype t)) : val :=
match x with
| Some f => val_of_float f
| None => Vundef
end.

Definition ctype_of_type (t: type) : Ctypes.type :=
 if type_eq_dec t Tdouble then tdouble
 else if type_eq_dec t Tsingle then tfloat
 else tvoid.


Definition reptype_ftype {t: type} (n: Z) (vl: list val) : reptype (tarray (ctype_of_type t) n).
unfold ctype_of_type.
repeat if_tac.
apply vl.
apply vl.
apply (Zrepeat tt n).
Defined.

Definition densematn {t: type} (sh: share) (m n: Z) (data: Z -> Z -> option (ftype t)) (p: val) : mpred :=
 !! (0 <= m <= Int.max_signed /\ 0 <= n <= Int.max_signed /\ m*n <= Int.max_signed)
  && data_at sh (tarray (ctype_of_type t) (m*n))
      (reptype_ftype (m*n) (map (@val_of_optfloat t) (column_major m n data)))
      p.


Definition densemat (sh: share) (m n: Z) (data: Z -> Z -> option (ftype the_type)) (p: val) : mpred :=
     field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint (Int.repr m)) p
   * field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint (Int.repr n)) p
   * densematn sh m n data (offset_val densemat_data_offset p)
   * malloc_token' sh (densemat_data_offset + sizeof (tarray the_ctype (m*n))) p.

Definition densematn_local_facts: forall {t} sh m n data p,
  @densematn t sh m n data p |-- 
      !! (0 <= m <= Int.max_signed /\ 0 <= n <= Int.max_signed
          /\ m*n <= Int.max_signed
          /\ field_compatible (tarray (ctype_of_type t) (m*n)) [] p).
Proof.
intros.
unfold densematn.
entailer!.
Qed.

Definition densemat_local_facts: forall sh m n data p,
  densemat sh m n data p |-- 
      !! (0 <= m <= Int.max_signed /\ 0 <= n <= Int.max_signed
          /\ m*n <= Int.max_signed /\ 
           malloc_compatible (densemat_data_offset + sizeof (tarray the_ctype (m * n))) p).
Proof.
intros.
unfold densemat, densematn.
entailer!.
Qed.

#[export] Hint Resolve densematn_local_facts 
densemat_local_facts : saturate_local.

Lemma densematn_valid_pointer:
  forall t sh m n data p,
   m*n > 0 ->
   sepalg.nonidentity sh ->
   @densematn t sh m n data p |-- valid_pointer p.
Proof.
 intros.
 unfold densematn.
 Intros.
 apply data_at_valid_ptr; auto.
 unfold ctype_of_type.
 repeat if_tac; simpl; lia.
Qed.

Lemma densemat_valid_pointer:
  forall sh m n data p,
   densemat sh m n data p |-- valid_pointer p.
Proof.
 intros.
 unfold densemat. entailer!.
Qed.

#[export] Hint Resolve densematn_valid_pointer densemat_valid_pointer : valid_pointer.


Definition densemat_malloc_spec :=
  DECLARE _densemat_malloc
  WITH m: Z, n: Z, gv: globals
  PRE [ tint, tint ]
    PROP(0 <= m <= Int.max_signed; 0 <= n <= Int.max_signed; m*n <= Int.max_signed)
    PARAMS (Vint (Int.repr m); Vint (Int.repr n) ) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr densemat_t ]
   EX p: val,
    PROP () 
    RETURN (p) 
    SEP(densemat Ews m n (fun _ _ => None) p; mem_mgr gv).


Definition densemat_free_spec :=
  DECLARE _densemat_free
  WITH m: Z, n: Z, v: Z -> Z -> option float, p: val, gv: globals
  PRE [ tptr densemat_t ]
    PROP() 
    PARAMS ( p ) GLOBALS (gv)
    SEP(densemat Ews m n v p; mem_mgr gv)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP( mem_mgr gv ).

Definition densematn_clear_spec :=
  DECLARE _densematn_clear
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share
  PRE [ tptr the_ctype, tint, tint ]
    PROP(writable_share sh) 
    PARAMS (p; Vint (Int.repr m); Vint (Int.repr n) )
    SEP(densematn sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densematn sh m n (fun _ _ => Some (Zconst the_type 0)) p).

Definition densemat_clear_spec :=
  DECLARE _densemat_clear
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share
  PRE [ tptr densemat_t ]
    PROP(writable_share sh) 
    PARAMS (p)
    SEP(densemat sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densemat sh m n (fun _ _ => Some (Zconst the_type 0)) p).

Definition densematn_get_spec :=
  DECLARE _densematn_get
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, x: ftype the_type
  PRE [ tptr the_ctype , tint, tint, tint ]
    PROP(readable_share sh; 0 <= i < m; 0 <= j < n; v i j = Some x ) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j))
    SEP(densematn sh m n v p)
  POST [ tdouble ]
    PROP () 
    RETURN (val_of_float x) 
    SEP(densematn sh m n v p).

Definition densemat_get_spec :=
  DECLARE _densemat_get
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, x: ftype the_type
  PRE [ tptr densemat_t , tint, tint ]
    PROP(readable_share sh; 0 <= i < m; 0 <= j < n; v i j = Some x ) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j))
    SEP(densemat sh m n v p)
  POST [ tdouble ]
    PROP () 
    RETURN (val_of_float x) 
    SEP(densemat sh m n v p).

Definition densemat_upd {T: type} (v: Z -> Z -> option (ftype T)) (i j: Z) (x: ftype T) : 
   Z -> Z -> option (ftype T) :=
 fun i' j' => if zeq i' i then if zeq j' j then Some x else v i' j' else v i' j'.

Definition densematn_set_spec :=
  DECLARE _densematn_set
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint, the_ctype ]
    PROP(writable_share sh; 0 <= i < m; 0 <= j < n ) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densematn sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densematn sh m n (densemat_upd v i j x) p).

Definition densemat_set_spec :=
  DECLARE _densemat_set
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, x: ftype the_type
  PRE [ tptr densemat_t, tint, tint, tdouble ]
    PROP(writable_share sh; 0 <= i < m; 0 <= j < n ) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densemat sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densemat sh m n (densemat_upd v i j x) p).

Definition densematn_addto_spec :=
  DECLARE _densematn_addto
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, y: ftype the_type, x: ftype the_type
  PRE [ tptr tdouble, tint, tint, tint, tdouble ]
    PROP(writable_share sh; 0 <= i < m; 0 <= j < n; v i j = Some y ) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densematn sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densematn sh m n (densemat_upd v i j (BPLUS y x)) p).

Definition densemat_addto_spec :=
  DECLARE _densemat_addto
  WITH m: Z, n: Z, v: Z -> Z -> option (ftype the_type), p: val, sh: share,
       i: Z, j: Z, y: ftype Tdouble, x: ftype the_type
  PRE [ tptr densemat_t, tint, tint, the_ctype ]
    PROP(writable_share sh; 0 <= i < m; 0 <= j < n; v i j = Some y ) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densemat sh m n v p)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP(densemat sh m n (densemat_upd v i j (BPLUS y x)) p).

Definition data_norm2_spec :=
  DECLARE _data_norm2
  WITH sh: share, v: list (ftype the_type), p: val
  PRE [ tptr the_ctype, tint ]
    PROP (readable_share sh; Zlength v <= Int.max_signed)
    PARAMS (p; Vint (Int.repr (Zlength v)))
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p)
  POST [ the_ctype ]
    PROP() RETURN (val_of_float (norm2 v)) 
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p).

Definition data_norm_spec :=
  DECLARE _data_norm
  WITH sh: share, v: list (ftype the_type), p: val
  PRE [ tptr the_ctype, tint ]
    PROP (readable_share sh; Zlength v <= Int.max_signed)
    PARAMS (p; Vint (Int.repr (Zlength v)))
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p)
  POST [ tdouble ]
    PROP() RETURN (Vfloat (FPStdLib.BSQRT(norm2 v))) 
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p).

Definition frobenius_norm2 {t: type} (m n: Z) (v: Z -> Z -> ftype t) :=
  norm2 (column_major m n v).

Definition frobenius_norm {t: type} (m n: Z) (v: Z -> Z -> ftype t) :=
  BSQRT (norm2 (column_major m n v)).


Definition densemat_norm2_spec :=
  DECLARE _densemat_norm2
  WITH sh: share, m: Z, n: Z, v: Z -> Z -> ftype the_type, p: val
  PRE [ tptr densemat_t ]
    PROP (readable_share sh)
    PARAMS (p)
    SEP(densemat sh m n (fun i j => Some (v i j)) p)
  POST [ the_ctype ]
    PROP() RETURN (val_of_float (frobenius_norm2 m n v)) 
    SEP(densemat sh m n (fun i j => Some (v i j)) p).

Definition densemat_norm_spec :=
  DECLARE _densemat_norm
  WITH sh: share, m: Z, n: Z, v: Z -> Z -> ftype the_type, p: val
  PRE [ tptr densemat_t ]
    PROP (readable_share sh)
    PARAMS (p)
    SEP(densemat sh m n (fun i j => Some (v i j)) p)
  POST [ the_ctype ]
    PROP() RETURN (val_of_float (frobenius_norm m n v)) 
    SEP(densemat sh m n (fun i j => Some (v i j)) p).

(* joinLU n L U    produces a matrix whose upper-triangle (including diagonal) matches U,
         and whose lower_triangle (excluding diagonal) matches L *)
Definition joinLU {T} n (L: Z -> Z -> T) (U: Z -> Z -> T) : Z -> Z -> T :=
 fun i j => if ((0 <=? i) && (i <=? j) && (j <? n))%bool then U i j else L i j.

Definition densematn_cfactor_spec :=
 DECLARE _densematn_cfactor
 WITH sh: share, n: Z, 
      M: (Z -> Z -> option (ftype the_type)), 
      A: (Z -> Z -> ftype the_type), p: val
 PRE [ tptr the_ctype, tint ]
    PROP (writable_share sh)
    PARAMS (p; Vint (Int.repr n))
    SEP (densematn sh n n (joinLU n M (fun i j => Some (A i j))) p)
 POST [ tvoid ]
   EX R: Z -> Z -> ftype the_type,
    PROP (cholesky_jik_spec n A R)
    RETURN ()
    SEP (densematn sh n n (joinLU n M (fun i j => Some (R i j))) p).

Definition densemat_cfactor_spec :=
 DECLARE _densemat_cfactor
 WITH sh: share, n: Z, 
      M: (Z -> Z -> option (ftype the_type)), 
      A: (Z -> Z -> ftype the_type), p: val
 PRE [ tptr densemat_t ]
    PROP (writable_share sh)
    PARAMS (p)
    SEP (densemat sh n n (joinLU n M (fun i j => Some (A i j))) p)
 POST [ tvoid ]
   EX R: Z -> Z -> ftype Tdouble,
    PROP (cholesky_jik_spec n A R)
    RETURN ()
    SEP (densemat sh n n (joinLU n M (fun i j => Some (R i j))) p).

Definition densematn_csolve_spec :=
 DECLARE _densematn_csolve
 WITH rsh: share, sh: share, n: Z, 
      M: (Z -> Z -> option (ftype the_type)), 
      R: (Z -> Z -> ftype the_type),
      x: list (ftype the_type), p: val, xp: val
 PRE [ tptr the_ctype, tptr the_ctype, tint ]
    PROP (readable_share rsh; writable_share sh)
    PARAMS (p; xp; Vint (Int.repr n))
    SEP (densematn rsh n n (joinLU n M (fun i j => Some (R i j))) p;
         data_at sh (tarray the_ctype n) (map val_of_float x) xp)
 POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (densematn rsh n n (joinLU n M (fun i j => Some (R i j))) p;
         data_at sh (tarray the_ctype n) 
          (map val_of_float (backward_subst n R (forward_subst n (transpose R) x)))
           xp).

Definition densemat_csolve_spec :=
 DECLARE _densemat_csolve
 WITH rsh: share, sh: share, n: Z, 
      M: (Z -> Z -> option (ftype the_type)), 
      R: (Z -> Z -> ftype the_type),
      x: list (ftype the_type), p: val, xp: val
 PRE [ tptr densemat_t, tptr the_ctype ]
    PROP (readable_share rsh; writable_share sh)
    PARAMS (p; xp)
    SEP (densemat rsh n n (joinLU n M (fun i j => Some (R i j))) p;
         data_at sh (tarray the_ctype n) (map val_of_float x) xp)
 POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (densemat rsh n n (joinLU n M (fun i j => Some (R i j))) p;
         data_at sh (tarray the_ctype n) 
          (map val_of_float (backward_subst n R (forward_subst n (transpose R) x)))
           xp).


Definition densemat_lujac_spec : ident*funspec := 
 (_densemat_lujac, vacuous_funspec (Internal f_densemat_lujac)).
Definition densematn_lujac_spec : ident*funspec := 
 (_densematn_lujac, vacuous_funspec (Internal f_densematn_lujac)).
Definition densematn_print_spec : ident*funspec := 
 (_densematn_print, vacuous_funspec (Internal f_densematn_print)).
Definition densemat_print_spec : ident*funspec := 
 (_densemat_print, vacuous_funspec (Internal f_densemat_print)).
Definition densemat_lusolve_spec : ident*funspec := 
 (_densemat_lusolve, vacuous_funspec (Internal f_densemat_lusolve)).
Definition densematn_lusolve_spec : ident*funspec := 
 (_densematn_lusolve, vacuous_funspec (Internal f_densematn_lusolve)).
Definition densemat_lufactor_spec : ident*funspec := 
 (_densemat_lufactor, vacuous_funspec (Internal f_densemat_lufactor)).
Definition densematn_lufactor_spec : ident*funspec := 
 (_densematn_lufactor, vacuous_funspec (Internal f_densematn_lufactor)).
Definition densematn_lusolveT_spec : ident*funspec := 
 (_densematn_lusolveT, vacuous_funspec (Internal f_densematn_lusolveT)).
Definition densemat_lusolveT_spec : ident*funspec := 
 (_densemat_lusolveT, vacuous_funspec (Internal f_densemat_lusolveT)).



Definition densematASI : funspecs := [ 
   densemat_malloc_spec; densemat_free_spec; densematn_clear_spec; densemat_clear_spec;
   densemat_get_spec; densematn_get_spec;
   densemat_set_spec; densematn_set_spec;
   densemat_addto_spec; densematn_addto_spec;
   data_norm_spec; data_norm2_spec;
   densemat_norm_spec; densemat_norm2_spec;
   densemat_lujac_spec; densematn_lujac_spec;
   densemat_print_spec; densematn_print_spec;
   densemat_lusolve_spec; densematn_lusolve_spec;
   densemat_lufactor_spec; densematn_lufactor_spec;
   densemat_csolve_spec; densematn_csolve_spec;
   densemat_cfactor_spec; densematn_cfactor_spec;
   densemat_lusolveT_spec; densematn_lusolveT_spec
    ].


