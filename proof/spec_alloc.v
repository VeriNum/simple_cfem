Require Import VST.floyd.proofauto.
From CFEM Require Import alloc.
(* From vcfloat Require Import vcfloat.FPStdCompCert vcfloat.FPStdLib. *)
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[export] Declare Instance Malloc: MallocAPD.

Definition exit_spec :=
  DECLARE _exit
  WITH n: int
  PRE [ tint ]
    PROP() PARAMS (Vint n) SEP()
  POST [ tvoid ]
    PROP (False) RETURN () SEP().

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:Ctypes.type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition double_calloc_spec :=
  DECLARE _double_calloc
   WITH n: Z, gv: globals
   PRE [ tint ]
     PROP (0 <= n <= Int.max_signed)
     PARAMS (Vint (Int.repr n)) GLOBALS (gv)
     SEP (mem_mgr gv)
   POST [ tptr tdouble ] EX p:_,
     PROP() RETURN (p) 
     SEP (data_at Ews (tarray tdouble n) (Zrepeat (Vfloat Float.zero) n) p;
          malloc_token Ews (tarray tdouble n) p;
          mem_mgr gv).


Definition int_calloc_spec :=
  DECLARE _int_calloc
   WITH n: Z, gv: globals
   PRE [ tint ]
     PROP (0 <= n <= Int.max_signed)
     PARAMS (Vint (Int.repr n)) GLOBALS (gv)
     SEP (mem_mgr gv)
   POST [ tptr tint ] EX p:_,
     PROP() RETURN (p) 
     SEP (data_at Ews (tarray tint n) (Zrepeat (Vint Int.zero) n) p;
          malloc_token Ews (tarray tint n) p;
          mem_mgr gv).

Definition double_clear_spec :=
  DECLARE _double_clear
   WITH p: val, n: Z, sh: share
   PRE [ tptr tdouble , tint ]
     PROP ( 0 <= n <= Int.max_signed; writable_share sh )
     PARAMS (p ; Vint (Int.repr n))
     SEP (data_at_ sh (tarray tdouble n) p)
   POST [ tvoid ]
     PROP() RETURN()
     SEP (data_at sh (tarray tdouble n) (Zrepeat (Vfloat Float.zero) n) p).


Definition allocASI : funspecs := [ 
   exit_spec; surely_malloc_spec; double_calloc_spec; int_calloc_spec; double_clear_spec ].
