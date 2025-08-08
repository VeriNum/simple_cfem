From VST.floyd Require Import proofauto VSU.
From CFEM Require Import densemat spec_alloc spec_densemat.
(* From vcfloat Require Import vcfloat.FPStdCompCert vcfloat.FPStdLib. *)
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition densemat_E : funspecs := [].
Definition densemat_imported_specs : funspecs := 
   [free_spec'; surely_malloc_spec'; double_clear_spec]. (* subset of MallocASI ++ allocASI *)
Definition densemat_internal_specs : funspecs := densematASI.
Definition Gprog :=  densemat_imported_specs ++ densemat_internal_specs.

Instance change_composite_env_alloc :
  change_composite_env spec_alloc.CompSpecs CompSpecs.
Proof.
   make_cs_preserve spec_alloc.CompSpecs CompSpecs.
Qed.

Instance change_composite_env_alloc' :
  change_composite_env CompSpecs spec_alloc.CompSpecs.
Proof.
   make_cs_preserve CompSpecs spec_alloc.CompSpecs.
Qed.

Lemma column_major_const:
 forall m n x, 
  0 <= m -> 0 <= n -> 
  map val_of_optfloat (column_major m n (fun _ _ => x)) =
  Zrepeat (val_of_optfloat x) (m*n).
Proof.
intros.
unfold column_major, Zrepeat.
rewrite Z2Nat.inj_mul by lia.
forget (Z.to_nat m) as a.
forget (Z.to_nat n) as b.
clear.
rewrite Nat.mul_comm.
symmetry.
transitivity (concat (repeat (repeat (val_of_optfloat x) a) b)).
 +
 induction b.
  * auto.
  * simpl. rewrite repeat_app. f_equal; auto.
 + unfold mklist.
   pose (i := O). change (seq 0 b) with (seq i b).
   clearbody i.
   revert i; induction b; simpl; intros; auto.
   rewrite map_app.
   f_equal; auto.
   clear.
   set (i := O). clearbody i.
   revert i; induction a; simpl; intros; auto.
   f_equal; auto.
Qed.

Lemma body_densemat_malloc: semax_body Vprog Gprog f_densemat_malloc densemat_malloc_spec.
Proof.
start_function.
forward_call (densemat_data_offset+m*n*sizeof(tdouble), gv);
unfold densemat_data_offset.
simpl; rep_lia.
Intros p.
assert_PROP (isptr p /\ malloc_compatible (8 + m * n * sizeof tdouble) p) by entailer!.
destruct H2.
destruct p; try contradiction. clear H2.
destruct H3.
rewrite <- (Ptrofs.repr_unsigned i).
rewrite memory_block_split by (simpl in *; rep_lia).
rewrite !Ptrofs.repr_unsigned.
change (memory_block Ews 8) 
  with (memory_block Ews (sizeof (Tstruct _densemat_t noattr))).
rewrite memory_block_data_at_.
2:{
split3; auto. simpl; auto.
split3. simpl. simpl in H3. rep_lia.
red.
eapply align_compatible_rec_Tstruct.
reflexivity. simpl. auto.
simpl co_members.
intros.
unfold Ctypes.field_type in H4.
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_by_value. reflexivity.
unfold natural_alignment in H2. simpl.
destruct H2. exists (2*x)%Z. lia.
clear H6. 
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_by_value. reflexivity.
unfold natural_alignment in H2. simpl.
destruct H2. exists (2*x+1)%Z. lia.
clear H6.
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_Tarray.
intros.
eapply align_compatible_rec_by_value. reflexivity.
simpl.
destruct H2. exists (2*x+2)%Z. lia.
inv H4.
compute; auto.
}
Intros.
forward.
forward.
forward.
Exists (Vptr b i).
unfold densemat.
simpl sizeof.
unfold densemat_data_offset.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (m*n)).
entailer!.
unfold_data_at (data_at _ _ _ _).
cancel.
rewrite field_at_data_at.
simpl.
sep_apply data_at_zero_array_inv.
rewrite emp_sepcon.
unfold Ptrofs.add.
rewrite Ptrofs.unsigned_repr by rep_lia.
replace (8 * (m*n))%Z with (sizeof (tarray tdouble (m*n)))%Z
 by (simpl; lia).
sep_apply memory_block_data_at_.
-
clear - H H0 H1 H5 H8 H9.
destruct H5 as [_ [_ [? [? _]]]].
split3; auto.
simpl. auto.
split3; [ | | hnf; auto].
red in H2,H9|-*.
simpl. rewrite Z.max_r by rep_lia.
rep_lia.
red.
red in H3.
destruct H8.
apply align_compatible_rec_Tarray.
intros.
eapply align_compatible_rec_by_value.
reflexivity.
simpl.
simpl in H9.
rewrite Ptrofs.unsigned_repr in H9|-* by rep_lia.
unfold natural_alignment in H4.
destruct H4.
rewrite H4.
repeat apply Z.divide_add_r.
apply Z.divide_mul_r.
exists 2; auto.
exists 2; auto.
apply Z.divide_mul_l.
exists 2; auto.
-
sep_apply data_at__data_at.
apply derives_refl'.
f_equal.
clear - H H0.
unfold default_val.
simpl.
symmetry.
change Vundef with (val_of_optfloat None).
apply column_major_const; lia.
Qed.


Lemma body_densemat_free: semax_body Vprog Gprog f_densemat_free densemat_free_spec.
Proof.
start_function.
unfold densemat.
Intros.
assert_PROP (isptr p
      /\ malloc_compatible (densemat_data_offset +
      sizeof (tarray tdouble (m * n))) p) by entailer!.
destruct H2 as [H2 COMPAT].
simpl in COMPAT. rewrite Z.max_r in COMPAT by lia.
red in COMPAT.
forward_call (densemat_data_offset+m*n*sizeof(tdouble), p, gv).
-
revert Frame.
instantiate (1:=nil). intro.
subst Frame.
rewrite if_false by (intro; subst; contradiction).
simpl.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (m*n)).
cancel.
destruct p; try contradiction; clear H2.
rewrite <- (Ptrofs.repr_unsigned i).
unfold densemat_data_offset in *.
saturate_local.
rewrite memory_block_split; try (simpl; rep_lia).
apply sepcon_derives.
change 8 with (4+4).
rewrite memory_block_split; try (simpl; rep_lia).
apply sepcon_derives;
rewrite field_at_data_at; simpl;
unfold field_address;
rewrite if_true by auto with field_compatible; simpl.
rewrite ptrofs_add_repr, Z.add_0_r.
apply data_at_memory_block.
rewrite ptrofs_add_repr.
apply data_at_memory_block.
simpl.
rewrite ptrofs_add_repr.
pose (x:= sizeof (tarray tdouble (m*n))).
simpl in x.
replace (8 * (m*n))%Z with (8 * (Z.max 0 (m*n)))%Z by rep_lia.
apply data_at_memory_block.
-
entailer!.
Qed.

Lemma body_densematn_clear: semax_body Vprog Gprog f_densematn_clear densematn_clear_spec.
Proof.
start_function.
assert_PROP (field_compatible densemat_t (DOT _data) p). 
entailer!.
unfold densemat.
Intros.
forward_call (field_address densemat_t (DOT _data) p,m*n,sh)%Z.
-
unfold field_address.
rewrite if_true by auto.
simpl.
unfold densemat_data_offset.
change_compspecs CompSpecs.
cancel.
-
unfold densemat.
entailer!.
simpl.
rewrite Z.max_r by rep_lia.
unfold field_address; rewrite if_true by auto.
simpl.
change_compspecs CompSpecs.
unfold densemat_data_offset.
cancel.
apply derives_refl'.
f_equal.
symmetry.
apply column_major_const; lia.
Qed.

Lemma body_densemat_clear: semax_body Vprog Gprog f_densemat_clear densemat_clear_spec.
Proof.
start_function.
assert_PROP (field_compatible densemat_t (DOT _data) p). {
 entailer!.
 assert (field_compatible densemat_t [] p);
   [ | auto with field_compatible].
 apply malloc_compatible_field_compatible; try reflexivity.
 destruct p; try contradiction;
 destruct H2; split; auto.
 unfold densemat_data_offset in H3; simpl in H3|-*. lia.
}
unfold densemat.
Intros.
forward.
forward.
forward_call (m,n,v,p,sh).
unfold densemat.
entailer!!.
entailer!!.
Qed.


Lemma densemat_field_compat0: 
 forall m n p, 
  0 <= m -> 0 <= n -> m*n <= Int.max_unsigned ->
  malloc_compatible
    (densemat_data_offset + sizeof (tarray tdouble (m * n))) p ->
  field_compatible0 (tarray tdouble (m*n)) (SUB (n*m)) 
        (offset_val densemat_data_offset p).
Proof.
intros.
destruct p; try contradiction.
destruct H2.
split3; [ | | split3]; auto.
- simpl; auto.
- simpl. rewrite Z.max_r by rep_lia.
unfold densemat_data_offset in *.
rewrite <- (Ptrofs.repr_unsigned i).
rewrite ptrofs_add_repr.
simpl in H3. rewrite Z.max_r in H3 by rep_lia.
rewrite Ptrofs.unsigned_repr by rep_lia.
lia.
- red. unfold offset_val, densemat_data_offset in *.
  apply align_compatible_rec_Tarray. 
  intros.
  eapply align_compatible_rec_by_value; try reflexivity.
  simpl in *.
  rewrite <- (Ptrofs.repr_unsigned i).
  rewrite ptrofs_add_repr.
  rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold natural_alignment in H2.
  repeat apply Z.divide_add_r.
  destruct H2 as [x ?]. rewrite H2. 
  exists (2*x)%Z. lia.
  exists 2; lia.
  apply Z.divide_mul_l. exists 2; lia.
- split; simpl; auto. lia.
Qed.

Lemma Znth_column_major:
  forall m n i j (v: Z -> Z -> option float), 
  0 <= i < m -> 0 <= j < n ->
  Znth (i+j*m) (column_major m n v) = v i j.
Proof.
intros.
unfold column_major.
unfold mklist.
Search (Z.of_nat (Z.to_nat _)).
rewrite <- (Z2Nat.id i) in * by lia.
rewrite <- (Z2Nat.id j) in * by lia.
forget (Z.to_nat i) as a; clear i; rename a into i.
forget (Z.to_nat j) as b; clear j; rename b into j.
rewrite <- (Z2Nat.id m) in * by lia.
forget (Z.to_nat m) as c; clear m; rename c into m.
rewrite <- (Z2Nat.id n) in H0 by lia.
forget (Z.to_nat n) as c; clear n; rename c into n.
assert (i<m)%nat by lia.
assert (j<n)%nat by lia.
rewrite Nat2Z.id.
clear H  H0.
replace (Z.of_nat i + Z.of_nat j * Z.of_nat m)%Z with (Z.of_nat (i+j*m)) by lia.
rewrite <- nth_Znth.
2:{
rewrite Zlength_correct.
split. lia.
Search (Z.of_nat _ < Z.of_nat _).
apply inj_lt.
rewrite length_concat.
rewrite map_map.
apply Nat.lt_le_trans with (n*m)%nat.
nia.
clear i j H1 H2.
replace  (fun x : nat =>
       Datatypes.length
         (map (fun i : nat => v (Z.of_nat i) (Z.of_nat x))
            (seq 0 m)))
 with (fun x:nat => m).
2:{
extensionality x.
rewrite length_map.
rewrite length_seq.
auto.
}
set (k:=O).
unfold k at 2.
replace (n*m)%nat with (n*m+k)%nat by lia.
clearbody k.
revert k; induction n; intro.
simpl. lia.
rewrite seq_S.
rewrite map_app.
simpl.
rewrite fold_right_app.
simpl.
specialize (IHn (m+k)%nat).
lia.
}
(* finish this later *)
Admitted.

Lemma body_densemat_get: semax_body Vprog Gprog f_densemat_get densemat_get_spec.
Proof.
start_function.
unfold densemat; Intros.
forward.
assert (0 <= i + j * m < m * n). {
 split. rep_lia.
 rewrite (Z.mul_comm m).
 replace n with (1 + (n-1)) by lia.
 rewrite Z.mul_add_distr_r.
 apply Z.add_lt_le_mono; try lia.
 apply Z.mul_le_mono_nonneg_r; try lia.
}
assert_PROP (field_compatible0 (tarray tdouble (m*n)) (SUB (n*m)) 
        (offset_val densemat_data_offset p)).
 entailer!.
assert_PROP (force_val
   (sem_add_ptr_int tdouble Signed (offset_val 8 p)
      (Vint
         (Int.add (Int.repr i)
            (Int.mul (Int.repr j) (Int.repr m))))) =
 field_address (tarray tdouble (m*n)) (SUB (i+j*m)) 
       (offset_val densemat_data_offset p)). {
 entailer!!.
 unfold field_address.
 rewrite if_true.
 2:{ 
  apply field_compatible_range with (lo:=0) (hi:=(m*n)%Z); auto.
  auto with field_compatible.
  rewrite (Z.mul_comm n) in H6; auto.
 }
 simpl. rewrite offset_offset_val.
 unfold densemat_data_offset.
 f_equal.
}
assert (0 <= i + j * m < Zlength (column_major m n v)) by admit.
forward.
entailer!!.
rewrite Znth_map by auto.
rewrite Znth_column_major by lia.
rewrite H1; simpl. auto.
forward.
unfold densemat.
entailer!!.
rewrite Znth_map by auto.
rewrite Znth_column_major by lia.
rewrite H1; simpl. auto.
Admitted.

(* BEGIN workaround for VST issue #814, until we can install VST 2.16 which fixes it. *)
Ltac new_simpl_fst_snd :=
  match goal with |- context[@fst ident funspec ?A] =>
     let j := eval hnf in A in 
     match j with (?x,?y) => 
      try change (fst A) with x;
      try change (snd A) with y
     end
    end.

Ltac SF_vacuous ::=
 try new_simpl_fst_snd;
 match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
 match goal with H: @eq compspecs _ _ |- _ => rewrite <- H end;
red; red; repeat simple apply conj;
[ reflexivity (* id_in_list ... *)
| repeat apply Forall_cons; (* Forall complete_type fn_vars *)
  try apply Forall_nil; reflexivity
| repeat constructor; simpl; rep_lia (* var_sizes_ok *)
| reflexivity (* fn_callconv ... *)
| split3; [reflexivity | reflexivity | intros; apply semax_vacuous] (* semax_body *)
| eexists; split; compute; reflexivity (* genv_find_func *)
].
(* END workaround for VST issue #814 *)

Definition densematVSU: @VSU NullExtension.Espec
         densemat_E densemat_imported_specs 
         ltac:(QPprog prog) densematASI (fun _ => TT).
  Proof.
    mkVSU prog densemat_internal_specs.
    - solve_SF_internal body_densemat_malloc.
    - solve_SF_internal body_densemat_free.
    - solve_SF_internal body_densematn_clear.
    - solve_SF_internal body_densemat_clear.
  Qed.
