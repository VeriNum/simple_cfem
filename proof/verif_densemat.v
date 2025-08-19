From VST.floyd Require Import proofauto VSU.
From CFEM Require Import densemat spec_alloc spec_densemat floatlib.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition densemat_E : funspecs := [].
Definition densemat_imported_specs : funspecs := 
   [free_spec'] (* subset of MallocASI *)
  ++ [surely_malloc_spec'; double_clear_spec] (* subset of allocASI *)
  ++ [fma_spec; sqrt_spec]. (* subset of MathASI *)
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
 forall {t: type} m n (x: option (ftype t)), 
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
unfold densemat, densematn.
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
change Vundef with (@val_of_optfloat Tdouble None).
apply (@column_major_const Tdouble); lia.
Qed.


Lemma body_densemat_free: semax_body Vprog Gprog f_densemat_free densemat_free_spec.
Proof.
start_function.
unfold densemat, densematn.
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
unfold densematn.
Intros.
forward_call (p,m*n,sh)%Z.
unfold densematn.
entailer!.
change_compspecs CompSpecs.
apply derives_refl'.
f_equal.
symmetry.
apply (@column_major_const Tdouble); lia.
Qed.

Lemma body_densemat_clear: semax_body Vprog Gprog f_densemat_clear densemat_clear_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (m,n,v,(offset_val densemat_data_offset p),sh).
entailer!.
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
  forall {T: type} m n i j (v: Z -> Z -> option (ftype T)), 
  0 <= i < m -> 0 <= j < n ->
  Znth (i+j*m) (column_major m n v) = v i j.
Proof.
intros.
unfold column_major.
unfold mklist.
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
rewrite Nat2Z.id.
pose (n0 := O). change (seq 0 n) with (seq n0 n).
change (Z.of_nat j) with (Z.of_nat (n0+j)). clearbody n0.
revert n0 j H2; induction n; simpl; intros. lia.
destruct j.
rewrite app_nth1 by (rewrite length_map, length_seq; lia).
rewrite nth_map_seq by lia.
f_equal; lia.
rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq.
replace (i + S j * m - m)%nat with (i + j*m)%nat by nia.
replace (n0 + S j)%nat with (S n0 + j)%nat by lia.
apply IHn.
lia.
Qed.


Lemma Zlength_concat_map_seq: forall {T} (F: nat -> nat -> T) k1 k2 m n,
  Zlength (concat (map (fun j => map (F j) (seq k1 m))
                     (seq k2 n))) = Z.of_nat (m*n).
Proof.
intros.
rewrite Zlength_concat.
revert k1 k2; induction n; intros.
simpl; lia.
simpl.
autorewrite with sublist.
transitivity (Z.of_nat m + Z.of_nat (m*n)); [ | lia].
f_equal.
apply IHn.
Qed.

Lemma Zlength_column_major: forall {T} m n (v: Z -> Z -> T),
  0 <= m -> 0 <= n -> 
  Zlength (column_major m n v) = (m*n)%Z.
Proof.
intros.
unfold column_major.
unfold mklist.
rewrite (Zlength_concat_map_seq (fun j i => v (Z.of_nat i) (Z.of_nat j))
                 O O (Z.to_nat m) (Z.to_nat n)). lia.
Qed.

Lemma firstn_seq: forall k i m, (i<=m)%nat -> firstn i (seq k m) = seq k i.
intros.
revert k i H; induction m; simpl; intros.
destruct i; try lia. auto.
destruct i; simpl; auto.
f_equal.
apply IHm.
lia.
Qed.

Lemma upd_Znth_column_major: forall {T: type} m n i j (x: ftype T) (v: Z -> Z -> option (ftype T)),
  0 <= i < m -> 0 <= j < n -> 
  upd_Znth (i + j * m) (column_major m n v) (Some x) =
  column_major m n (densemat_upd v i j x).
Proof.
intros.
unfold column_major.
unfold mklist.
set (F (v: Z -> Z -> option (ftype T)) j := 
  map (fun i => v (Z.of_nat i) (Z.of_nat j)) (seq 0 (Z.to_nat m))).
change (upd_Znth (i+j*m) (concat (map (F v) (seq 0 (Z.to_nat n)))) (Some x) =
        concat (map (F (densemat_upd v i j x)) (seq 0 (Z.to_nat n)))).
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
clear H H0.
replace (Z.of_nat i + Z.of_nat j * Z.of_nat m)%Z with (Z.of_nat (i+j*m)) by lia.
unfold upd_Znth.
unfold Sumbool.sumbool_and.
destruct (Z_le_gt_dec 0 (Z.of_nat (i + j * m))); [| lia].
destruct (Z_lt_dec _ _).
2:{
exfalso. apply n0; clear n0.
rewrite Zlength_correct.
apply inj_lt.
rewrite length_concat.
rewrite map_map.
apply Nat.lt_le_trans with (n*m)%nat.
nia.
clear i j l H1 H2 x.
replace  (fun x : nat => Datatypes.length (F v x))
 with (fun x:nat => m).
2:{
extensionality x. subst F; simpl.
rewrite length_map.
rewrite length_seq.
auto.
}
set (k:=O).
simpl.
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
clear l0.
unfold F at 2; rewrite Zlength_concat_map_seq.
set (U := densemat_upd _ _ _ _).
replace (map (F U) (seq 0 n)) with
   (map (F U) (seq 0 j ++ (seq (0+j) 1) 
    ++ seq (0+j+1) (n-(j+1)))) 
  by (f_equal; rewrite <- !seq_app; f_equal; lia).
rewrite !map_app.
change (?A :: ?B) with ([A]++B).
replace (Some x) with (U (Z.of_nat i) (Z.of_nat j))
 by (unfold U, densemat_upd; rewrite !if_true; auto).
unfold seq at 4.
simpl map.
unfold F at 4.
replace (seq 0 m) with (seq 0 i ++ seq (0+i) 1 ++ seq (0+i+1) (m-(i+1)))
  by (rewrite <- !seq_app; f_equal; lia).
rewrite !concat_app.
unfold concat at 4.
rewrite app_nil_r.
rewrite !map_app.
simpl map at 5.
set (Uij := [U _ _]). clearbody Uij.
set (U' i := U (Z.of_nat i) (Z.of_nat j)).
transitivity 
 ((concat (map (F U) (seq 0 j)) ++ map U' (seq 0 i))
  ++ Uij
  ++ (map U' (seq (0+i+1) (m-(i+1))) ++ concat (map (F U) (seq (j+1) (n-(j+1))))));
 [ | rewrite !app_assoc; auto].
f_equal; [ | f_equal].
-
rewrite (sublist_split 0 (Z.of_nat (j*m)) (Z.of_nat (i+j*m))); try lia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
f_equal.
+
replace (seq 0 n) with (seq 0 j ++ seq (0+j) (n-j))
  by (rewrite <- seq_app; f_equal ;lia).
rewrite map_app, concat_app, sublist_app1; try nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
rewrite sublist_same; try lia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
f_equal.
apply map_ext_Forall.
apply FPStdLib.Forall_seq.
intros.
unfold F.
f_equal.
rename i0 into j'.
extensionality i'.
unfold U, densemat_upd.
destruct (zeq (Z.of_nat j') (Z.of_nat j)); try lia.
if_tac; auto.
+
replace n with (j+(n-j))%nat by lia.
rewrite seq_app, map_app, concat_app.
rewrite sublist_app2; try lia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
unfold F; rewrite Zlength_concat_map_seq by nia.
replace (_ - _) with 0 by lia.
replace (_ - _) with (Z.of_nat i) by lia.
simpl.
replace (n-j)%nat with (1+(n-(j+1)))%nat by lia.
rewrite seq_app, map_app, concat_app, sublist_app1.
2: lia.
2: simpl; unfold F; rewrite Zlength_app, Zlength_map, Zlength_nil, Zlength_correct, length_seq; lia.
simpl. rewrite app_nil_r.
unfold F.
rewrite sublist_map.
unfold sublist. rewrite Nat2Z.id.
rewrite firstn_seq by lia.
rewrite map_skipn. simpl.
apply map_ext_Forall.
apply FPStdLib.Forall_seq.
intros.
unfold U', U, densemat_upd.
if_tac; try lia.
auto.
-
rewrite (sublist_split _ (Z.of_nat ((j+1)*m))); try  nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
f_equal.
+
replace (seq 0 n) with (seq 0 (j+1+(n-(j+1)))) by (f_equal; lia).
rewrite seq_app, map_app, concat_app.
rewrite sublist_app1; try nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
replace (seq 0 (j+1)) with (seq 0 (j+(j+1-j))) by (f_equal; lia).
rewrite seq_app.
rewrite map_app, concat_app.
rewrite sublist_app2; try nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
unfold F at 1 2; rewrite Zlength_concat_map_seq by nia.
replace (_ - _) with (Z.of_nat i+1) by nia.
replace (_ - _) with (Z.of_nat m) by nia.
replace (j+1-j)%nat with 1%nat by lia.
simpl. rewrite app_nil_r.
unfold F.
rewrite sublist_map.
replace (seq 0 m) with (seq 0 ((i+1)+(m-(i+1)))) by (f_equal; lia).
rewrite seq_app.
rewrite sublist_app2 by (rewrite Zlength_correct, length_seq; lia).
rewrite Zlength_correct, length_seq.
replace (_ - _) with 0 by lia.
rewrite sublist_same.
2: lia.
2: rewrite  Zlength_correct, length_seq; lia.
simpl.
apply map_ext_Forall.
apply FPStdLib.Forall_seq.
intros.
unfold U', U, densemat_upd.
if_tac; try lia. auto.
+
replace (seq 0 n) with (seq 0 (j+1+(n-(j+1)))) by (f_equal; lia).
rewrite seq_app, map_app, concat_app.
rewrite sublist_app2; try nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
unfold F at 1 2; rewrite Zlength_concat_map_seq by nia.
replace (_ - _) with 0 by lia.
replace (Z.of_nat _ - _) with (Z.of_nat (m * (n-(j+1)))) by nia.
simpl.
rewrite sublist_same; try nia.
2: unfold F; rewrite Zlength_concat_map_seq; nia.
f_equal.
apply map_ext_Forall.
apply FPStdLib.Forall_seq.
intros.
unfold F, U', U, densemat_upd.
if_tac; try lia.
apply map_ext_Forall.
apply FPStdLib.Forall_seq.
intros.
if_tac; try lia; auto.
Qed.

Lemma body_densematn_get: semax_body Vprog Gprog f_densematn_get densematn_get_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
pose proof (Zlength_column_major m n v ltac:(lia) ltac:(lia)).
assert (0 <= i + j * m < Zlength (column_major m n v)) by nia.
forward.
entailer!.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by auto.
rewrite (@Znth_column_major Tdouble) by lia.
rewrite H1; simpl; auto.
forward.
entailer!!.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by auto.
rewrite (@Znth_column_major Tdouble) by lia.
rewrite H1; simpl; auto.
Qed.

Lemma body_densemat_get: semax_body Vprog Gprog f_densemat_get densemat_get_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*; Intros.
forward.
forward_call (m,n,v, offset_val densemat_data_offset p, sh, i, j, x).
forward.
entailer!!.
Qed.


Lemma body_densematn_set: semax_body Vprog Gprog f_densematn_set densematn_set_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
assert (0 <= i + j * m < m * n) by nia. 
forward.
entailer!.
apply derives_refl'.
f_equal.
change (Vfloat x) with (@val_of_optfloat Tdouble (Some x)).
change (reptype_ftype _ ?A) with A.
rewrite upd_Znth_map.
f_equal.
rewrite (@upd_Znth_column_major Tdouble) by lia.
auto.
Qed.


Lemma body_densemat_set: semax_body Vprog Gprog f_densemat_set densemat_set_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward_call (m,n,v, offset_val densemat_data_offset p, sh, i, j, x).
entailer!.
Qed.

Lemma body_densematn_addto: semax_body Vprog Gprog f_densematn_addto densematn_addto_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
pose proof (Zlength_column_major m n v ltac:(lia) ltac:(lia)).
assert (0 <= i + j * m < Zlength (column_major m n v)) by nia.
forward.
entailer!.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by auto.
rewrite (@Znth_column_major Tdouble) by lia.
rewrite H1. simpl; auto.
forward.
entailer!!.
apply derives_refl'; f_equal.
change (Vfloat x) with (@val_of_optfloat Tdouble (Some x)).
change (reptype_ftype _ ?A) with A.
rewrite Znth_map, (@Znth_column_major Tdouble), H1 by (auto; lia).
simpl.
change (Vfloat ?A) with (@val_of_optfloat Tdouble (Some A)).
rewrite upd_Znth_map.
rewrite (@upd_Znth_column_major Tdouble )by lia.
auto.
Qed.


Lemma body_densemat_addto: semax_body Vprog Gprog f_densemat_addto densemat_addto_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward_call (m,n,v, offset_val densemat_data_offset p, sh, i, j, y, x).
entailer!!.
Qed.


Lemma body_data_norm2: semax_body Vprog Gprog f_data_norm2 data_norm2_spec.
Proof.
start_function.
forward.
forward_for_simple_bound (Zlength v) (EX j:Z,
      PROP ()
      LOCAL (temp _result (val_of_float (norm2 (sublist 0 j v)));
             temp _data p; temp _n (Vint (Int.repr (Zlength v))))
      SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p))%assert.
- entailer!!.
- forward.
  forward_call.
  forward.
  entailer!!.
  (* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
  set (e := Binary.Bfma _ _ _ _ _ _ _ _ _).
  replace e with (FPStdLib.BFMA (Znth i v) (Znth i v) (norm2 (sublist 0 i v)))
    by (unfold e,BFMA,FPCore.fma_nan; simpl; f_equal; f_equal; apply proof_irr).
  rewrite <- norm2_snoc.
  rewrite (sublist_split 0 i (i+1)) by rep_lia.
  rewrite (sublist_one i) by rep_lia. reflexivity.
- forward.
  entailer!!.
  simpl. rewrite sublist_same by rep_lia. reflexivity.
Qed.

Lemma body_data_norm: semax_body Vprog Gprog f_data_norm data_norm_spec.
Proof.
start_function.
forward_call.
forward_call.
forward.
entailer!!.
(* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
f_equal.
unfold BSQRT, UNOP.
simpl.
f_equal.
extensionality z.
f_equal.
apply proof_irr.
Qed.


Lemma val_of_optfloat_column_major:
  forall t m n (v: Z -> Z -> ftype t),
  map val_of_optfloat (column_major m n (fun i j : Z => Some (v i j)))
  = map val_of_float (column_major m n v).
Proof.
intros.
unfold column_major.
rewrite !concat_map.
f_equal.
unfold mklist. rewrite !map_map.
f_equal. extensionality x. rewrite !map_map. f_equal.
Qed.

Lemma body_densemat_norm2: semax_body Vprog Gprog f_densemat_norm2 densemat_norm2_spec.
Proof.
start_function.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major m n v, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
- forward.
  simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   rewrite Z.max_r by lia.
  cancel.
Qed.

Lemma body_densemat_norm: semax_body Vprog Gprog f_densemat_norm densemat_norm_spec.
Proof.
start_function.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major m n v, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
- forward.
  simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   rewrite Z.max_r by lia.
  cancel.
Qed.

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
    - solve_SF_internal body_densemat_get.
    - solve_SF_internal body_densematn_get.
    - solve_SF_internal body_densemat_set.
    - solve_SF_internal body_densematn_set.
    - solve_SF_internal body_densemat_addto.
    - solve_SF_internal body_densematn_addto.
    - solve_SF_internal body_data_norm.
    - solve_SF_internal body_data_norm2.
    - solve_SF_internal body_densemat_norm.
    - solve_SF_internal body_densemat_norm2.
  Qed.

