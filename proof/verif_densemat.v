From VST.floyd Require Import proofauto VSU.
From CFEM Require Import densemat spec_alloc spec_densemat floatlib cholesky_model.
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
unfold mklist, Zrangelist.
rewrite !Z.sub_0_r.
forget (Z.to_nat m) as a.
forget (Z.to_nat n) as b. clear m n H H0.
clear.
rewrite Nat.mul_comm.
symmetry.
transitivity (concat (repeat (repeat (val_of_optfloat x) a) b)).
 +
 induction b.
  * auto.
  * simpl. rewrite repeat_app. f_equal; auto.
 + pose (i := O). change (seq.iota (Z.to_nat 0) b) with (seq.iota i b).
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
unfold mklist, Zrangelist.
rewrite !Z.sub_0_r.
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
change (Z.to_nat 0) with O.
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
replace (fun x : Z =>
       Datatypes.length
         (map (fun i : Z => v i x)
            (map Z.of_nat (seq.iota 0 m))))
 with (fun _:Z => m)
  by (extensionality x; rewrite !length_map, length_seq; auto).
rewrite map_map.
apply Nat.eq_le_incl.
set (k:=O).
unfold k at 1. 
replace O with (k*m)%nat by lia.
replace (seq.iota k n) with (seq.iota O (n-k)) by (f_equal; lia).
assert (k<=n)%nat by lia.
clearbody k.
set (j := O). clearbody j.
replace (n*m)%nat with ((n-k+k)*m)%nat by nia.
forget (n-k)%nat as i.
clear H.
revert k j; induction i; intros.
simpl. auto.
simpl.
f_equal.
apply IHi.
}
rewrite Nat2Z.id.
simpl.
change seq.iota with seq.
pose (n0 := O). change (seq 0 n) with (seq n0 n).
change (Z.of_nat j) with (Z.of_nat (n0+j)). clearbody n0.
rewrite !map_map.
revert n0 j H2; induction n; simpl; intros. lia.
rewrite !map_map.
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

Lemma Zlength_concat_map_Zrangelist: forall {T} (F: Z -> Z -> T) 
  (k1 k2 m n : Z),
 k1 <= m -> k2 <= n -> 
 Zlength
  (concat
     (map
        (fun j : Z => map (fun i => F i j) (Zrangelist k1 m)) (Zrangelist k2 n))) = ((m-k1) * (n-k2))%Z.
Proof.
intros.
unfold Zrangelist.
rewrite Zlength_concat.
rewrite map_map.
replace  (fun _ : Z => Zlength _) with (fun _: Z => m-k1).
2:{ extensionality x. rewrite !Zlength_map, Zlength_correct, length_seq. lia. }
rewrite map_map.
rewrite <- (Z2Nat.id (n-k2)) at 2 by lia.
forget (Z.to_nat k2) as a.
revert a; induction (Z.to_nat (n-k2)); intros; simpl.
nia.
rewrite IHn0.
nia.
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
rewrite (Zlength_concat_map_Zrangelist v); lia.
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

Lemma Zrangelist_split: 
 forall lo mid hi,  
  0 <= lo -> 
  lo <= mid <= hi -> Zrangelist lo hi = Zrangelist lo mid ++ Zrangelist mid hi.
Proof.
intros.
unfold Zrangelist.
rewrite <- map_app.
f_equal.
replace (Z.to_nat mid) with (Z.to_nat lo + Z.to_nat (mid-lo))%nat by lia.
rewrite <- seq_app.
change seq.iota with seq.
f_equal.
lia.
Qed.


Lemma Forall_Zrangelist:
 forall (P: Z -> Prop) (lo hi: Z), 
   0 <= lo <= hi -> 
  (forall i, lo <= i < hi -> P i) ->
  Forall P (Zrangelist lo hi). 
Proof.
intros.
unfold Zrangelist.
apply Forall_map.
apply FPStdLib.Forall_seq.
intros.
apply H0.
lia.
Qed.


Lemma Zlength_Zrangelist:
  forall lo hi, lo <= hi -> Zlength (Zrangelist lo hi) = (hi-lo).
Proof.
intros.
rewrite Zlength_correct.
unfold Zrangelist.
rewrite length_map, length_seq. lia.
Qed.

Lemma Zrangelist_one: forall i j, 0 <= i -> i+1=j -> 
  Zrangelist i j = [i].
Proof.
intros.
unfold Zrangelist. replace (j-i) with 1 by lia.
simpl. f_equal. lia.
Qed.

Lemma upd_Znth_column_major: forall {T: type} m n i j (x: ftype T) (v: Z -> Z -> option (ftype T)),
  0 <= i < m -> 0 <= j < n -> 
  upd_Znth (i + j * m) (column_major m n v) (Some x) =
  column_major m n (densemat_upd v i j x).

Proof.
intros.
unfold column_major.
unfold mklist.
rewrite (Zrangelist_split 0 j n) by lia.
rewrite (Zrangelist_split j (j+1) n) by lia.
rewrite !map_app.
rewrite !concat_app.
rewrite upd_Znth_app2
 by (rewrite Zlength_app, !Zlength_concat_map_Zrangelist; nia).
rewrite Zlength_concat_map_Zrangelist by lia.
rewrite upd_Znth_app1
 by (rewrite !Zlength_concat_map_Zrangelist; lia).
f_equal; [ | f_equal].
-
f_equal.
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros.
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros.
unfold densemat_upd.
repeat if_tac; try lia; auto.
-
rewrite (Zrangelist_one j) by lia.
simpl.
rewrite !app_nil_r.
replace (_ - _) with i by nia.
unfold densemat_upd.
destruct (zeq j j); try lia.
rewrite (Zrangelist_split 0 i m) by lia.
rewrite (Zrangelist_split i (i+1) m) by lia.
rewrite !map_app.
rewrite upd_Znth_app2.
2:{ rewrite Zlength_app, !Zlength_map, !Zlength_Zrangelist; lia. }
rewrite Zlength_map, Zlength_Zrangelist by lia.
rewrite upd_Znth_app1.
2:{ rewrite Zlength_map, Zlength_Zrangelist; lia. }
f_equal; [ | f_equal].
+
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros. if_tac; try lia; auto.
+
rewrite Zrangelist_one by lia.
simpl.
rewrite if_true by auto.
replace (i-(i-0)) with 0 by lia.
reflexivity.
+
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros. if_tac; try lia; auto.
-
f_equal.
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros.
apply map_ext_Forall.
apply Forall_Zrangelist.
lia.
intros.
unfold densemat_upd.
repeat if_tac; try lia; auto.
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

Lemma body_densematn_cfactor: semax_body Vprog Gprog f_densematn_cfactor densematn_cfactor_spec.
Proof.
start_function.
assert_PROP (0<=n<=Int.max_signed) by entailer!.
forward_for_simple_bound n 
  (EX j:Z, EX R: Z->Z->ftype the_type,
      PROP(cholesky_jik_upto n 0 j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh n n (joinLU n M (fun i j : Z => Some (R i j))) p))%assert.
-
Exists A.
entailer!!.
intros i j; split; [ | split3]; intros; try lia; auto; red; intros; try lia.
-
rename i into j.
forward_for_simple_bound j 
  (EX i:Z, EX R: Z->Z->ftype the_type,
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh n n (joinLU n M (fun i j : Z => Some (R i j))) p))%assert.
 + Exists R.
   entailer!!.
 + clear R.  rename R0 into R.
   forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,i,j,R i j).
   unfold joinLU; replace (andb _ _) with true by lia; auto.
   Intros vret.
   destruct (H2 i j) as [_ [_ [_ ?]]]. rewrite H4 in H3 by lia.
   subst vret. clear H4.
   forward_for_simple_bound i
     (EX k:Z, 
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _s (val_of_float (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh n n (joinLU n M (fun i j : Z => Some (R i j))) p))%assert.
  * entailer!!.
  * rename i0 into k.
    forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,k,i,R k i).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    Intros vret. subst vret.
    forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,k,j,R k j).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    forward.
    change (Vfloat
            (Float.sub (subtract_loop A R i j k)
               (Float.mul (R k i) (R k j))))
    with (val_of_float (BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)))).
    entailer!!.
     f_equal.
     unfold subtract_loop.
     replace (seq.iota 0 (Z.to_nat (k + 1))) with (seq.iota 0 (Z.to_nat k) ++ [Z.to_nat k]).
     rewrite !map_app, fold_left_app.
     simpl. f_equal. rewrite Z2Nat.id by lia. auto.
     replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
     rewrite iota_plus1. f_equal.
    *
    forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,i,i,R i i).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    Intros vret. subst vret.
    forward_call.
     change (Float.div ?A ?B) with (BDIV A B).
     set (rij := BDIV _ _).
     Exists (updij R i j rij).
     entailer!!.
     apply update_i_lt_j; auto. lia.
     apply derives_refl'. f_equal.
     unfold densemat_upd, updij.
     extensionality i' j'.
     subst rij.
     unfold joinLU.
     repeat if_tac; try lia; subst; auto.
     replace (andb _ _) with true by lia; auto.
  + clear R. Intros R.
    forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,j,j,R j j).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    deadvars!.
   forward_for_simple_bound j
     (EX k:Z, 
      PROP()
      LOCAL(temp _s (val_of_float (subtract_loop A R j j k) );
            temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh n n (joinLU n M (fun i j : Z => Some (R i j))) p)).
  * entailer!!. unfold subtract_loop. simpl.
    f_equal. destruct (H1 j j) as [_ [_ [? ?]]]. symmetry; apply H3; lia.
  * rename i into k. 
    forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,sh,k,j,R k j).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    forward.
    change Vfloat with (@val_of_float the_type).
    change Float.sub with (@BMINUS _ the_type).
    change Float.mul with (@BMULT _ the_type).
    entailer!!. f_equal.
    apply @subtract_another; lia.
  * forward_call.
    forward_call.
    replace (Binary.Bsqrt _ _ _ _ _ _) with (@BSQRT _ the_type).
2:{ (* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
 unfold BSQRT, UNOP. f_equal. extensionality x. simpl. f_equal. apply proof_irr.
   }
    set (Rx := densemat_upd _ _ _ _).
    assert (Rx = joinLU n M (fun i' j' => Some (updij R j j (BSQRT (subtract_loop A R j j j)) i' j'))). {
      extensionality i' j'.
      subst Rx. unfold densemat_upd, updij.
      repeat if_tac; try lia; auto.
      unfold joinLU; replace (andb _ _) with true by lia; auto.
      subst i'. rewrite !if_true by auto. auto.
      subst i'.
      unfold joinLU.
      destruct (andb _ _) eqn:?H; auto.
      repeat if_tac; try lia; auto.
      unfold joinLU.
      destruct (andb _ _) eqn:?H; auto.
      repeat if_tac; try lia; auto.   
    }
    rewrite H2; clear Rx H2.     
    set (R' := updij _ _ _ _).
    Exists R'.
    entailer!!.
    apply cholesky_jik_upto_newrow; auto.       
 - Intros R. Exists R.
   entailer!!.
   intros i j.
   specialize (H0 i j).   
   destruct (zlt j n);[ | split; intros; lia].
   destruct H0.
   apply H0; auto.
Qed.


Lemma body_densemat_cfactor: semax_body Vprog Gprog f_densemat_cfactor densemat_cfactor_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_if True; [ | contradiction | ].
forward.
entailer!!.
forward.
forward_call (sh,n,M,A,offset_val densemat_data_offset p).
Intros R. Exists R.
entailer!!.
Qed.


Lemma Zlength_forward_subst_step:
  forall {t} n (L: Z -> Z -> ftype t) x i,
   Zlength (forward_subst_step n L x i) = Zlength x.
Proof.
intros.
unfold forward_subst_step.
list_solve.
Qed.

Lemma Zlength_backward_subst_step:
  forall {t} n (L: Z -> Z -> ftype t) x i,
   Zlength (backward_subst_step n L x i) = Zlength x.
Proof.
intros.
unfold backward_subst_step.
list_solve.
Qed.


Lemma fold_left_preserves: forall [A C: Type] (g: A -> C) [B: Type] (f: A -> B -> A) (bl: list B),
  (forall x y, g (f x y) = g x) -> 
  (forall x, g (fold_left f bl x) = g x).
Proof.
intros.
revert x; induction bl; simpl; intros; auto.
rewrite IHbl; auto.
Qed.

Lemma Zrangelist_plus1:
  forall lo hi, 0 <= lo <= hi -> Zrangelist lo (hi + 1) = Zrangelist lo hi ++ [hi].
Proof.
intros.
unfold Zrangelist.
replace [hi] with (map Z.of_nat [Z.to_nat hi]) by (simpl; f_equal; lia).
rewrite <- map_app. f_equal.
replace (Z.to_nat (hi+1-lo)) with (Z.to_nat (hi-lo)+1)%nat by lia.
rewrite iota_plus1.
f_equal. f_equal. lia.
Qed.

Lemma Zrangelist_minus1:
  forall lo hi, 0 <= lo < hi -> Zrangelist lo hi = [lo] ++ Zrangelist (lo+1) hi.
Proof.
intros.
unfold Zrangelist.
replace [lo] with (map Z.of_nat [Z.to_nat lo]) by (simpl; f_equal; lia).
rewrite <- map_app. f_equal.
replace (Z.to_nat (hi-lo)) with (S (Z.to_nat (hi-(lo+1))))%nat by lia.
simpl. f_equal. f_equal. lia.
Qed.

Lemma body_densematn_csolve: semax_body Vprog Gprog f_densematn_csolve densematn_csolve_spec.
Proof.
start_function. 
assert_PROP (0 <= n <= Int.max_signed /\ Zlength x = n)
  by (entailer!; list_solve).
destruct H.
forward_for_simple_bound n (EX i:Z,
   PROP ( )
   LOCAL (temp _R p; temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh n n (joinLU n M (fun i j : Z => Some (R i j))) p;
        data_at sh (tarray the_ctype n) (map val_of_float 
         (fold_left (forward_subst_step n (transpose R)) (Zrangelist 0 i) x)) xp))%assert.
- entailer!!.
- forward. {
    entailer!!.
    rewrite Znth_map. simpl; auto.
    rewrite fold_left_preserves; auto.
    intros. apply Zlength_forward_subst_step.
  }
  rewrite Znth_map.
  set (x' := fold_left _ _ _).
  set (xi := Znth i x').
  forward_for_simple_bound i (EX j:Z,
   PROP ( )
   LOCAL (temp _bi (val_of_float (fold_left BMINUS 
                     (map (fun j => BMULT (transpose R i j) (Znth j x')) (Zrangelist 0 j))
                      (Znth i x'))); 
          temp _i (Vint (Int.repr i)); temp _R p; 
   temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh n n
          (joinLU n M (fun i0 j : Z => Some (R i0 j))) p;
   data_at sh (tarray the_ctype n) (map val_of_float x') xp))%assert.
 + entailer!!.
 + rename i0 into j.
   assert (Zlength x' = Zlength x). {
     apply fold_left_preserves; try lia.
     intros. apply Zlength_forward_subst_step.
   }
   forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,rsh,j,i,R j i).
   unfold joinLU; replace (andb _ _) with true by lia; auto.
   forward. 
    entailer!!;  rewrite Znth_map; simpl; auto; lia.
   forward.
   entailer!!.
   rewrite Znth_map by lia.
   simpl. 
   rewrite Zrangelist_plus1 by lia.
   rewrite map_app.
   simpl map.
   rewrite fold_left_app.
   reflexivity.
 +  forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,rsh,i,i,R i i).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    forward.
   entailer!!.
   apply derives_refl'. f_equal.
   rewrite upd_Znth_map. f_equal.
   rewrite Zrangelist_plus1 by lia.
   rewrite fold_left_app.
   reflexivity.
 + rewrite fold_left_preserves. lia.
   intros. apply Zlength_forward_subst_step.
- 
 deadvars!.
 set (x1 := fold_left _ _ _).
 assert (Zlength x1 = n). {
     rewrite <- H0; apply fold_left_preserves; try lia.
     intros. apply Zlength_forward_subst_step.
   }
forward_loop (EX i:Z,
   PROP (0 <= i <= n)
   LOCAL (temp _i__1 (Vint (Int.repr i));
          temp _R p; temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh n n (joinLU n M (fun i j : Z => Some (R i j))) p;
   data_at sh (tarray the_ctype n)
     (map val_of_float 
         (fold_left (backward_subst_step n R) (rev (Zrangelist i n)) x1)) xp))%assert.
 + forward.
  Exists n. entailer!!. 
  unfold Zrangelist. rewrite Z.sub_diag. simpl. cancel.
 + Intros i.
  set (x2 := fold_left (backward_subst_step n R) (rev (Zrangelist i n)) x1).
  assert (Zlength x2 = n). {
     rewrite <- H1.
     apply fold_left_preserves; try lia.
     intros. apply Zlength_backward_subst_step.
   }
  forward_if.
  * forward. entailer!!; rewrite Znth_map; simpl; auto; lia.
    rewrite Znth_map by lia.
  forward_for_simple_bound n (EX j:Z,
   PROP (i <= j)
   LOCAL (temp _yi (val_of_float 
            (fold_left BMINUS 
              (map (fun j => BMULT (R (i-1) j) (Znth j x2)) (Zrangelist i j))
                      (Znth (i-1) x2))); 
          temp _i__1 (Vint (Int.repr i)); temp _R p; 
          temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh n n (joinLU n M (fun i j : Z => Some (R i j))) p;
        data_at sh (tarray the_ctype n) (map val_of_float x2) xp))%assert.
  -- forward. Exists i; entailer!!. unfold Zrangelist; rewrite Z.sub_diag; reflexivity. 
  -- rename i0 into j. Intros.
   forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,rsh,i-1,j,R (i-1) j).
   unfold joinLU; replace (andb _ _) with true by lia; auto.
   forward. 
    entailer!!;  rewrite Znth_map; simpl; auto; lia.
   forward.
   entailer!!.
   rewrite Znth_map by lia.
   simpl. 
   rewrite Zrangelist_plus1 by lia.
   rewrite map_app.
   simpl map.
   rewrite fold_left_app.
   reflexivity.
 -- forward_call (n,n,(joinLU n M (fun i j : Z => Some (R i j))),p,rsh,i-1,i-1,R (i-1) (i-1)).
    unfold joinLU; replace (andb _ _) with true by lia; auto.
    Intros vret. subst vret.
    forward.
    forward.
    Exists (i-1).
    entailer!!.
    apply derives_refl'. f_equal.
    rewrite upd_Znth_map. f_equal.
   rewrite (Zrangelist_minus1 (i-1)) by lia.
   simpl rev.
   rewrite fold_left_app.
   unfold backward_subst_step.
   simpl.
   replace (i-1+1) with i by lia.
   reflexivity.
  *
   forward.
   entailer!!.
   assert (i=0) by lia. subst i.
   apply derives_refl.
Qed.


Lemma body_densemat_csolve: semax_body Vprog Gprog f_densemat_csolve densemat_csolve_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros. 
forward.
forward_call (rsh,sh,n,M,R,x, offset_val densemat_data_offset p, xp).
entailer!!.
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
    - solve_SF_internal body_densemat_csolve.
    - solve_SF_internal body_densematn_csolve.
    - solve_SF_internal body_densemat_cfactor.
    - solve_SF_internal body_densematn_cfactor.
  Qed.

