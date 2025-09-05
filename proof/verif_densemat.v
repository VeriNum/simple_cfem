From VST.floyd Require Import proofauto VSU.
From CFEM Require Import densemat spec_alloc spec_densemat floatlib cholesky_model.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.


From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import fintype matrix.

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

Lemma map_const_ord_enum: forall {T} n (x: T), map (fun _ => x) (ord_enum n) = repeat x n.
Proof.
 intros.
 pose proof @val_ord_enum n.
 set (F := eqtype.isSub.val_subdef _ ) in H.
 transitivity (map (fun _: nat => x) (map F (ord_enum n))).
rewrite map_map. f_equal.
change @seq.map with @map in H.
rewrite H.
clear.
forget O as k.
revert k.
induction n; simpl; intros; f_equal; auto.
Qed.

Lemma column_major_const:
 forall {t: type} m n (x: option (ftype t)), 
  map val_of_optfloat (@column_major _ m n (const_mx x)) =
  Zrepeat (val_of_optfloat x) (Z.of_nat m * Z.of_nat n).
Proof.
intros.
unfold column_major, Zrepeat.
rewrite Z2Nat.inj_mul by lia.
rewrite !Nat2Z.id.
rewrite <- map_repeat.
f_equal.
unfold mklist.
symmetry.
transitivity (concat (repeat (repeat x m) n)).
-
 rewrite Nat.mul_comm. induction n; simpl; auto.
 rewrite repeat_app. f_equal; auto.
- f_equal.
 replace (fun j : 'I_n => map (fun i : 'I_m => fun_of_matrix (const_mx x) i j) (ord_enum m))
  with (fun _: 'I_n => repeat x m).
 rewrite map_const_ord_enum; auto.
 extensionality j.
 replace (fun i : 'I_m => fun_of_matrix (const_mx x) i j) with (fun _: 'I_m => x).
 rewrite map_const_ord_enum; auto.
 extensionality i.
 unfold const_mx; rewrite mxE; auto.
Qed.

Lemma body_densemat_malloc: semax_body Vprog Gprog f_densemat_malloc densemat_malloc_spec.
Proof.
start_function.
forward_call (densemat_data_offset+Z.of_nat m*Z.of_nat n*sizeof(tdouble), gv);
unfold densemat_data_offset.
simpl; rep_lia.
Intros p.
assert_PROP (isptr p /\ malloc_compatible (8 + Z.of_nat m * Z.of_nat n * sizeof tdouble) p) by entailer!.
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
rewrite (Z.mul_comm (Z.of_nat m * Z.of_nat n)).
entailer!.
unfold_data_at (data_at _ _ _ _).
cancel.
rewrite field_at_data_at.
simpl.
sep_apply data_at_zero_array_inv.
rewrite emp_sepcon.
unfold Ptrofs.add.
rewrite Ptrofs.unsigned_repr by rep_lia.
replace (8 * (Z.of_nat m*Z.of_nat n))%Z with (sizeof (tarray tdouble (Z.of_nat m*Z.of_nat n)))%Z
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
destruct M as [[m n] M].
simpl in M|-*.
Intros.
assert_PROP (isptr p
      /\ malloc_compatible (densemat_data_offset +
      sizeof (tarray tdouble (Z.of_nat m * Z.of_nat n))) p) by entailer!.
destruct H2 as [H2 COMPAT].
simpl in COMPAT. rewrite Z.max_r in COMPAT by lia.
red in COMPAT.
forward_call (densemat_data_offset+Z.of_nat m*Z.of_nat n*sizeof(tdouble), p, gv).
-
revert Frame.
instantiate (1:=nil). intro.
subst Frame.
rewrite if_false by (intro; subst; contradiction).
simpl.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (Z.of_nat m*Z.of_nat n)).
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
pose (x:= sizeof (tarray tdouble (Z.of_nat m*Z.of_nat n))).
simpl in x.
replace (8 * (Z.of_nat m*Z.of_nat n))%Z with (8 * (Z.max 0 (Z.of_nat m*Z.of_nat n)))%Z by rep_lia.
apply data_at_memory_block.
-
entailer!.
Qed.

(*  The following destructs any let-definitions immediately after PRE or POST *)
Ltac destruct_it B :=
 match B with 
 | ?C _ => destruct_it C
 | let '(x,y) := ?A in _ => destruct A as [x y]
 | match ?A with _ => _ end =>
     match type of A with
     | @sigT _ (fun x => _) => destruct A as [x A] 
     end
 end.

Ltac destruct_PRE_POST_lets :=
repeat lazymatch goal with 
| |- semax _ (sepcon (close_precondition _ ?B) _) _ _ => destruct_it B
| |- semax _ _ _ (frame_ret_assert (function_body_ret_assert _ ?B) _) => destruct_it B
end;
repeat change (fst (?A,?B)) with A in *;
repeat change (snd (?A,?B)) with B in *.

Ltac start_function ::= start_function1; destruct_PRE_POST_lets; start_function2; start_function3.


Lemma body_densematn_clear: semax_body Vprog Gprog f_densematn_clear densematn_clear_spec.
Proof.
start_function.
rename X into M.
unfold densematn.
Intros.
forward_call (p,Z.of_nat m* Z.of_nat n,sh)%Z.
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
rename X into M.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
pose (X := existT _ (m,n) M : {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}).
forward_call (X, offset_val densemat_data_offset p, sh).
entailer!.
Qed.

Lemma densemat_field_compat0: 
 forall m n p, 
  0 <= m -> 0 <= n -> m*n <= Int.max_unsigned ->
  malloc_compatible
    (densemat_data_offset + sizeof (tarray tdouble (m * n))) p ->
  field_compatible0 (tarray tdouble (m*n)) (SUB (n * m)) 
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

Lemma length_ord_enum: forall n, length (ord_enum n) = n.
Proof.
intros.
transitivity (length (repeat tt n)).
rewrite <- (@map_const_ord_enum unit).
rewrite length_map; auto.
rewrite repeat_length; auto.
Qed.

Lemma nth_ord_enum: forall n d (i: 'I_n), nth (nat_of_ord i) (ord_enum n) d = i.
Proof.
intros.
pose proof (val_ord_enum n).
set (F := eqtype.isSub.val_subdef _) in H.
simpl in F.
change (@seq.map) with @map in H.
change @seq.iota with @seq in H.
pose proof (ltn_ord i).
subst F.
simpl in *.
assert (nth (nat_of_ord i) (map (nat_of_ord(n:=n)) (ord_enum n)) (nat_of_ord d) = nat_of_ord i).
intros. rewrite H. rewrite seq_nth; try lia.
rewrite map_nth in H1.
apply ord_inj in H1.
auto.
Qed.

Lemma Znth_column_major:
  forall {T} {INH: Inhabitant T} m n i j (M: 'M[T]_(m,n)), 
  Znth (Z.of_nat (nat_of_ord i+nat_of_ord j * m))%nat (column_major M) = M i j.
Proof.
intros.
unfold column_major.
unfold mklist.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
pose proof (ltn_ord i). pose proof (ltn_ord j).
assert (Zlength (ord_enum m) = Z.of_nat m). rewrite Zlength_correct, length_ord_enum; auto.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
replace (ord_enum n) with 
 (sublist 0 (Z.of_nat j) (ord_enum n) ++ 
  sublist (Z.of_nat j) (Z.of_nat j+1) (ord_enum n) ++ 
  sublist (Z.of_nat j+1) (Z.of_nat n) (ord_enum n))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite !concat_app.
rewrite Znth_app2.
2:{
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)). lia.
rewrite Zlength_map. rewrite Zlength_sublist; try lia.
apply Forall_map.
apply Forall_sublist.
apply Forall_forall.
intros.
simpl.
list_solve.
}
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)).
2: list_solve.
2:{ 
apply Forall_map.
apply Forall_sublist.
apply Forall_forall.
intros.
simpl.
list_solve.
}
replace (_ - _) with (Z.of_nat i) by lia.
rewrite Znth_app1.
2:{
rewrite (@sublist_one _ j); try lia.
simpl.
list_solve.
}
rewrite (@sublist_one _ j); try lia.
simpl.
rewrite app_nil_r.
rewrite (@Znth_map _ i); try lia.
rewrite <- !nth_Znth'.
rewrite !nth_ord_enum.
auto.
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

Lemma Zlength_column_major: forall {T} m n (M: 'M[T]_(m,n)),
  Zlength (column_major M) = (Z.of_nat m*Z.of_nat n)%Z.
Proof.
intros.
unfold column_major.
unfold mklist.
rewrite (@Zlength_concat' _ (Z.of_nat n) (Z.of_nat m)).
lia.
rewrite Zlength_map, Zlength_correct, length_ord_enum; auto.
apply Forall_map.
apply Forall_forall; intros.
simpl.
rewrite Zlength_map, Zlength_correct, length_ord_enum; auto.
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

Lemma in_sublist_ord_enum: forall n (a: 'I_n) (lo hi: Z),
  0 <= lo <= hi -> hi <= Z.of_nat n ->
  In a (sublist lo hi (ord_enum n)) -> (lo <= Z.of_nat a < hi)%Z.
Proof.
intros.
pose proof (val_ord_enum n). simpl in H2.
assert (In (nat_of_ord a) (sublist lo hi (map (nat_of_ord(n:=n)) (ord_enum n)))).
rewrite sublist_map. apply in_map. auto.
change @seq.map with @map in H2.
rewrite H2 in H3.
change seq.iota with seq in H3.
forget (nat_of_ord a) as i.
apply In_Znth in H3.
destruct H3 as [j [? ?]].
assert (Zlength (seq 0 n) = Z.of_nat n).
rewrite Zlength_correct, length_seq; auto.
rewrite Zlength_sublist in H3; try lia.
rewrite Znth_sublist in H4 by list_solve.
subst.
rewrite <- nth_Znth by lia.
rewrite seq_nth by lia.
lia.
Qed.

Lemma upd_Znth_column_major: forall {T} [m n] (M:'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x:T),
   upd_Znth (Z.of_nat (i + j * m)) (column_major M) x = column_major (matrix_upd M i j x).
Proof.
intros.
unfold column_major.
unfold mklist.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
pose proof (ltn_ord i). pose proof (ltn_ord j).
assert (Hm: Inhabitant 'I_m). apply i.
assert (Hn: Inhabitant 'I_n). apply j.
assert (Zlength (ord_enum m) = Z.of_nat m). rewrite Zlength_correct, length_ord_enum; auto.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
replace (ord_enum n) with 
 (sublist 0 (Z.of_nat j) (ord_enum n) ++ 
  sublist (Z.of_nat j) (Z.of_nat j+1) (ord_enum n) ++ 
  sublist (Z.of_nat j+1) (Z.of_nat n) (ord_enum n))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite !concat_app.
rewrite upd_Znth_app2.
2:{
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)); try list_solve.
rewrite sublist_one; simpl concat; list_solve.
}
f_equal.
f_equal.
apply map_ext_in.
intros.
assert (nat_of_ord a < nat_of_ord j)%nat
 by (apply in_sublist_ord_enum in H4; lia).
f_equal.
extensionality i'.
unfold matrix_upd.
rewrite mxE.
destruct (Nat.eq_dec (nat_of_ord a) _); try lia. simpl.
rewrite andb_false_r. auto.
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)); try list_solve.
rewrite sublist_one by list_solve.
simpl concat. rewrite !app_nil_r.
rewrite upd_Znth_app1 by list_solve.
f_equal.
2:{
f_equal.
apply map_ext_in.
intros.
assert (nat_of_ord j < nat_of_ord a)%nat
 by (apply in_sublist_ord_enum in H4; lia).
f_equal.
extensionality i'.
unfold matrix_upd.
rewrite mxE.
destruct (Nat.eq_dec (nat_of_ord a) _); try lia. simpl.
rewrite andb_false_r. auto.
}
replace (_ - _) with (Z.of_nat i) by nia.
replace (ord_enum m) with 
 (sublist 0 (Z.of_nat i) (ord_enum m) ++ 
  sublist (Z.of_nat i) (Z.of_nat i+1) (ord_enum m) ++ 
  sublist (Z.of_nat i+1) (Z.of_nat m) (ord_enum m))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite upd_Znth_app2 by list_solve.
autorewrite with sublist.
rewrite (sublist_one _ (Z.of_nat i + 1)); try lia.
simpl map.
unfold upd_Znth. simpl.
rewrite <- !nth_Znth'.
rewrite !nth_ord_enum.
unfold matrix_upd at 2.
rewrite mxE.
repeat (destruct (Nat.eq_dec _ _); [ | lia]).
simpl.
f_equal; [ | f_equal].
apply map_ext_in.
intros.
assert (nat_of_ord a < nat_of_ord i)%nat
 by (apply in_sublist_ord_enum in H4; lia).
unfold matrix_upd; rewrite mxE.
destruct (Nat.eq_dec _ _); [lia | ]. auto.
apply map_ext_in.
intros.
assert (nat_of_ord i < nat_of_ord a)%nat
 by (apply in_sublist_ord_enum in H4; lia).
unfold matrix_upd; rewrite mxE.
destruct (Nat.eq_dec _ _); [lia | ]. auto.
Qed.

Lemma body_densematn_get: semax_body Vprog Gprog f_densematn_get densematn_get_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
pose proof (Zlength_column_major _ _ M).
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
assert (0 <= Z.of_nat (i + j * m) < Zlength (column_major M)) by nia.
forward;
replace (Z.of_nat (nat_of_ord i) + Z.of_nat (nat_of_ord j) * Z.of_nat m)
  with (Z.of_nat (i+j * m)) by lia.
entailer!.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by lia.
rewrite Znth_column_major by lia.
rewrite H; simpl; auto.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by lia.
rewrite Znth_column_major by lia.
forward.
simpl.
entailer!!.
rewrite H; simpl; auto.
Qed.

Lemma body_densemat_get: semax_body Vprog Gprog f_densemat_get densemat_get_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*; Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, x).
forward.
entailer!!.
Qed.

Lemma body_densematn_set: semax_body Vprog Gprog f_densematn_set densematn_set_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
assert (0 <= Z.of_nat i + Z.of_nat j * Z.of_nat m < Z.of_nat m * Z.of_nat n) by nia.
change (reptype_ftype _ ?A) with A.
forward; simpl fst; simpl snd.
entailer!.
apply derives_refl'.
f_equal.
change (Vfloat x) with (@val_of_optfloat the_type (Some x)).
change (reptype_ftype _ ?A) with A.
rewrite upd_Znth_map.
f_equal.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
apply upd_Znth_column_major.
Qed.


Lemma body_densemat_set: semax_body Vprog Gprog f_densemat_set densemat_set_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, x).
entailer!!.
Qed.

Lemma body_densematn_addto: semax_body Vprog Gprog f_densematn_addto densematn_addto_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
pose proof (Zlength_column_major _ _ M).
assert (0 <= Z.of_nat i + Z.of_nat j * Z.of_nat m < Zlength (column_major M)) by nia.
change (reptype_ftype _ ?A) with A.
forward.
entailer!.
rewrite Znth_map by auto.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
rewrite Znth_column_major by lia.
rewrite H. simpl; auto.
forward.
entailer!!; simpl.
apply derives_refl'; f_equal.
change (Vfloat x) with (@val_of_optfloat Tdouble (Some x)).
change (reptype_ftype _ ?A) with A.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
rewrite Znth_map, Znth_column_major, H by (auto; lia).
simpl.
change (Vfloat ?A) with (@val_of_optfloat Tdouble (Some A)).
rewrite upd_Znth_map.
rewrite upd_Znth_column_major by lia.
auto.
Qed.


Lemma body_densemat_addto: semax_body Vprog Gprog f_densemat_addto densemat_addto_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, y, x).
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
  forall t m n (M: 'M[ftype t]_(m,n)),
  map val_of_optfloat (column_major (map_mx Some M))
  = map val_of_float (column_major M).
Proof.
intros.
unfold column_major.
rewrite !concat_map.
f_equal.
unfold mklist. rewrite !map_map.
f_equal. extensionality j. rewrite !map_map. f_equal.
extensionality i.
unfold map_mx.
rewrite mxE. reflexivity.
Qed.

Lemma body_densemat_norm2: semax_body Vprog Gprog f_densemat_norm2 densemat_norm2_spec.
Proof.
start_function.
rename X into M.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major M, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
- 
  rewrite Z.max_r by lia.
  forward; simpl.
  change (ctype_of_type the_type) with the_ctype.
  rewrite val_of_optfloat_column_major.
  change (reptype_ftype _ ?A) with A.
  entailer!!.
Qed.

Lemma body_densemat_norm: semax_body Vprog Gprog f_densemat_norm densemat_norm_spec.
Proof.
start_function.
rename X into M.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major M, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
-
  rewrite Z.max_r by lia.
  forward; simpl.
  change (ctype_of_type the_type) with the_ctype.
  change (reptype_ftype _ ?A) with A.
  rewrite val_of_optfloat_column_major.
  entailer!!.
Qed.

Lemma body_densematn_cfactor: semax_body Vprog Gprog f_densematn_cfactor densematn_cfactor_spec.
Proof.
start_function.
rename X into M.
assert_PROP (0< n <= Int.max_signed) by entailer!.
pose (A := map_mx optfloat_to_float (mirror_UT M)).
assert (Datatypes.is_true (ssrnat.leq 1 n)) by lia.
pose (zero := @Ordinal n 0 H1).
forward_for_simple_bound (Z.of_nat n) 
  (EX j':Z, EX j: 'I_(S n), EX R: 'M[ftype the_type]_n,
      PROP(j'=j; cholesky_jik_upto zero j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
- Exists (lshift1 zero) A.
  entailer!!.
  apply cholesky_jik_upto_zero; auto.
  apply derives_refl'; f_equal.
  subst A.
  clear - H.
  apply matrixP.
  intros i j. unfold joinLU. rewrite mxE.
  destruct (ssrnat.leq _ _) eqn:?H; auto.
  unfold map_mx. rewrite !mxE.
  specialize (H i j).
  unfold mirror_UT, joinLU in *.
  rewrite mxE in *. rewrite H0 in *. destruct (M i j); try contradiction. auto.  
-
rename i into j'.
Intros. subst j'.
forward_for_simple_bound (Z.of_nat j) 
  (EX i':Z, EX i: 'I_n, EX R: 'M[ftype the_type]_n,
      PROP(i' = Z.of_nat i; cholesky_jik_upto i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
 + Exists (@Ordinal n O ltac:(clear - H2; lia)) R.
   entailer!!.
 + clear H4 R.  rename R0 into R.
   Intros. subst i. rename i0 into i.
   assert (Datatypes.is_true (ssrnat.leq (S j) n)) by lia.
   pose (j' := @Ordinal n _ H4).
   assert (j = lshift1 j'). apply ord_inj. simpl. auto.
   rewrite H6 in *. clearbody j'. subst j. rename j' into j. simpl in H3.
   pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i, j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
   forward_call (X,p,sh,R i j); clear X.
   unfold joinLU, map_mx. rewrite !mxE. replace (ssrnat.leq _ _) with true by lia. auto.
(*   destruct (H5 i j') as [_ [_ [_ H8]]]. rewrite H8 in H3 by lia.*)
(*   subst vret. *) 
   forward_for_simple_bound (Z.of_nat i)
     (EX k':Z, EX k:'I_n,
      PROP(k'=Z.of_nat k; cholesky_jik_upto i (lshift1 j) A R)
      LOCAL(temp _s (val_of_float (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
    pose proof (ltn_ord i); lia.
  * Exists zero. entailer!!. f_equal. unfold subtract_loop. simpl.
    destruct (H5 i j) as [_ [_ [_ H8]]]. rewrite H8; auto.
  * Intros. subst i0.
    assert (Hi := ltn_ord i).
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(k,i)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh,R k i); clear X.
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(k,j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh,R k j); clear X.
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    forward.
    assert (Datatypes.is_true (ssrnat.leq (S (S k)) n)) by lia.
    pose (Sk := @Ordinal n _ H7).
    Exists Sk. 
    change (Vfloat
            (Float.sub (subtract_loop A R i j k)
               (Float.mul (R k i) (R k j))))
    with (val_of_float (BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)))).
    entailer!!. split. simpl; lia.
     f_equal.
     unfold subtract_loop.
     simpl ord_enum.
     rewrite ord_enum_snoc'.
     rewrite !map_app, fold_left_app.
     simpl. f_equal. f_equal. change @seq.map  with map. f_equal.
     rewrite map_map. f_equal.
     extensionality x. apply ord_inj. auto.
     f_equal. f_equal. apply ord_inj; auto. f_equal. apply ord_inj; auto.
    *
    Intros k'.
    assert (i=k')%nat by (apply ord_inj; lia). subst k'.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,i)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh,R i i); clear X.
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh, BDIV (subtract_loop A R i j i) (R i i)); clear X.
    set (rij := BDIV _ _).
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) n)) by (pose proof ltn_ord j; lia).
    pose (i1 := @Ordinal n _ H7).
    Exists i1 (matrix_upd R i j rij).
    entailer!!. split. subst i1. simpl.  lia.
    apply update_i_lt_j; auto. lia.
    apply derives_refl'. f_equal.
     apply matrixP. intros i' j'.
     unfold matrix_upd, joinLU, map_mx.
     rewrite !mxE. simpl in i',j'.
     do 2 destruct (Nat.eq_dec _ _); auto. simpl in *.
     replace (ssrnat.leq _ _) with true; auto. lia.
  + clear R H4. Intros i R.
    assert (j = lshift1 i) by (apply ord_inj; simpl; lia).
    subst j.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,i)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh,R i i); clear X.
    unfold joinLU, map_mx; rewrite !mxE; replace (ssrnat.leq _ _) with true by lia; auto.
    simpl.
   forward_for_simple_bound (Z.of_nat i)
     (EX k':Z, EX k:'I_n,
      PROP(k' = Z.of_nat k)
      LOCAL(temp _s (val_of_float (subtract_loop A R i i k) );
            temp _j (Vint (Int.repr i)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p)).
  * Exists zero. entailer!!. unfold subtract_loop. simpl.
    f_equal. destruct (H4 i i) as [_ [_ [? ?]]]. symmetry; apply H6; lia.
  * Intros. subst i0.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(k,i)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh,R k i).
    unfold joinLU, map_mx; rewrite !mxE; replace (ssrnat.leq _ _) with true by lia; auto.
    forward.
    assert (Datatypes.is_true (ssrnat.leq (S (S k)) n)) by lia.
    Exists (Ordinal H6).
    change Vfloat with (@val_of_float the_type).
    change Float.sub with (@BMINUS _ the_type).
    change Float.mul with (@BMULT _ the_type).    
    entailer!!.  split. simpl; lia. f_equal.
    apply @subtract_another; auto; lia.
  * Intros k. assert (k=i) by (apply ord_inj; lia). subst k.
    forward_call.
    replace (Binary.Bsqrt _ _ _ _ _ _) with (@BSQRT _ the_type).
2:{ (* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
 unfold BSQRT, UNOP. f_equal. extensionality x. simpl. f_equal. apply proof_irr.
   }
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,i)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X, p, sh, BSQRT (subtract_loop A R i i i)); clear X.
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) (S n))) by (lia).
    Exists (@Ordinal (S n) (S i) H6).
    Exists (matrix_upd R i i (BSQRT (subtract_loop A R i i i))).
    entailer!!. split. simpl. lia.
    apply cholesky_jik_upto_newrow; auto.   
    apply derives_refl'. f_equal.
    set (a := BSQRT _). clearbody a.
    clear.
    apply matrixP; simpl; intros i' j'.
    unfold matrix_upd, joinLU, map_mx; rewrite !mxE.
    repeat destruct (Nat.eq_dec _ _); simpl in *; auto.
    replace (ssrnat.leq _ _) with true by lia; auto.
 - Intros n' R. Exists R.
   entailer!!. fold A.
   intros i j.
   destruct (H3 i j) as [H4 _ _ _].
   apply H4.
   pose proof (ltn_ord j).  lia.
Qed.


Lemma body_densemat_cfactor: semax_body Vprog Gprog f_densemat_cfactor densemat_cfactor_spec.
Proof.
start_function.
rename X into M.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_if True; [ | contradiction | ].
forward.
entailer!!.
forward.
pose (X := existT _ n M
      : {n & 'M[option (ftype the_type)]_n}).
forward_call (sh,X,offset_val densemat_data_offset p).
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

