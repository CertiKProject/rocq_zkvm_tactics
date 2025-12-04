(* Copyright (C) 2025 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.
Require Import ETableModel.
Require MTableModel.

Require Import Moddable.
Require Import ModdableETable.

Require Import OpBinShiftModel.


#[local] Hint Resolve rhs_modulus_unlimited size_modulus_unlimited res_unlimited pad_unlimited lookup_pow_power_unlimited degree_helper_unlimited : moddable.

#[local] Hint Resolve 
 is_i32_bit lhs_flag_bit_cell_bit is_shl_bit is_shr_u_bit is_shr_s_bit is_rotl_bit is_rotr_bit is_l_bit is_r_bit : moddable.

#[local] Hint Resolve lhs_flag_u16_rem_cell_common lhs_flag_u16_rem_diff_cell_common rhs_round_common rhs_rem_common rhs_rem_diff_common : moddable.


Lemma lhs_u16_cells_U16_0 : is16 lhs_u16_cells_le_0.
Proof. pose lhs_u16_cells_U16. tauto. Qed.
Lemma lhs_u16_cells_U16_1 : is16 lhs_u16_cells_le_1.
Proof. pose lhs_u16_cells_U16. tauto. Qed.
Lemma lhs_u16_cells_U16_2 : is16 lhs_u16_cells_le_2.
Proof. pose lhs_u16_cells_U16. tauto. Qed.
Lemma lhs_u16_cells_U16_3 : is16 lhs_u16_cells_le_3.
Proof. pose lhs_u16_cells_U16. tauto. Qed.

Lemma rhs_u16_cells_U16_0 : is16 rhs_u16_cells_le_0.
Proof. pose rhs_u16_cells_U16. tauto. Qed.
Lemma rhs_u16_cells_U16_1 : is16 rhs_u16_cells_le_1.
Proof. pose rhs_u16_cells_U16. tauto. Qed.
Lemma rhs_u16_cells_U16_2 : is16 rhs_u16_cells_le_2.
Proof. pose rhs_u16_cells_U16. tauto. Qed.
Lemma rhs_u16_cells_U16_3 : is16 rhs_u16_cells_le_3.
Proof. pose rhs_u16_cells_U16. tauto. Qed.

#[local] Hint Resolve lhs_u16_cells_U16_0 lhs_u16_cells_U16_1 lhs_u16_cells_U16_2 lhs_u16_cells_U16_3
 rhs_u16_cells_U16_0 rhs_u16_cells_U16_1 rhs_u16_cells_U16_2 rhs_u16_cells_U16_3 lhs_U64 rhs_U64  : moddable.
  
#[local] Hint Resolve round_U64 rem_U64 diff_U64 : moddable.


Lemma lhs_flag_bit_dyn_helper : forall bit x y z u v,
    0 <= bit < 2 ->
    0 <= x < 2^16 ->
    0 <= y < common ->
    0 <= z < 2^16 ->
    0 <= u < 2^16 ->
    0 <= v < 2^16 ->    
    0 <= Z.abs (x + y - (z + bit * (u - v))) < field_order.
Proof.
  intros.
  assert (e1 := Z.abs_triangle (x+y) (z + bit * (u - v))).
  assert (e2 := Z.abs_triangle x y).
  assert (e3 := Z.abs_triangle z (bit * (u - v))).
  assert (Z.abs (bit * (u - v)) <= Z.abs u + Z.abs v).
  {
    assert (e4 := Z.abs_sub_triangle u v ).
    destruct (Z.eq_dec bit 0).
    - subst. lia.
    - replace bit with 1 by lia. lia.
  }
  pose field_order_big. pose common_small. lia.
Qed.
  
Program Definition lhs_flag_bit_dyn :=  pgate_to_gate  _  p_lhs_flag_bit_dyn.
Next Obligation.
  repeat (split; auto).
  - apply moddable_absbounded.
    apply lhs_flag_bit_dyn_helper;
     eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Program Definition bin_shift_op_select :=  pgate_to_gate  _  p_bin_shift_op_select.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Lemma two_U64_1_bounded : forall x y,
    0 <= x < 2^64 + 1 ->
    0 <= y < 2^64 + 1 ->
    0 <= x+y < field_order.
Proof. pose field_order_big. lia. Qed.

(* this is  (Z.shiftl 1 64) *)
Lemma const_18446744073709551616_U64_1 : 
  0 <= Z.abs 18446744073709551616 <  2^64 + 1.
Proof. rewrite Z.abs_eq; lia. Qed.

       
(* this is 0xFFFFFFFF *)
Lemma const_1844674406941458432_U64_1 : 
  0 <= Z.abs 1844674406941458432 <  2^64 + 1.
Proof. rewrite Z.abs_eq; lia. Qed.

#[local] Hint Resolve  two_U64_1_bounded  const_18446744073709551616_U64_1 const_1844674406941458432_U64_1 : moddable.


Lemma bin_shift_modulus_helper : forall c n,
   isbit c ->
   0 <= 64 - etable_values c n * 32 < field_order.
Proof.
  intros c n Hbit.
  pose field_order_big.
  destruct (Hbit n) as [H|H]; rewrite H; try lia.
Qed.

Lemma bin_shift_modulus_helper' : forall c n,
   isbit c ->
   0 <= 18446744073709551616 - etable_values c n * 18446744069414584320 < field_order.
Proof.
  intros c n Hbit.
  pose field_order_big.
  destruct (Hbit n) as [H|H]; rewrite H; try lia.
Qed.

Program Definition bin_shift_modulus :=  pgate_to_gate  _  p_bin_shift_modulus.
Next Obligation.
  repeat (split; auto).
  - apply moddable_mul. 
    eauto 25 with moddable.
    replace (etable_values rhs_modulus (n + 0) - 64 + etable_values is_i32 (n + 0) * 32) with
    (etable_values rhs_modulus (n + 0) - (64 - etable_values is_i32 (n + 0) * 32))
    by lia.
    apply moddable_sub.
    eauto 25 with moddable.
    eauto using bin_shift_modulus_helper with moddable.
  -  apply moddable_mul.
     + eauto 25 with moddable.
     + replace (  (etable_values size_modulus (n + 0) - 18446744073709551616 +
                   etable_values is_i32 (n + 0) * 18446744069414584320))
       with (  (etable_values size_modulus (n + 0) - (18446744073709551616 -
     etable_values is_i32 (n + 0) * 18446744069414584320))) by lia.
     apply moddable_sub.
     eauto 25 with moddable.
    eauto using bin_shift_modulus_helper' with moddable.
Qed.

Lemma size_modulus_bound : forall n,
    0 <= n ->
    etable_values (ops_cell BinShift) n <> 0 ->
    0 <= etable_values size_modulus n < 2^64+1.
Proof.
  change (2^64+1) with 18446744073709551617.
  intros n Hrange Hops.
  destruct (bin_shift_modulus n Hrange) as [_ [Hgate _]].
  simpl in Hgate.
  replace (n+0) with n in * by lia.
  apply Zmult_integral in Hgate.
  destruct Hgate; [congruence |].  
  destruct (is_i32_bit n) as [Hbit | Hbit]; rewrite Hbit in *; lia.
Qed.

Lemma rhs_modulus_bound : forall n,
    0 <= n ->
    etable_values (ops_cell BinShift) n <> 0 ->
    0 <= etable_values rhs_modulus n < 2^64+1.
Proof.
  change (2^64+1) with 18446744073709551617.
  intros n Hrange Hops.
  destruct (bin_shift_modulus n Hrange) as [Hgate _].
  simpl in Hgate.
  replace (n+0) with n in * by lia.
  apply Zmult_integral in Hgate.
  destruct Hgate; [congruence |].  
  destruct (is_i32_bit n) as [Hbit | Hbit]; rewrite Hbit in *; lia.
Qed.

(* These two lemmas are proven in the full zkWasm development. *)
Lemma lookup_pow_power_bounded : forall x,
  0 <= x ->
  0 <= etable_values lookup_pow_power x < 256.
Admitted.
Lemma lookup_pow_modulus_bounded' : forall x,
  0 <= x ->
  1 <= etable_values lookup_pow_modulus x < 2^128.
Admitted.

(* This one is also needed for OpStore, move it to some common place. *)
Lemma lookup_pow_modulus_bounded : forall x,
  0 <= x ->
  0 <= etable_values lookup_pow_modulus x < 2^128.
Proof.
  intros.
  pose (lookup_pow_modulus_bounded' x). lia.
Qed.  

#[global] Hint Resolve lookup_pow_power_bounded lookup_pow_modulus_bounded : moddable.

(* This is pretty special-purpose *)
Lemma common_mul_u64_bounded : forall x y,
    0 <= x < common ->
    0 <=  y < 2^64+1 ->
    0 <= (x*y) < field_order.
Proof.
  intros.
  pose field_order_big. pose common_small. 
  assert (x*y <= 2^32*(2^64+1)) by (apply Zmult_le_compat; lia).
  lia.
Qed.
  
#[local] Hint Resolve common_mul_u64_bounded : moddable. 

(* This gate uses multiple unlimited numbers in a subtle way.
Program Definition bin_shift_rhs_rem :=  pgate_to_gate  _  p_bin_shift_rhs_rem.
*)

Program Definition bin_shift_modulus_pow_lookup :=  pgate_to_gate  _  p_bin_shift_modulus_pow_lookup.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

Program Definition bin_shift_modulus_is_r :=  pgate_to_gate  _  p_bin_shift_is_r.
Next Obligation.
  replace (n+0) with n in * by lia.
  pose (lookup_pow_modulus_bounded n H).      
  repeat (split; auto).
  -    apply moddable_mul.
       +     eauto 25 with moddable.
       + apply moddable_absbounded.
         apply absbound_ppm.
         apply u64_plus_u192_plus_u64_bounded;
           eauto 25  with moddable.
  - eauto 25 with moddable.
Qed.

Program Definition bin_shift_shr_u :=  pgate_to_gate  _  p_bin_shift_shr_u.
Next Obligation.
  repeat (split; auto).
  -  eauto 25 with moddable.
Qed.

Lemma u128_mul_u64_1: forall x y,
    0 <= x < 2^128 ->
    0 <= y < 2^64+1 ->
    0 <= (x*y) < field_order.
Proof.
  intros.
  pose field_order_big. 
  assert (x*y <= 2^128*(2^64+1)) by (apply Zmult_le_compat; lia).
  lia.
Qed.

Lemma bin_shift_shr_s_helper : forall x y,
      0 <= x < 2^65 ->
      0 <= y < 2^128 ->
      0 <= x*y < field_order.
Proof.
  intros.
  pose field_order_big. 
  assert (x*y <= (2^65)*(2^128)) by (apply Zmult_le_compat; lia).
  lia.
Qed.

(* This gate uses multiple unlimited numbers in a subtle way. 
Program Definition bin_shift_shr_s :=  pgate_to_gate  _  p_bin_shift_shr_s.
 *)

(* Some very special purpose lemma... *)
Lemma bin_shift_is_rotr_helper : forall x y z w ,
    0 <= x <  2^64 ->
    0 <= y <  2^128 ->
    0 <= z <  2^64 ->
    0 <= w < 2^64+1 ->
    0 <= (x*y) + (z*w) < field_order.
Proof.
  intros.
  assert (x*y <= (2^64)*(2^128)) by (apply Zmult_le_compat; lia).
  assert (z*w <= (2^64)*(2^64+1)) by (apply Zmult_le_compat; lia).
  pose field_order_big. 
  lia.
Qed.

Program Definition bin_shift_is_rotr :=  pgate_to_gate  _  p_bin_shift_is_rotr.
Next Obligation.  
  repeat (split; auto).
  - replace (n+0) with n by lia.    
    apply moddable_mul'.
    eauto 25 with moddable.
    intros Hops.
    apply moddable_pmm.
    + apply  u192_bounded, u64_mul_u128_u192.
      pose (alloc_memory_table_lookup_write_cell_with_value_U64 stack_write).
      eauto.
      eauto 25 with moddable.
    + rewrite <- Z.neq_mul_0 in Hops.
      destruct Hops as [Hops _].
      pose (size_modulus_bound n H Hops).
      pose (lookup_pow_modulus_bounded' n H).
      apply bin_shift_is_rotr_helper;
        eauto with moddable.
Qed.

(* Some very special purpose lemma... *)
Lemma bin_shift_is_l_helper : forall x y z ,
    0 <= x <  2^64 ->
    0 <= y <  2^64+1 ->
    0 <= z <  2^64 ->
    0 <= x*y + z < field_order.
Proof.
  intros.
  assert (x*y <= (2^64)*(2^64+1)) by (apply Zmult_le_compat; lia).
  pose field_order_big. 
  lia.
Qed.

Program Definition bin_shift_is_l  := pgate_to_gate _ p_bin_shift_is_l.
Next Obligation.
  repeat (split; auto).
  - replace (n+0) with n in * by lia.
    pose (lookup_pow_modulus_bounded n H).
    apply moddable_mul'.
     eauto 25 with moddable.
     intros Hops.
     apply moddable_pmm.
    + eauto 25 with moddable.
    + rewrite <- Z.neq_mul_0 in Hops.
      destruct Hops as [Hops _].
      pose (size_modulus_bound n H Hops). 
      apply bin_shift_is_l_helper;
        eauto 25 with moddable.
  -  eauto 25 with moddable.
Qed.

Program Definition bin_shift_shl :=  pgate_to_gate  _  p_bin_shift_shl.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

Program Definition bin_shift_rotl :=  pgate_to_gate  _  p_bin_shift_rotl.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.
