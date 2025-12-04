(* Copyright (C) 2025 CertiK. *)

Require Import ZArith.
Require Import List.
Require Import Shared.

Require Import ETableModel.
Require Import OpUnaryModel.

Require Import Wasm.numerics.
Require Import IntegerFunctions.
Require Import BitTableModel.
Require Import Lia.
Require RTableModel.

Require Import Moddable.

Require Import ModdableETable.
Require Import CommonModel.

#[local] Hint Resolve
  ops_bit
  bits_common
  rest_mops_common
  rest_jops_common
  input_index_common
  context_input_index_common
  context_output_index_common
  external_host_call_index_common
  sp_common
  mpages_common
  frame_id_common
  eid_common
  fid_common
  iid_common
  maximal_memory_pages_common
  operand_is_zero_bit
  is_ctz_bit
  is_clz_bit
  is_popcnt_bit
  is_i32_bit
  is64_aux1
  is64_aux2 : moddable.

#[local] Hint Resolve
  int_lt_order
  one_lt_common
  common_le_2_32
  : moddable.


Lemma one_sub_bit_bounded: forall x,
  0 <= x < 2 ->
  0 <= (1 - x) < 2.
Proof.
  lia.
Qed.

Lemma abs_bit_sub_one_bounded: forall x,
  0 <= x < 2 ->
  0 <= Z.abs (x - 1) < 2.
Proof.
  lia.
Qed.

Lemma abs_one_sub_bit_bounded: forall x,
  0 <= x < 2 ->
  0 <= Z.abs (1 - x) < 2.
Proof.
  lia.
Qed.

Lemma common_bound_u64: forall x,
  0 <= x < common ->
  0 <= x < 2^64.
Proof.
  intros.
  pose proof (common_le_2_32).
  lia.
Qed.

Lemma u128_bounded: forall x,
  0 <= x < 2^128 ->
  0 <= x < field_order.
Proof.
  intros.
  pose proof (int_lt_order).
  lia.
Qed.

Lemma u128_p_bounded: forall x y,
  0 <= x < 2^128 ->
  0 <= y < 2^128 ->
  0 <= x + y < field_order.
Proof.
  intros.
  pose proof (int_lt_order).
  lia.
Qed.

Lemma u128_pp_bounded: forall x y z,
  0 <= x < 2^128 ->
  0 <= y + z < 2^128 ->
  0 <= x + y + z < field_order.
Proof.
  intros.
  pose proof (u128_p_bounded x (y + z) H H0).
  lia.
Qed.

Lemma u128_ppp_bounded: forall x y z w,
  0 <= x < 2^128 ->
  0 <= y + z + w < 2^128 ->
  0 <= x + y + z + w < field_order.
Proof.
  intros.
  pose proof (u128_p_bounded x (y + z + w) H H0).
  lia.
Qed.

Lemma u128_ppu_bounded: forall x y z w,
  0 <= x + y + z < 2^128 ->
  0 <= w < 2^128 ->
  0 <= x + y + z + w < field_order.
Proof.
  intros.
  pose proof (u128_p_bounded (x + y + z) w H H0).
  lia.
Qed.

Lemma u64_p_bounded: forall x y,
  0 <= x < 2^64 ->
  0 <= y < 2^64 ->
  0 <= x + y < 2^128.
Proof.
  lia.
Qed.

Lemma abs_sub_bound: forall x y b,
  0 <= x < b ->
  0 <= y < b ->
  0 <= Z.abs (x - y) < b.
Proof.
  lia.
Qed.


#[local] Hint Resolve
  one_sub_bit_bounded
  abs_bit_sub_one_bounded
  abs_one_sub_bit_bounded
  common_bound_u64
  u128_p_bounded
  u128_pp_bounded
  u128_ppp_bounded
  u128_ppu_bounded
  u64_p_bounded
  abs_sub_bound 
  : moddable.


Lemma etable_ops_cell_isbit : forall cls i,
  0 <= etable_values (ops_cell cls) i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_ops_cell_is_ctz_isbit: forall i,
  0 <= etable_values is_ctz i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_ops_cell_is_clz_isbit: forall i,
  0 <= etable_values is_clz i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_ops_cell_is_popcnt_isbit: forall i,
  0 <= etable_values op_unary_is_popcnt i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_ops_cell_is_i32_isbit: forall i,
  0 <= etable_values is_i32 i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_bits_is_common: forall i,
  0 <= etable_values bits i < common.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_operand_is_zero_isbit: forall i,
  0 <= etable_values operand_is_zero i < 2.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_aux1_is64: forall i,
  is64 aux1 ->
  0 <= etable_values aux1 i < 2^64.
Proof.
  eauto 12 with moddable.
Qed.

Lemma etable_aux2_is64: forall i,
  is64 aux2 ->
  0 <= etable_values aux2 i < 2^64.
Proof.
  eauto 12 with moddable.
Qed.

(* In the full development this is proven in BitTable.v *)
Lemma etable_allocated_bit_table_lookup_cells_u64: forall i cell,
  0 <= i ->
  0 <= etable_values (bit_table_lookup_cells cell) i < 2^64.
Proof.
Admitted.

#[local] Hint Resolve
  etable_ops_cell_isbit
  etable_ops_cell_is_ctz_isbit
  etable_ops_cell_is_clz_isbit
  etable_ops_cell_is_popcnt_isbit
  etable_ops_cell_is_i32_isbit
  etable_bits_is_common
  etable_operand_is_zero_isbit
  etable_aux1_is64
  etable_aux2_is64
  etable_allocated_bit_table_lookup_cells_u64
  : moddable.

Program Definition operand_is_common := 
  alloc_memory_table_lookup_read_cell_with_value_U64 stack_read.

Program Definition result_is_common := 
  alloc_memory_table_lookup_write_cell_with_value_U64 stack_write.

#[local] Hint Resolve 
  operand_is_common
  result_is_common
  : moddable.

Program Definition op_unary_selector :=  pgate_to_gate  _ p_op_unary_selector.
Next Obligation.
  replace (n + 0) with n in * by lia.
  split; auto.
  apply moddable_mul.
  - eauto 12 with moddable.
  - eauto 20 with moddable.
Qed.

(* only the first half of this gate is amenable to moddable. *)
Lemma p_op_unary_zero_cond' :
  pgate etable
    (fun get =>
      (get (ops_cell Unary) 0) * (get operand_is_zero 0) * (get operand 0)
                                                             ::nil).
Proof.
  assert (H:= p_op_unary_zero_cond).
  unfold pgate, ForallP in *.
  firstorder.
Qed.

Program Definition op_unary_zero_cond :=  pgate_to_gate  _ p_op_unary_zero_cond'.
Next Obligation.
  replace (n + 0) with n in * by lia.
  repeat (split; auto).
  - apply moddable_mul; eauto 12 with moddable.
Qed.

(* Diable unfold 32%Z * _ ; ONLY FOR READING. CAN BE REMOVED *)
Opaque Z.mul.
Arguments Z.mul : simpl never.

Program Definition op_unary_bits_gate :=  pgate_to_gate  _ p_op_unary_bits_gate.
Next Obligation.
  replace (n + 0) with n in * by lia.
  split; auto.
  apply moddable_mul.
  - eauto 12 with moddable.
  - eauto 12 with moddable.
Qed.

(* Diable unfold 32%Z - _ *)
Opaque Z.sub.
Arguments Z.sub : simpl never.

Lemma lookup_pow_power_bounded : forall x,
  0 <= x ->
  0 <= etable_values lookup_pow_power x < 256.
Proof.
  intros.
  assert (Hin := ETableModel.c8d x H).
  destruct (Z.eq_dec (etable_values lookup_pow_power x) 0) as [Hzero | Hnonzero].
  - rewrite Hzero.
    lia.
  - apply RTableModel.in_op_table_power in Hin; auto.
    lia.
Qed.

Lemma lookup_pow_power_lose_bounded : forall x,
  0 <= x ->
  0 <= etable_values lookup_pow_power x < 2^64.
Proof.
  intros.
  pose proof (lookup_pow_power_bounded x H) as Hm.
  lia.
Qed.

Lemma lookup_pow_modulus_bounded : forall n,
  0 <= n ->
  0 <= etable_values lookup_pow_modulus n < 2^128.
Proof.
  intros.
  assert (Hin := ETableModel.c8d n H).
  destruct (Z.eq_dec (etable_values lookup_pow_modulus n) 0) as [Hzero | Hnonzero].
  - rewrite Hzero. lia.
  - apply RTableModel.in_op_table_power in Hin; auto.
    destruct Hin as [Hp Hm].
    assert (0 <= etable_values lookup_pow_power n - 128 < 128) as Hp' by lia.
    rewrite Hm.
    pose proof (Z.pow_lt_mono_r 2 (etable_values lookup_pow_power n - 128) 128).
    lia.
Qed.

#[local] Hint Resolve
  lookup_pow_power_bounded
  lookup_pow_power_lose_bounded
  lookup_pow_modulus_bounded
  : moddable.

Program Definition op_unary_clz :=  pgate_to_gate  _ p_op_unary_clz.
Next Obligation.
  replace (n + 0) with n in * by lia.
  split; auto.
  - apply moddable_mul.
    +  apply moddable_mul.
       apply moddable_mul.
       apply moddable_absbounded.
       eauto 12 with moddable.
       eauto 12 with moddable.
    + eauto 12 with moddable.
      eauto 12 with moddable.
  - split.
    apply moddable_mul.
    + apply moddable_mul.
      apply moddable_absbounded.
      apply one_bit_bounded.
      eauto 20 with moddable.
      eauto 20 with moddable.
      
    +
     (* lookup_pow_modulus +  aux1 - operand
                      2^128    2^64      2^64
      *)
      apply moddable_absbounded.
      apply absbound_ppm.
      apply u128_pp_bounded.
      * eauto 12 with moddable.
      * eauto 12 with moddable.
  - split.
    apply moddable_mul.
    +
      apply moddable_mul.
      apply moddable_mul.


      eauto 12 with moddable.
      eauto 12 with moddable.
      eauto 12 with moddable.
    + (* aux1 + aux2 + 1 - lookup_pow_modulus
         2^64   2^64   1                2^128
      *)
      apply moddable_absbounded.
      eauto 20 with moddable.
  - split; auto.
    apply moddable_mul.
    + apply moddable_mul; [|eauto 12 with moddable].
      apply moddable_mul; eauto 12 with moddable.
    + (* lookup_pow_power -   bits - result - 1 + 128
                      128   common     2^64.  1.  128
      *)
      apply moddable_absbounded.
      replace (etable_values lookup_pow_power n -
                (etable_values bits n - etable_values result n - 1 + 128))
      with (etable_values lookup_pow_power n -
              etable_values bits n + etable_values result n - 127) by lia.
      eauto 20 with moddable.
Qed.
