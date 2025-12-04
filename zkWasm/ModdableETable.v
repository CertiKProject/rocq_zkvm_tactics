(* Copyright (C) 2025 CertiK. *)

Require Import ZArith.
Require Import Wasm.numerics.
Require Import Shared.
Require Import CommonModel.
Require Import ImageTableModel.
Require Import ETableModel.
Require Import Moddable.


Require Import Lia.

Open Scope Z_scope.

Lemma etable_isunlimited_unlimited : forall c i,
    isunlimited c ->
      0 <=  (etable_values c i) < field_order.
Proof.
  intros c i Hc.
  unfold isunlimited in Hc.
  pose proof (Hc i) as Hrange.
  lia.
Qed.

Lemma etable_isbit_bounded : forall c i,
    isbit c ->
      0 <= etable_values c i < 2.
Proof.
  intros c i Hbit.
  unfold isbit in Hbit.
  pose proof (Hbit i) as [H | H]; rewrite H; simpl; lia.
Qed.

Lemma etable_iscommon_common : forall c i,
    iscommon c ->
      0 <=  (etable_values c i) < common.
Proof.
  intros c i Hbit.
  unfold iscommon in Hbit.
  pose proof (Hbit i).
  lia.
Qed.

Lemma etable_is16_u16 : forall c i,
    is16 c ->
      0 <= (etable_values c i) < 2^16.
Proof.
  intros c i Hbit.
  unfold iscommon in Hbit.
  pose proof (Hbit i).
  lia.
Qed.

Lemma etable_is8_u8 : forall c i,
    is8 c ->
    0 <= Z.abs (etable_values c i) < 2^8.
Proof.
  intros c i H.
  unfold is8 in *.
  pose proof (H i).
  apply bounded_absbounded.
  lia.
Qed.

Lemma etable_isbit_bounded_neg : forall c i,
    isbit c ->
    0 <= Z.abs (etable_values c i - 1) < 2.
Proof.
  intros c i Hbit.
  pose (etable_isbit_bounded c i Hbit).
  lia.
Qed.

Lemma moddable_neg_bit : forall c i,
    isbit c ->
    moddable (1- etable_values c i).
Proof.
  intros.
  apply moddable_absbounded.
  pose field_order_big.
  destruct (H i) as [H1 | H1]; rewrite H1; simpl; lia.
Qed.
#[global] Hint Resolve moddable_neg_bit : moddable.


Lemma etable_is64_u64 : forall c i,
    is64 c ->
    0 <= (etable_values c i) < 2^64.
Proof.
  intros c i H.
  unfold is64 in *.
  change ( Wasm_int.Int64.modulus) with (2^64) in *.
  pose proof (H i).
  lia.
Qed.

#[global] Hint Resolve etable_is64_u64 : moddable.


Lemma etable_is64_from16_u64 : forall c c1 c2 c3 c4 i,
    is64_from16 c c1 c2 c3 c4 ->
    0 <= (etable_values c i) < 2^64.
Proof.
  intros c  c1 c2 c3 c4 i H.
  unfold is64_from16 in H.
  specialize (H i).
  tauto.
Qed.
#[global] Hint Resolve  etable_is64_from16_u64 : moddable. 

#[global] Hint Resolve
  etable_isunlimited_unlimited
  etable_isbit_bounded
  etable_iscommon_common
  etable_is16_u16
  enabled_bit
  : moddable.

(* #[export] Hint Resolve  etable_isbit_bounded  etable_isbit_bounded_neg  etable_iscommon_common etable_is16_u16 etable_is64_u64  etable_isunlimited_unlimited.
 : moddable. *)

#[export] Hint Resolve
enabled_bit ops_bit rest_mops_common rest_jops_common input_index_common context_input_index_common context_output_index_common external_host_call_index_common sp_common mpages_common frame_id_common eid_common fid_common iid_common maximal_memory_pages_common op_br_if_eqz_cond_is_zero_cell_bit op_br_if_eqz_keep_cell_bit op_br_if_cond_is_not_zero_cell_bit op_br_if_keep_cell_bit op_br_keep_cell_bit op_br_table_keep_bit op_return_keep_cell_bit op_store_is_cross_block_bit
: moddable.

Axiom alloc_memory_table_lookup_read_cell_with_value_U64 :
  forall {c eid location_type offset is_i32 enabled} ,
    alloc_memory_table_lookup_read_cell_with_value c eid location_type offset is_i32 enabled
    ->
      forall i,
        0 <= Z.abs (etable_values (c AMTLRC_value_cell) i) < 2^64.

Axiom alloc_memory_table_lookup_read_cell_U64 :
  forall {c eid location_type offset is_i32 value enabled} ,
    alloc_memory_table_lookup_read_cell c eid location_type offset is_i32 value enabled
    ->
      forall i,
        0 <= Z.abs (etable_values (c AMTLRC_value_cell) i) < 2^64.

Axiom alloc_memory_table_lookup_write_cell_with_value_U64 :
  forall {c eid location_type offset is_i32 enabled} ,
    alloc_memory_table_lookup_write_cell_with_value c eid location_type offset is_i32 enabled
    ->
      forall i,
        0 <= etable_values (c AMTLWC_value_cell) i < 2^64.

Axiom alloc_memory_table_lookup_write_cell_U64 :
  forall {c eid location_type offset is_i32 value enabled} ,
    alloc_memory_table_lookup_write_cell c eid location_type offset is_i32 value enabled
    ->
      forall i,
        0 <=  (etable_values (c AMTLWC_value_cell) i) < 2^64.
