(* Copyright (C) 2025 CertiK. *)

Require Import Wasm.numerics.

Require Import ZArith.
Require Import List.
Require Import Lia.

Require Import Shared.
Require Import CommonModel.
Require Import ImageTableModel.
Require Import MTableModel.

Require Import Moddable.

Open Scope Z_scope.

(* Proofs about pgate->gate. *)

Lemma mtable_isbit_bounded : forall c i,
    isbit c ->
      0 <= (mtable_values c i) < 2.
Proof.
  intros c i Hbit.
  unfold isbit in Hbit.
  pose proof (Hbit i) as [H | H]; rewrite H; simpl; lia.
Qed.

Lemma mtable_isbit_bounded_neg : forall c i,
    isbit c ->
      0 <= Z.abs (mtable_values c i - 1) < 2.
Proof.
  intros c i Hbit.
  unfold isbit in Hbit.
  pose proof (Hbit i) as [H | H]; rewrite H; simpl; lia.
Qed.

Lemma mtable_iscommon_common : forall c i,
    iscommon c ->
      0 <= Z.abs (mtable_values c i) < common.
Proof.
  intros c i Hbit.
  unfold iscommon in Hbit.
  pose proof (Hbit i).
  rewrite Z.abs_eq; lia.
Qed.

Lemma mtable_is16_u16 : forall c i,
    is16 c ->
      0 <= Z.abs (mtable_values c i) < 2^16.
Proof.
  intros c i Hbit.
  unfold iscommon in Hbit.
  pose proof (Hbit i).
  rewrite Z.abs_eq; lia.
Qed.

#[local] Hint Resolve   mtable_isbit_bounded  mtable_isbit_bounded_neg  mtable_iscommon_common mtable_is16_u16

  enabled_bit is_global_bit is_heap_bit is_stack_bit is_next_same_ltype_bit is_next_same_offset_bit is_mutable_bit is_i32_bit is_i64_bit is_init_bit
  start_eid_common end_eid_common eid_diff_common rest_mops_common offset_align_left_common offset_align_right_common offset_align_left_diff_common offset_align_right_diff_common offset_common offset_diff_common

value_U64 value_u16_cells_le0_U16 value_u16_cells_le1_U16 value_u16_cells_le2_U16 value_u16_cells_le3_U16 encode_cell_unlimited init_encode_cell_unlimited
  
  :moddable.

Program Definition gate_mc1 := pgate_to_gate _ pgate_mc1.
Next Obligation.
  eauto 12 with moddable.
Qed.

Program Definition gate_mc2 := pgate_to_gate _ pgate_mc2.
Next Obligation.
  split; auto.
  eauto 25 with moddable.
Qed.

Program Definition gate_mc3 := pgate_to_gate _ pgate_mc3.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 15 with moddable.
Qed.

Program Definition gate_mc4a := pgate_to_gate _ pgate_mc4a.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

(* One of the four equations in the gate uses the "inverse element" idiom. *)
(*
Program Definition gate_mc4b := pgate_to_gate _ pgate_mc4b.
Next Obligation.
*)

Program Definition gate_mc5 := pgate_to_gate _ pgate_mc5.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

Program Definition gate_mc6 := pgate_to_gate _ pgate_mc6.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Program Definition gate_mc7 := pgate_to_gate _ pgate_mc7.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.
  
Program Definition gate_mc7b := pgate_to_gate _ pgate_mc7b.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

Lemma encode_init_memory_table_entry_bounded : forall l m s e v,
    0 <= encode_init_memory_table_entry l m s e v < field_order.
Proof.
  intros.
  eauto using Z.mod_pos_bound, field_order_positive.
Qed.
    
Program Definition gate_mc7c := pgate_to_gate _ pgate_mc7c.
Next Obligation.
  split; auto.
  - eauto 25 using encode_init_memory_table_entry_bounded with moddable.
Qed.

Program Definition gate_mc8 := pgate_to_gate _ pgate_mc8.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Lemma gate_mc9_helper : forall x y z w,
    0 <= x < 2^16 ->
    0 <= y < 2^16 ->
    0 <= z < 2^16 ->
    0 <= w < 2^16 ->    
    0 <= x + y * 65536 + z * 4294967296 + w * 281474976710656 < field_order.
Proof. intros. pose field_order_big. lia. Qed.

Program Definition gate_mc9 := pgate_to_gate _ pgate_mc9.
Next Obligation.
  repeat (split; auto).
  - eauto 25 using gate_mc9_helper with moddable.
Qed.

Program Definition gate_mc10b := pgate_to_gate _ pgate_mc10b.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Program Definition gate_mc10c := pgate_to_gate _ pgate_mc10c.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.


Program Definition gate_mc11 := pgate_to_gate _ pgate_mc11.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Opaque Z.sub.

Lemma encode_memory_table_entry_bounded : forall x y z,
    0 <= encode_memory_table_entry x y z < field_order.
Proof.
  intros.
  eauto using Z.mod_pos_bound, field_order_positive.
Qed.

Program Definition gate_mc12 := pgate_to_gate _ pgate_mc12.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 using encode_memory_table_entry_bounded with moddable.
Qed.

Transparent Z.sub.
