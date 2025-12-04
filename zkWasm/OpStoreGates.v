(* Copyright (C) 2025 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Moddable.
Require Import ModdableETable.

Require Import Shared.
Require Import ETableModel.
Require MTableModel.
Require RTableModel.

Require Import OpStoreModel.

#[global] Hint Resolve etable_isunlimited_unlimited : moddable.

#[local] Hint Resolve
unchanged_value_unlimited 
len_unlimited
len_modulus_unlimited
lookup_pow_modulus_unlimited
lookup_pow_power_unlimited
load_block_inner_pos_unlimited
store_base_unlimited
store_value_in_heap1_unlimited
store_value_in_heap2_unlimited
load_value_in_heap1_unlimited
load_value_in_heap2_unlimited
store_value_wrapped_unlimited
opcode_store_offset_common 
load_block_index_common 
cross_block_rem_common
cross_block_rem_diff_common
address_within_allocated_pages_helper_common
load_block_inner_pos_bits_0_bit 
load_block_inner_pos_bits_1_bit 
load_block_inner_pos_bits_2_bit 
is_cross_block_bit 
is_one_byte_bit
is_two_bytes_bit
is_four_bytes_bit
is_eight_bytes_bit
is_i32_bit
load_picked_byte_proof_U8 
store_value_tailing_u16_u8_high_U8 
store_value_tailing_u16_u8_low_U8 
load_picked_u16_cells_le_0_U16 
load_picked_u16_cells_le_1_U16 
load_picked_u16_cells_le_2_U16 
load_picked_u16_cells_le_3_U16 
store_value_u16_cells_le_0_U16 
store_value_u16_cells_le_1_U16 
store_value_u16_cells_le_2_U16 
store_value_u16_cells_le_3_U16 
load_tailing_U64
load_tailing_diff_U64
load_leading_U64
  : moddable.

#[local] Hint Resolve load_picked_U64 store_value_U64 : moddable.

(* Some ad-hoc lemmas for  OpStore in particular. *)

Lemma shifted_bits_bounded : forall x y z w,
   0 <= Z.abs x < 2 ->
   0 <= Z.abs y < 2 ->
   0 <= Z.abs z < 2 ->
   0 <= Z.abs w < 2  ->
   0 <= Z.abs (x * 256) + Z.abs (y * 65536)  + Z.abs (z*4294967296) + Z.abs (w*18446744073709551616) < field_order.
Proof.
  intros.
  rewrite !Z.abs_mul. simpl.
  pose field_order_big.
  lia.
Qed.

Lemma common_mul_BLOCK_SIZE_U64: forall x,
    0 <= Z.abs x < common ->
    0 <= Z.abs (x * WASM_BLOCK_BYTE_SIZE) < 2^64.
Proof.
  change (2^64) with 18446744073709551616.
  unfold WASM_BLOCK_BYTE_SIZE.
  pose field_order_big.
  pose common_small.
  lia.
Qed.
#[local] Hint Resolve  shifted_bits_bounded  : moddable.

Program Definition op_store_length  :=  pgate_to_gate  _ p_op_store_length.
Next Obligation.
  split; auto.
  eauto 25 with moddable.
Qed.

(* In the full development this lemma is proved in OpStore.v *)
Lemma load_one_number_of_bytes : forall i,
    0 <= i ->
    etable_values (ops_cell Store) i = 1 ->
    (etable_values is_one_byte i = 1 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 1 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 1 /\ etable_values is_eight_bytes i = 0)
 \/ (etable_values is_one_byte i = 0 /\ etable_values is_two_bytes i = 0 /\ etable_values is_four_bytes i = 0 /\ etable_values is_eight_bytes i = 1).
Admitted. 
  
Program Definition op_store_len_gate :=  pgate_to_gate  _ p_op_store_len_gate.
Next Obligation.
  split; auto.
  eauto 25 with moddable.
Qed.


#[global] Hint Resolve u8_u64 etable_is8_u8 two_u64_bounded three_u64_bounded :moddable.

(* This gate has a single unlimited number but is not easily provable because it contains a subtraction.
Program Definition op_store_load_block_index_gate :=  pgate_to_gate  _ p_op_store_load_block_index_gate.
*)

Lemma inner_pos_bounded : forall n,
    0<=n ->
    etable_values (ops_cell Store) n <> 0 ->
    0 <= etable_values load_block_inner_pos n < 8.
Proof.
  intros n Hrange Hops.
  destruct (op_store_load_block_index_gate n Hrange) as [_ [Hgate _]].
  replace (n+0) with n in * by lia.
  simpl in Hgate.
   apply Zmult_integral in Hgate.
   destruct Hgate; [congruence|].
   destruct (load_block_inner_pos_bits_0_bit n);
   destruct (load_block_inner_pos_bits_1_bit n);
   destruct (load_block_inner_pos_bits_2_bit n); lia.
Qed.

Lemma  op_store_pow_lookup_helper : forall x,
   0 <= x < 8 ->
   0 <= (x * 8 + 128) < field_order.
Proof.
  pose field_order_big. lia.
Qed.
  
Program Definition op_store_pow_lookup :=  pgate_to_gate  _  p_op_store_pow_lookup.
Next Obligation.
  repeat (split; auto).
  - apply moddable_mul'.
    eauto 25 with moddable.
    intros Hops.
    replace (n+0) with n in * by lia.
    assert (Hpos:= inner_pos_bounded n H Hops).
    eauto 25 with moddable.
    apply moddable_pm.
    eauto 25 with moddable.
    apply op_store_pow_lookup_helper; eauto. 
Qed.

Lemma lookup_pow_values : forall i,
    0 <= i ->
    etable_values lookup_pow_power i <> 0 ->    
    128 <= etable_values lookup_pow_power i < 256 /\
    etable_values lookup_pow_modulus i = 2^(etable_values lookup_pow_power i - 128).
Proof.
  intros i Hrange Hnonzero.
  assert (Hin:=ETableModel.c8d i Hrange).
  apply RTableModel.in_op_table_power in Hin; auto.
Qed.

Lemma lookup_pow_modulus_bounded : forall i,    
    0 <= i ->
    etable_values (ops_cell Store) i <> 0 -> 
    0 <= etable_values lookup_pow_modulus i < 2^64.
Proof.
  intros i Hrange Hops.
  assert (Hpow_value := lookup_pow_values i Hrange).
  replace (etable_values lookup_pow_power i) with ((etable_values load_block_inner_pos i) * 8 + 128) in *.
  2: {
    destruct (op_store_pow_lookup i Hrange) as [Hgate _].
    simpl in Hgate.
    replace (i+0) with i in * by lia.
    apply Zmult_integral in Hgate.
    destruct Hgate.
    - congruence.
    - lia. }
  assert (Hinner :=  inner_pos_bounded i Hrange Hops).
  specialize (Hpow_value ltac:(lia)).
  
  revert Hpow_value Hinner.
  generalize (etable_values load_block_inner_pos i ).
  intros z [H1 H2] H3.
  rewrite H2. clear H1 H2.
  replace (z * 8 + 128 - 128) with (z*8) by lia.
  split.
  - lia.
  - apply Z.pow_lt_mono_r; lia.
Qed.
    
Lemma op_store_len_modulus_helper : forall x y z w,
    0 <= x < 2 ->
    0 <= y < 2 ->
    0 <= z < 2 ->
    0 <= w < 2 ->
      0 <=
  x * 256 +
  y * 65536 +
  z * 4294967296 +
  w * 18446744073709551616 < field_order.
Proof. pose field_order_big. lia. Qed.

Program Definition op_store_len_modulus_gate :=  pgate_to_gate  _  p_op_store_len_modulus_gate.
Next Obligation.
  split; auto.
  - eauto 30 using  op_store_len_modulus_helper with moddable.
Qed.
    
Lemma len_modulus_bounded : forall i, 0<=i ->
                                      value etable (ops_cell Store) i <> 0 ->
                                      0 <=  (etable_values len_modulus i) <= 2^64.
Proof.
  intros i Hrange Hops.

  assert (Hops' :  value etable (ops_cell Store) i = 1).
  {
    simpl in Hops.
    destruct (ops_bit Store i); try congruence; auto.
  }
  destruct (op_store_len_modulus_gate i Hrange) as [Hgate _].
  replace (i+0) with i in * by lia.

  apply Zmult_integral in Hgate.
  destruct Hgate as [Hgate|Hgate]; [congruence|].
  unfold value in *. simpl in *.
  change (Z.pow_pos 2 64) with 18446744073709551616. 
  replace (etable_values len_modulus i) with
    (etable_values is_one_byte i * 256 +
          etable_values is_two_bytes i * 65536 + etable_values is_four_bytes i * 4294967296 +
          etable_values is_eight_bytes i * 18446744073709551616) by lia.
  clear Hgate.
  destruct (load_one_number_of_bytes i Hrange Hops') as [[? [? [? ?]]] | [[? [? [? ?]]]  | [[? [? [? ?]]]  | [? [? [? ?]]] ]]] ; lia.
Qed.


(* Yet another special purpose lemma.. *)
Lemma U64_plus_64_64_64 : forall x y z w,
    0 <= x < 2^64 ->
    0 <= y < 2^64 ->
    0 <= z < 2^64->
    0 <= w <= 2^64 ->
    0 <= x + (y*z*w) < field_order.
Proof.
intros.
assert (y*z*w < (2^64)*(2^64)*(2^64)).
apply Z.le_lt_trans with (y * z * 2^64).
- apply Zmult_le_compat_l. lia. lia.
- apply Zmult_lt_compat_r. lia.
  apply Zmult_lt_compat; lia. 
- pose field_order_big.
lia.
Qed.

Lemma u16_u64 : forall x,
    0 <= x < 2 ^16 ->
    0 <= x < 2^64.
Proof. lia. Qed.  
#[global] Hint Resolve u16_u64 : moddable.

Lemma shift_add_u16_u64: forall x y,
    0 <= x < 2 ^16 ->
    0 <= y < 2 ^16 ->
    0 <= Z.abs (x + y * 65536) < 2^64.
Proof.
  intros.
  rewrite Z.abs_eq by lia. lia.
Qed.
#[local] Hint Resolve shift_add_u16_u64 : moddable.

#[global] Hint Resolve  etable_is64_from16_u64 : moddable. 

Program Definition op_store_value_wrap :=  pgate_to_gate  _  p_op_store_value_wrap.
Next Obligation.
  split; auto.
  - apply moddable_mul'.
    eauto with moddable.
    intros Hops.

    apply moddable_pm.
    eauto with moddable.

    replace (n+0) with n in * by lia.
      
    assert (Hops' :  value etable (ops_cell Store) n = 1).
    {
      simpl in Hops.
      destruct (ops_bit Store n); try congruence; auto.
    }

    destruct (load_one_number_of_bytes n H Hops') as [[Hone [Htwo [Hthree Hfour]]] | [[Hone [Htwo [Hthree Hfour]]]  | [[Hone [Htwo [Hthree Hfour]]]  | [Hone [Htwo [Hthree Hfour]]] ]]];
      rewrite Hone, Htwo, Hthree, Hfour, !Z.mul_1_l, !Z.mul_0_l, !Z.add_0_r; try rewrite !Z.add_0_l.

    eauto with moddable.
    eauto with moddable.
    eauto with moddable.
    eauto with moddable.
Qed.
    
Lemma store_value_wrapped_u64 : forall n,  
  0<=n ->
  etable_values (ops_cell Store) n <> 0 ->
  0 <= Z.abs (etable_values store_value_wrapped n) < 2^64.
Proof.
  intros n Hrange Hops.
  destruct (op_store_value_wrap n Hrange) as [Hgate _].
  replace (n+0) with n in * by lia.
  simpl in Hgate.
  apply Zmult_integral in Hgate;
    destruct Hgate as [Hgate|Hgate] ; [congruence|].
  replace (etable_values store_value_wrapped n) with
    (etable_values is_one_byte n * etable_values store_value_tailing_u16_u8_low n +
           etable_values is_two_bytes n * etable_values store_value_u16_cells_le_0 n +
           etable_values is_four_bytes n *
           (etable_values store_value_u16_cells_le_0 n +
            etable_values store_value_u16_cells_le_1 n * 65536) +
           etable_values is_eight_bytes n * etable_values store_value_u64_cell n)
    by lia.
  clear Hgate.

  assert (Hops' :  value etable (ops_cell Store) n = 1).
    {
      simpl in Hops.
      destruct (ops_bit Store n); try congruence; auto.
    }

    destruct (load_one_number_of_bytes n Hrange Hops') as [[Hone [Htwo [Hthree Hfour]]] | [[Hone [Htwo [Hthree Hfour]]]  | [[Hone [Htwo [Hthree Hfour]]]  | [Hone [Htwo [Hthree Hfour]]] ]]];
      rewrite Hone, Htwo, Hthree, Hfour, !Z.mul_1_l, !Z.mul_0_l, !Z.add_0_r; try rewrite !Z.add_0_l;
    eauto with moddable.
Qed.  

Program Definition op_store_pick_value1 :=  pgate_to_gate  _  p_op_store_pick_value1.
Next Obligation.
  split; auto.
  apply moddable_mul'.
  eauto 25 with moddable.
  intros Hops.
  apply moddable_pmm. 
  eauto 25 with moddable.

  replace (n+0) with n in * by lia.
  pose (len_modulus_bounded n H Hops).
  apply U64_plus_64_64_64; eauto 25 with moddable.
  apply lookup_pow_modulus_bounded;auto.
Qed.


(* These two gate use unlimited numbers.
Program Definition op_store_pick_value2 :=  pgate_to_gate  _  p_op_store_pick_value2.
Program Definition op_store_pick_value3 :=  pgate_to_gate  _  p_op_store_pick_value3.
 *)

Program Definition op_store_pick_helper_value_check :=  pgate_to_gate  _  p_op_store_pick_helper_value_check.
Next Obligation.
  repeat (split; auto).
  - replace (n+0) with n in * by lia.
    apply moddable_mul; [eauto 25 with moddable|].
    pose (lookup_pow_modulus_bounded n H).
    eauto 25 with moddable.
Qed.

Program Definition op_store_pick_value_size_check :=  pgate_to_gate  _  p_op_store_pick_value_size_check.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.

Lemma u8_mul_256_u64 : forall x,
    0 <=  x < 2^8 ->
    0 <= (x * 256) < 2^64.
Proof. lia. Qed.
#[local] Hint Resolve  u8_mul_256_u64 : moddable.

Program Definition op_store_tailing_u16_decompose :=  pgate_to_gate  _  p_op_store_tailing_u16_decompose.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
Qed.

Lemma common_mul_BLOCKS_PER_PAGE_U64: forall x,
    0 <=  x < common ->
    0 <=  (x * WASM_BLOCKS_PER_PAGE) < 2^64.
Proof.
  intros. pose common_small. unfold WASM_BLOCKS_PER_PAGE. lia.
Qed.

(* This gate uses unlimited numbers.
Program Definition op_store_allocated_address :=  pgate_to_gate  _  p_op_store_allocated_address.
*)
