(* Copyright (C) 2025 CertiK. *)

Require Import Wasm.numerics.
Require Import Shared.
Require Import ETableModel.
Require Import ImageTableModel.
Require Import CommonModel.

Require Import List.
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.


Require Import IntegerFunctions.
Require Import WasmiModel.
Require Import InjectivityHelper.

(* Lemmas used for instruction decoding proofs. *)
Definition bool_of_Z (z:Z) : bool
             := if Z.eqb z 0 then false else true.

Lemma Z_of_BinShiftOp_inj : forall b b',
    Z_of_BinShiftOp b = Z_of_BinShiftOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_BinOp_inj : forall b b',
    Z_of_BinOp b = Z_of_BinOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_UnaryOp_inj : forall b b',
    Z_of_UnaryOp b = Z_of_UnaryOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_BitOp_inj : forall b b',
    Z_of_BitOp b = Z_of_BitOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma Z_of_RelOp_inj : forall b b',
    Z_of_RelOp b = Z_of_RelOp b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Transparent Z_of_bool.


Lemma Z_of_bool_inj : forall b b',
    Z_of_bool b = Z_of_bool b' ->
    b = b'.
Proof.
  destruct b; destruct b'; simpl in *; intros; try lia; reflexivity.
Qed.

Lemma encode_load_access_inj : forall sz sz' sign sign',
    encode_load_access sz sign = encode_load_access sz' sign' ->
    sz = sz' /\ sign = sign'.
Proof.
  destruct sz; destruct sz'; destruct sign; destruct sign';
    unfold encode_load_access; simpl; intros; split; try lia; reflexivity.
Qed.

Lemma encode_store_access_inj : forall sz sz',
    encode_store_access sz  = encode_store_access sz' ->
    sz = sz'.
Proof.
  destruct sz; destruct sz';
    unfold encode_store_access; simpl; intros;  try lia; reflexivity.
Qed.

Transparent Z.add Z.mul Z.shiftl Z_of_bool.


Lemma encode_ConvOp_inj : forall sign sign' is32 is32' src src' dst dst',
    encode_ConvOp sign is32 src dst = encode_ConvOp sign' is32' src' dst' ->
    sign = sign' /\ is32 = is32' /\ src = src' /\ dst = dst'.
Proof.
  destruct sign; destruct sign'; destruct is32; destruct is32'; destruct src; destruct src'; destruct dst; destruct dst';
    unfold encode_ConvOp; simpl; intros; repeat split; try lia; reflexivity.
Qed.

Opaque Z.add Z.mul Z.shiftl Z_of_bool.

Lemma Z_of_UnaryOp_is32 : forall b,
    0 <= Z_of_UnaryOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BitOp_is32 : forall b,
    0 <= Z_of_BitOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BinOp_is32 : forall b,
    0 <= Z_of_BinOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_BinShiftOp_is32 : forall b,
    0 <= Z_of_BinShiftOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.

Lemma Z_of_RelOp_is32 : forall b,
    0 <= Z_of_RelOp b < 2^32.
Proof.
  destruct b; simpl; lia.
Qed.    

Transparent Z_of_bool.
Lemma encode_load_access_is32 : forall l s,
   0 <= encode_load_access l s < 2^32.
Proof.
  destruct l; destruct s; unfold encode_load_access, Z_of_bool; simpl; lia.
Qed.

Lemma encode_store_access_is32 : forall l,
   0 <= encode_store_access l < 2^32.
Proof.
  destruct l;  unfold encode_store_access, Z_of_bool; simpl; lia.
Qed.

Lemma encode_ConvOp_is32 : forall sign is32 src dst,
    0 <= encode_ConvOp sign is32 src dst < 2^32.
Proof.
  destruct sign; destruct is32; destruct src; destruct dst; unfold encode_ConvOp; simpl;
    rewrite !Z.shiftl_mul_pow2 by lia;
    lia.
Qed.

Opaque Z_of_bool.

#[export] Hint Resolve Z_of_BitOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_BinOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_BinShiftOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_UnaryOp_is32 : size_lemmas.
#[export] Hint Resolve Z_of_RelOp_is32 : size_lemmas.
#[export] Hint Resolve encode_load_access_is32 : size_lemmas.
#[export] Hint Resolve encode_store_access_is32 : size_lemmas.
#[export] Hint Resolve encode_ConvOp_is32 : size_lemmas.

Opaque Z.add Z.mul Z.shiftl Z_of_bool.

Lemma opcode_of_instruction_inj : forall i1 i2,
    opcode_of_instruction i1 = opcode_of_instruction i2 ->
    i1 = i2.
Proof.
  
  (destruct i1; destruct i2; simpl; try rewrite <- !Zplus_assoc; intros H;
    try match goal with
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT + _)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT |- _ ]
        => replace (Z.shiftl c2 OPCODE_CLASS_SHIFT) with (Z.shiftl c2 OPCODE_CLASS_SHIFT + 0) in H by lia
      | [H: (Z.shiftl ?c1 OPCODE_CLASS_SHIFT)
                = Z.shiftl ?c2 OPCODE_CLASS_SHIFT + _ |- _ ]
        => replace (Z.shiftl c1 OPCODE_CLASS_SHIFT) with (Z.shiftl c1 OPCODE_CLASS_SHIFT + 0) in H by lia
      end);
  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_CLASS_SHIFT + _
            = Z.shiftl ?c OPCODE_CLASS_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT
            = Z.shiftl _ OPCODE_CLASS_SHIFT |- _] => apply (shift_inj OPCODE_CLASS_SHIFT_nonneg) in H; now congruence
(*    | [ H: _ = 0 |- _] => admit (* todo later *) *)
(*    | [ H: 0 = _ |- _] => admit (* todo later *) *)
                                                                                
      | [ H:    Z.shiftl _ OPCODE_CLASS_SHIFT + _
            = Z.shiftl _ OPCODE_CLASS_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_CLASS_SHIFT_nonneg H); [eauto 7 with size_lemmas | eauto 7 with size_lemmas | congruence]
    end;

  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_ARG0_SHIFT + _
            = Z.shiftl ?c OPCODE_ARG0_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_ARG0_SHIFT
            = Z.shiftl _ OPCODE_ARG0_SHIFT |- _] => apply (shift_inj OPCODE_ARG0_SHIFT_nonneg) in H
      | [ H:   Z.shiftl _ OPCODE_ARG0_SHIFT + _
            = Z.shiftl _ OPCODE_ARG0_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_ARG0_SHIFT_nonneg H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas  | ]
    end;
  try match goal with
    | [ H:    Z.shiftl ?c OPCODE_ARG1_SHIFT + _
            = Z.shiftl ?c OPCODE_ARG1_SHIFT + _ |- _] => apply Z.add_reg_l in H
    | [ H:    Z.shiftl _ OPCODE_ARG1_SHIFT
            = Z.shiftl _ OPCODE_ARG1_SHIFT |- _] => apply (shift_inj OPCODE_ARG1_SHIFT_nonneg) in H
      | [ H:   Z.shiftl _ OPCODE_ARG1_SHIFT + _
            = Z.shiftl _ OPCODE_ARG1_SHIFT + _ |- _] => destruct (shift_plus_inj OPCODE_ARG1_SHIFT_nonneg H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas  | ]
    end;
  repeat match goal with
    | [ H: Z_of_BinShiftOp _ = Z_of_BinShiftOp _ |- _] => apply Z_of_BinShiftOp_inj in H
    | [ H: Z_of_BinOp _ = Z_of_BinOp _ |- _] => apply Z_of_BinOp_inj in H
    | [ H: Z_of_UnaryOp _ = Z_of_UnaryOp _ |- _] => apply Z_of_UnaryOp_inj in H
    | [ H: Z_of_BitOp _ = Z_of_BitOp _ |- _] => apply Z_of_BitOp_inj in H
    | [ H: Z_of_RelOp _ = Z_of_RelOp _ |- _] => apply Z_of_RelOp_inj in H
    | [ H: Z_of_bool _ = Z_of_bool _ |- _] => apply Z_of_bool_inj in H
    | [ H:  encode_load_access _ _ = encode_load_access _ _ |- _] =>
        apply encode_load_access_inj in H; destruct H
    | [ H:  encode_store_access _ = encode_store_access _ |- _] =>
        apply encode_store_access_inj in H; destruct H
    | [ H:  encode_ConvOp _ _ _ _ = encode_ConvOp _ _ _ _ |- _] =>
        apply encode_ConvOp_inj in H; destruct H as [? [? [? ?]]]
    | [ H: Wasm_int.Int32.unsigned _ = Wasm_int.Int32.unsigned _ |- _] => apply Int32_unsigned_inj in H
    | [ H: Wasm_int.Int64.unsigned _ = Wasm_int.Int64.unsigned _ |- _] => apply Int64_unsigned_inj in H
         end;
  try congruence.
Qed. 

Lemma iscommon_is_2_32 : forall x,
    0 <= x < common ->
    0 <= x < 2^32.
Proof.
  intros.
  eapply bound_lt.
  apply common_le_2_32.
  auto.
Qed.

Lemma iscommon_is_2_64 : forall x,
    0 <= x < common ->
    0 <= x < 2^64.
Proof.
  intros.
  apply bound_lt with (2^32).
  lia.
  apply iscommon_is_2_32.
  auto.
Qed.

Lemma iscommon_is32 : forall x,
    0 <= x < common ->
    0 <= x <= Wasm_int.Int32.max_unsigned.
Proof.
  intros. 
  pose (iscommon_is_2_32 x).
  change ( Wasm_int.Int32.max_unsigned) with (2^32  -1).
  lia.
Qed.

Lemma iscommon_is64 : forall x,
 0 <= x < common ->
 0 <= x <= Wasm_int.Int64.max_unsigned.
Proof.
  intros. 
  pose (iscommon_is_2_64 x).
  change ( Wasm_int.Int64.max_unsigned) with (2^64  -1).
  lia.
Qed.

Lemma is64_is64 : forall x,
 0 <= x < Wasm_int.Int64.modulus ->
 0 <= x <= Wasm_int.Int64.max_unsigned.
Proof.
  change Wasm_int.Int64.modulus with (2^64).
  change Wasm_int.Int64.max_unsigned with (2^64 -1).
  lia.
Qed.
  
Lemma bool_of_Z_simpl : forall x,
    (x = 0 \/ x = 1) ->
    (Z_of_bool (bool_of_Z x)) = x.
Proof.
  Transparent Z_of_bool bool_of_Z.
  destruct 1; subst; unfold bool_of_Z; simpl; reflexivity.
  Opaque Z_of_bool bool_of_Z.
Qed.  

Lemma iscommon_lt_class_shift: forall x,
    0 <= x < common ->
    0 <= x <   2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros x H.
  change OPCODE_CLASS_SHIFT with 128.
  apply iscommon_is_2_32 in H.
  lia.
Qed.


Lemma iscommon_lt_arg0_shift: forall x,
    0 <= x < common ->
    0 <= x <   2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros x H.
  change OPCODE_ARG0_SHIFT with 96.
  apply iscommon_is_2_32 in H.
  lia.
Qed.

#[export] Hint Resolve iscommon_is_2_32 : size_lemmas.
#[export] Hint Resolve iscommon_is_2_64 : size_lemmas.
#[export] Hint Resolve iscommon_lt_class_shift : size_lemmas.
#[export] Hint Resolve iscommon_lt_arg0_shift : size_lemmas.

Lemma U64_unsigned_repr : forall c,
    is64 c ->
    forall i,
    Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int64.unsigned_repr.
  apply is64_is64.
  apply H.
Qed.

Lemma common_unsigned_repr: forall c,
    iscommon c ->
    forall i,
    Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int32.unsigned_repr.
  apply iscommon_is32.
  apply H.
Qed.

Lemma common_unsigned_repr64: forall c,
    iscommon c ->
    forall i,
    Wasm_int.Int64.unsigned (Wasm_int.Int64.repr (etable_values c i)) = (etable_values c i).
Proof.
  intros.
  apply Wasm_int.Int64.unsigned_repr.
  apply iscommon_is64.
  apply H.
Qed.

Transparent Z_of_bool.
Lemma bool_is_common : forall x,
    0 <= Z_of_bool x < common.
Proof.
  split.
  - destruct x; simpl; lia.
  - pose CommonModel.one_lt_common.
    destruct x; simpl; lia.
Qed.

Lemma isbit_iscommon : forall x,
    (x = 0 \/ x = 1) ->
    0 <= x < common.
Proof.
  intros x H.
  split.
  - lia.
  - pose CommonModel.one_lt_common.
    lia.
Qed.

Definition encode_br_table_entry' fid iid index drop keep dst_pc :=
  Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl fid 32 + iid) 32 + index) 32 + drop) 32 + keep) 32 + dst_pc.

Lemma encode_br_table_entry'_spec : forall fid iid index drop keep dst_pc,
    0 <= fid < 2^32 ->
    0 <= iid < 2^32 ->
    0 <= index < 2^32 ->
    0 <= drop < 2^32 ->
    0 <= keep < 2^32 ->
    0 <= dst_pc < 2^32 ->
    encode_br_table_entry fid iid index drop keep dst_pc
    =  encode_br_table_entry' fid iid index drop keep dst_pc.
Proof.
  intros  fid iid index drop keep dst_pc Hfid Hiid Hindex Hdrop Hkeep Hdst_pc.
  unfold   encode_br_table_entry,   encode_br_table_entry'.
  replace ( (0 * INDIRECT_CLASS_SHIFT + fid * Z.shiftl 1 (0 + 32 + 32 + 32 + 32 + 32) +
   iid * Z.shiftl 1 (0 + 32 + 32 + 32 + 32) + index * Z.shiftl 1 (0 + 32 + 32 + 32) +
               drop * Z.shiftl 1 (0 + 32 + 32) + keep * Z.shiftl 1 (0 + 32) + dst_pc))
    with
    ( fid * Z.shiftl 1 (32 + 32 + 32 + 32 + 32) + iid * Z.shiftl 1 (32 + 32 + 32 + 32) +
  index * Z.shiftl 1 (32 + 32 + 32) + drop * Z.shiftl 1 (32 + 32) + keep * Z.shiftl 1 32 + dst_pc).
  2: { rewrite Z.mul_0_l.
       reflexivity.
  }
  replace (fid * Z.shiftl 1 (32 + 32 + 32 + 32 + 32) + iid * Z.shiftl 1 (32 + 32 + 32 + 32) +
             index * Z.shiftl 1 (32 + 32 + 32) + drop * Z.shiftl 1 (32 + 32) + keep * Z.shiftl 1 32 + dst_pc)
    with (Z.shiftl fid (32 + 32 + 32 + 32 + 32) + Z.shiftl iid (32 + 32 + 32 + 32) +
  Z.shiftl index (32 + 32 + 32) + Z.shiftl drop (32 + 32) + Z.shiftl keep 32 + dst_pc).
  2: {
    rewrite !Z.shiftl_mul_pow2 by lia.
    reflexivity.
  }
  replace (Z.shiftl fid (32 + 32 + 32 + 32 + 32) + Z.shiftl iid (32 + 32 + 32 + 32) +
             Z.shiftl index (32 + 32 + 32) + Z.shiftl drop (32 + 32) + Z.shiftl keep 32 + dst_pc)
    with (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl fid 32 + iid) 32 + index) 32 + drop) 32 + keep) 32 + dst_pc).
  2: {
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite !Z.pow_add_r by lia.
    lia.
  }    
  rewrite Zmod_small.
  { reflexivity. }
  { 
    apply bound_lt with (2^(6*32)).
    apply  encode_br_table_entry_field_order.
    change (2 ^ (6 * 32)) with (2 ^ (32+(32+(32+(32+(32+32)))))).
    repeat apply shift_plus_bound; auto.
  }
Qed.
       
Lemma encode_br_table_entry_inj :
  forall fid fid' iid iid' index index' drop drop' keep keep' dst_pc dst_pc',
    0 <= fid < 2^32 ->
    0 <= fid' < 2^32 ->
    0 <= iid < 2^32 ->
    0 <= iid' < 2^32 ->
    0 <= index < 2^32 ->
    0 <= index' < 2^32 ->
    0 <= drop < 2^32 ->
    0 <= drop' < 2^32 ->
    0 <= keep < 2^32 ->
    0 <= keep' < 2^32 ->
    0 <= dst_pc < 2^32 ->
    0 <= dst_pc' < 2^32 ->
    encode_br_table_entry fid iid index drop keep dst_pc
    =  encode_br_table_entry fid' iid' index' drop' keep' dst_pc' ->
    fid=fid' /\ iid=iid' /\ index=index' /\ drop = drop' /\ keep=keep' /\ dst_pc = dst_pc'.
Proof.
  intros.
  rewrite !encode_br_table_entry'_spec in H11 by auto.
  unfold encode_br_table_entry' in H11.
  assert (nonneg32 : 0 <= 32) by lia.
  repeat match goal with
  | [ H:    Z.shiftl _ 32 + _
            = Z.shiftl _ 32 + _ |- _] => destruct (shift_plus_inj nonneg32 H); clear H; [eauto 7 with size_lemmas | eauto 7 with size_lemmas | ]
         end.
  lia.
Qed.

