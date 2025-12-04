(* Copyright CertiK 2025. *)

Require Import Wasm.numerics.
Require Import Shared.
Require Import CommonModel.
Require Import IntegerFunctions.

Require Import List.
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Lemma bound_lt : forall x b b',  b < b' ->  0 <= x < b -> 0 <= x < b'.
Proof.
  lia.
Qed.


Lemma COMMON_RANGE_OFFSET_nonneg : 0 <= COMMON_RANGE_OFFSET.
Proof. cbv; intros; congruence. Qed.

Lemma OPCODE_ARG1_SHIFT_nonneg : 0 <= OPCODE_ARG1_SHIFT.
Proof. cbv; intros; congruence. Qed.

Lemma OPCODE_ARG0_SHIFT_nonneg : 0 <= OPCODE_ARG0_SHIFT.
Proof. cbv; intros. congruence. Qed.

Lemma OPCODE_CLASS_SHIFT_nonneg : 0 <= OPCODE_CLASS_SHIFT.
Proof. cbv; intros. congruence. Qed.

  
Lemma shift_plus_inj : forall {x x' y y' s},
    0 <= s ->
    Z.shiftl x s + y = Z.shiftl x' s + y' ->
    0 <= y < 2^s ->
    0 <= y' < 2^s ->
    x = x' /\ y = y'.
Proof.
  intros x x' y y' s Hs H Hy Hy'.
  rewrite !Zbits.Zshiftl_mul_two_p in * by lia.
  rewrite two_p_correct in *.

  assert (H' : (x * 2 ^ s + y)/2^s = (x' * 2 ^ s + y')/2^s) by
    (f_equal; assumption).
  rewrite !Z_div_plus_full_l in H' by lia.
  rewrite !Zdiv_small in H' by lia.
  assert (Hx : x = x') by lia.
  split; [assumption|].
  clear H' Hy Hy'.
  rewrite Hx in *.
  lia.
Qed.
  
Lemma shift_inj : forall {s},
    0 <= s ->
    forall x x',
    Z.shiftl x s = Z.shiftl x' s  ->
    x = x'.
Proof.
  intros s Hle x x' H.
  rewrite !Zbits.Zshiftl_mul_two_p in H by lia.
  pose (two_p_gt_ZERO s Hle).
  apply Z.mul_reg_r in H; lia.
Qed.

Lemma Int32_unsigned_inj : forall x x' ,
    Wasm_int.Int32.unsigned x = Wasm_int.Int32.unsigned x' ->
    x = x'.
Proof.
  intros.
  destruct x as [x xrange].
  destruct x' as [x' xrange'].
  simpl in *.
  subst.
  f_equal.
  destruct xrange as [p q].
  destruct xrange' as [p' q'].
  rewrite (Wasm_int.Int64.Z_lt_irrelevant p p').
  rewrite (Wasm_int.Int64.Z_lt_irrelevant q q').
  reflexivity.
Qed.  

Lemma Int64_unsigned_inj : forall x x' ,
    Wasm_int.Int64.unsigned x = Wasm_int.Int64.unsigned x' ->
    x = x'.
Proof.
  intros.
  destruct x as [x xrange].
  destruct x' as [x' xrange'].
  simpl in *.
  subst.
  f_equal.
  destruct xrange as [p q].
  destruct xrange' as [p' q'].
  rewrite (Wasm_int.Int64.Z_lt_irrelevant p p').
  rewrite (Wasm_int.Int64.Z_lt_irrelevant q q').
  reflexivity.
Qed.

Opaque Z.add Z.mul Z.shiftl Z_of_bool.


(* Size-bounding lemmas. *)

Lemma size_trans: forall s s' x,
    s < s' ->
    0 <= x < 2^s ->
    0 <= x < 2^s'.
Proof.
  intros s s' x H [H1 H2].
  split; try lia.
  apply Z.lt_le_trans with (2^s).
  lia.
  apply Z.pow_le_mono_r; lia.
Qed.  

Lemma int64_lt_arg1 : forall i,
 0 <= Wasm_int.Int64.unsigned i < 2 ^ OPCODE_ARG1_SHIFT.
Proof.
  intros i.
  unfold OPCODE_ARG1_SHIFT.
  replace (2^64) with Wasm_int.Int64.modulus.
  2: { unfold Wasm_int.Int64.modulus, Wasm_int.Int64.wordsize, Integers.Wordsize_64.wordsize.
       rewrite two_power_nat_correct.
       rewrite Zpower_nat_Z.
       f_equal. }
  apply Wasm_int.Int64.unsigned_range.
Qed.

Lemma int64_lt_64 : forall i,
 0 <= Wasm_int.Int64.unsigned i < 2 ^ 64.
Proof.
  intros i.
  destruct (Wasm_int.Int64.unsigned_range i).
  split; auto.
Qed.

Lemma int32_lt_32 : forall i,
 0 <= Wasm_int.Int32.unsigned i < 2 ^ 32.
Proof.
  intros i.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT,  COMMON_RANGE_OFFSET.
  destruct (Wasm_int.Int32.unsigned_range i).
  split; auto.
Qed.

Lemma int32_lt_arg0 : forall i,
 0 <= Wasm_int.Int32.unsigned i < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros.
  apply (size_trans 32).
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET  ; lia.
  apply int32_lt_32.
Qed.

Lemma int64_lt_arg0 : forall i,
    0 <= Wasm_int.Int64.unsigned i < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  intros.
  apply (size_trans OPCODE_ARG1_SHIFT).
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
  apply int64_lt_arg1.
Qed.

Lemma is32_lt_class_shift : forall x,
    0 <= x < 2^32 ->
    0 <= x < 2 ^ OPCODE_CLASS_SHIFT.
Proof.  
  intros.
  apply (size_trans 32).
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET; lia.
  auto.
Qed.

Lemma zero_lt_class_shift :  0 <= 0 < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  change OPCODE_CLASS_SHIFT with ( 64 + 32 + 32); lia.
Qed.  

Lemma shift_arg0_lt_class_shift : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG0_SHIFT < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  split.
  1: { apply Z.shiftl_nonneg; lia. }
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.


(* Reminder: 
Definition COMMON_RANGE_OFFSET := 32.
Definition OPCODE_ARG1_SHIFT := 64.
Definition OPCODE_ARG0_SHIFT := OPCODE_ARG1_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_CLASS_SHIFT := OPCODE_ARG0_SHIFT + COMMON_RANGE_OFFSET.

In other words, the layout is like this:

[class (16 bits)][arg0 (32 bits)][arg1 (32 bits)] [arg2  (64 bits)]

*)

Lemma shift_arg1_lt_arg0 : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  split.
  1: { apply Z.shiftl_nonneg; lia. }
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  rewrite !Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

(* This is not a tight bound, but it's all we need below. *)
Lemma shift_arg1_lt_class_shift : forall x,
    0 <= x < 2 ^ 32 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros.
  apply (size_trans OPCODE_ARG0_SHIFT).
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
  apply shift_arg1_lt_arg0; auto.
Qed.


Lemma Z_of_bool_isbit : forall b,
    Z_of_bool b = 0 \/ Z_of_bool b = 1.
Proof.
  destruct b; simpl; auto.
Qed.

Lemma isbit_is32 : forall x,
    (x = 0 \/ x = 1) ->
    0 <= x < 2^32.
Proof.
  destruct 1; subst; lia.
Qed.

Require IntegerFunctions.

Lemma shift_plus_bound : forall x y i j,
    0 <= x < 2^i ->
    0 <= y < 2^j ->
    0 <= Z.shiftl x j + y < 2 ^ (j+i).
Proof.
  intros x y i j Hx Hy.
  assert (0 <= i).
  { destruct (Z_le_gt_dec 0 i).
    - assumption.
    - rewrite Z.pow_neg_r in Hx by lia. lia. }
  assert (0 <= j).
  { destruct (Z_le_gt_dec 0 j).
    - assumption.
    - rewrite Z.pow_neg_r in Hy by lia. lia. }
  rewrite Z.add_comm.
  rewrite IntegerFunctions.plus_lor_n by lia.
  apply (IntegerFunctions.lor_bound_r j); try lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  split; [lia|].
  rewrite Z.pow_add_r by lia.
  rewrite Z.mul_comm.
  apply Zmult_lt_compat_l; lia.
Qed.
  
Lemma shift_arg0_arg1_lt_class_shift : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^64 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT + y < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  intros.
  unfold OPCODE_CLASS_SHIFT, COMMON_RANGE_OFFSET in *.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  assert (bound := shift_plus_bound x y 32 64 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma shift_arg1_64_lt_arg0 : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^64 ->
    0 <= Z.shiftl x OPCODE_ARG1_SHIFT + y < 2 ^ OPCODE_ARG0_SHIFT.
Proof.
  unfold OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  assert (bound := shift_plus_bound x y 32 64 ltac:(lia) ltac:(lia)).
  lia.
Qed.
  
Lemma shift_arg1_64_lt_class_shift : forall x y,
    0 <= x < 2^32 ->
    0 <= y < 2^OPCODE_ARG0_SHIFT -> 
    0 <= Z.shiftl x OPCODE_ARG0_SHIFT + y < 2 ^ OPCODE_CLASS_SHIFT.
Proof.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  assert (bound := shift_plus_bound x y 32 (64+32) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma shift_16_class_shift_lt_144
  : forall x y,
  0 <= x < 2 ^ 16 ->
  0 <= y < 2 ^ OPCODE_CLASS_SHIFT ->
  0 <= Z.shiftl x OPCODE_CLASS_SHIFT + y <  2 ^ 144.
Proof.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  intros.
  change 144 with (128+16).
  apply shift_plus_bound; lia.
Qed.
  
Lemma shift_16_class_shift_lt_144_no_plus
  : forall x,
  0 <= x < 2 ^ 16 ->
  0 <= Z.shiftl x OPCODE_CLASS_SHIFT <  2 ^ 144.
Proof.
  intros.
  replace  (Z.shiftl x OPCODE_CLASS_SHIFT) with ( Z.shiftl x OPCODE_CLASS_SHIFT + 0) by lia.  
  apply shift_16_class_shift_lt_144; auto.
  unfold OPCODE_CLASS_SHIFT, OPCODE_ARG0_SHIFT, OPCODE_ARG1_SHIFT, COMMON_RANGE_OFFSET.
  lia.
Qed.

#[export] Hint Resolve int32_lt_32 : size_lemmas.
#[export] Hint Resolve int64_lt_64 : size_lemmas.
#[export] Hint Resolve int64_lt_arg1 : size_lemmas.
#[export] Hint Resolve int64_lt_arg0 : size_lemmas.
#[export] Hint Resolve int32_lt_arg0 : size_lemmas.
#[export] Hint Resolve is32_lt_class_shift : size_lemmas.
#[export] Hint Resolve zero_lt_class_shift : size_lemmas.
#[export] Hint Resolve shift_arg0_lt_class_shift : size_lemmas.
#[export] Hint Resolve shift_arg1_lt_arg0 : size_lemmas.
#[export] Hint Resolve shift_arg1_lt_class_shift : size_lemmas.
#[export] Hint Resolve Z_of_bool_isbit : size_lemmas.
#[export] Hint Resolve isbit_is32 : size_lemmas.

#[export] Hint Resolve shift_arg1_64_lt_arg0  : size_lemmas.
#[export] Hint Resolve shift_arg0_arg1_lt_class_shift   : size_lemmas.
#[export] Hint Resolve shift_arg1_64_lt_class_shift  : size_lemmas.

#[export] Hint Resolve shift_16_class_shift_lt_144  : size_lemmas.
#[export] Hint Resolve shift_16_class_shift_lt_144_no_plus  : size_lemmas.

