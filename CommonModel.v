(* Copyright CertiK 2025. *)


Require Import ZArith.
Require Import Shared.

Require Import ZArith.Znumtheory.

Open Scope Z_scope.

(* from spec/src/encode/mod.rs *)

Definition COMMON_RANGE_OFFSET := 32.

(* Assumption about the field order size versus the k value. 
   The "Pasta curves" have an order of about 2^254.
   The common range is about 2^22, so it should fit comfortably.
   https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/ *)
Axiom common_lt_order : 0 <= (2 * common + 10) * Z.shiftl 1 (0 + 1 + 32) + 10 < field_order.
Axiom int_lt_order : 2^129 < field_order.
Axiom field_order_prime : Znumtheory.prime field_order.
Axiom one_lt_common : 1 < common.
Axiom eighteen_le_common : (2^18) <= common. (* This is controlled by the definition of k in zkWasm. *)

Axiom encode_frame_table_entry_order1 : 2 ^ (1 + 5 * CommonModel.COMMON_RANGE_OFFSET) < field_order.

Axiom encode_br_table_entry_field_order : 2^(6*32) < field_order.
Axiom encode_instruction_table_entry_field_order : 2^(208) < field_order.

Axiom common_le_2_32 : common < 2^32.


(* Instruction encoding parameters *)
Definition OPCODE_ARG1_SHIFT := 64.
Definition OPCODE_ARG0_SHIFT := OPCODE_ARG1_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_CLASS_SHIFT := OPCODE_ARG0_SHIFT + COMMON_RANGE_OFFSET.
Definition OPCODE_SHIFT := OPCODE_CLASS_SHIFT + 16.
