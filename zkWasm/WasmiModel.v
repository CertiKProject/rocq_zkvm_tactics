Require Import ZArith.
Require Import List.
Require Import Wasm.operations.
Require Import IntegerFunctions.

Open Scope Z_scope.

(* (fid, iid) *)
Definition label : Set := Z * Z.

Record WasmState := {
    wasm_pc : label; (* program counter *)
    wasm_stack : list Z;
    wasm_globals : list Wasm.datatypes.global;
    wasm_memory : Wasm.datatypes.memory;
    wasm_callstack : list label
}.

Definition incr_iid st :=
  match st with
  | Build_WasmState (fid, iid) stk glb mem cs => Build_WasmState (fid, iid+1) stk glb mem cs
  end.

Definition move_to_label st lbl :=
  match st with
  | Build_WasmState _ stk glb mem cs => Build_WasmState lbl stk glb mem cs
  end.

Definition move_to_iid st next_iid :=
  match st with
  | Build_WasmState (fid, iid) stk glb mem cs => Build_WasmState (fid, next_iid) stk glb mem cs
  end.

Definition update_stack st a' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a'; wasm_globals := b; wasm_memory := c; wasm_callstack := d |}
  end.

Definition update_globals st b' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc;  wasm_stack := a; wasm_globals := b'; wasm_memory := c; wasm_callstack := d |}
  end.

Definition update_memory st c' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a; wasm_globals := b; wasm_memory := c'; wasm_callstack := d |}
  end.

Definition update_callstack st d' :=
  match st with
  | Build_WasmState pc a b c d => {| wasm_pc := pc; wasm_stack := a; wasm_globals := b; wasm_memory := c ; wasm_callstack := d' |}
  end.

  (*  Compare with the definition in Wasm.operations:

       Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
         List.nth_error (inst_globs i) j.

       Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
         option_bind (List.nth_error (s_globals s))
           (sglob_ind s i j).

       Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value :=
          option_map g_val (sglob s i j).

      Here we (for now) omit the indirection of global addresses -> globals.
   *)

From mathcomp Require seq.

Definition glob_val (gs : list Wasm.datatypes.global) (j : nat) : option value :=
  option_map g_val (List.nth_error gs j).

Definition set_glob (gs : list Wasm.datatypes.global) (k : nat) (v : Wasm.datatypes.value) : option (list Wasm.datatypes.global) :=
  option_map
    (fun g =>
      let g' := Wasm.datatypes.Build_global (Wasm.datatypes.g_mut g) v in
      seq.set_nth g' gs k g')
    (List.nth_error gs k).

Definition value_rel (z:Z) (v: value) : Prop :=
  match v with
  |  VAL_int32 i => z = Wasm_int.Z_of_uint i32m i
  |  VAL_int64 i => z = Wasm_int.Z_of_uint i64m i
  |  _ => False
  end.

Inductive BinOp :=
  ADD | SUB | MUL | DIV_u | REM_u | DIV_s | REM_s.

Inductive BinShiftOp :=
  SHL | SHR_u | SHR_s | ROTL | ROTR.

Inductive UnaryOp :=
  CTZ | CLZ | POPCNT.


Inductive RelOp :=
  EQ | NEQ | GT_s | GT_u | GE_s | GE_u | LT_s | LT_u | LE_s | LE_u.

Inductive ConvOpSrc :=
  VAL8 | VAL16 | VAL32 | VAL64.

Inductive ConvOpRes :=
  RES32 | RES64.

Inductive BitOp := AND | OR | XOR.

Inductive Instruction :=
| IBinShift : bool -> BinShiftOp -> Instruction
| IBin : bool -> BinOp -> Instruction
| IBrIfEqz : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| IBrIf : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| IBr : bool -> Wasm_int.Int32.int -> Wasm_int.Int64.int -> Instruction
| ICall : Wasm_int.Int32.int -> Instruction
| ICallIndirect : Wasm_int.Int32.int -> Instruction
| ICallHost
| IConst : bool -> Wasm_int.Int64.int -> Instruction
| IConversion : bool -> bool -> ConvOpSrc -> ConvOpRes -> Instruction
| IDrop 
| IGlobalGet : Wasm_int.Int32.int -> Instruction
| IGlobalSet : Wasm_int.Int32.int -> Instruction
| ILocalGet : bool -> Wasm_int.Int32.int -> Instruction
| ILocalSet : bool -> Wasm_int.Int32.int -> Instruction
| ILocalTee : bool -> Wasm_int.Int32.int -> Instruction
| IRel : bool -> RelOp -> Instruction
| IReturn : bool -> Wasm_int.Int32.int -> Instruction
| ISelect
| ITest : bool -> Instruction
| IUnary : bool -> UnaryOp -> Instruction
| ILoad : bool -> ConvOpSrc -> bool -> Wasm_int.Int64.int -> Instruction
| IStore : bool -> ConvOpSrc -> Wasm_int.Int64.int -> Instruction
| IBinBit : bool -> BitOp -> Instruction
| IMemorySize
| IMemoryGrow
| IBrTable : Wasm_int.Int32.int -> Instruction.

Parameter program : label -> Instruction.

(* Target addresses for the call_indirect instruction.  *)
Record CallTableEntry := {
    entry_table_idx :  Wasm_int.Int32.int;
    entry_type_id :  Wasm_int.Int32.int;
    entry_offset :   Wasm_int.Int32.int;
    entry_func_idx :   Wasm_int.Int32.int;
 }.
    
Parameter module_table_entries : CallTableEntry -> Prop.

Record BrTableEntry := {
    br_table_drop : Wasm_int.Int32.int;
    br_table_keep : bool;
    br_table_dst_pc : Wasm_int.Int32.int;
    }.    

