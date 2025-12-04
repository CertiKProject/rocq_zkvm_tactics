# Rocq Tactics for Field Element Manipulations in zkVMs

This repo presents a set of Rocq tactics to automatically handle proofs about integers modulo a large prime number. The work was done by CertiK for the Ethereum Foundation grant "Better Rocq tactics for modular arithmetic & handling packed integers", Grant ID FY25-1977 | EF ESP.

Reasoning about integers modulo is important in zero-knowledge applications, where all data must be encoded as elements in a finite field. Therefore, all the zk-constraints are equivalent to equations modulo a prime number p. Unfortunately this kind of equations is inconvenient to work with in Rocq. Goals that involve only sums and products of integers can often be solved completely automatically by Rocq's "Micromega" solvers, but as soon as there are modulo operations involved there is no similar decision procedure available and the programmer needs manual work. In our previous work on [verifying the zkWasm zkVM](https://github.com/CertiKProject/zkwasm-fv) we noticed that this kind of work took up a disproportionate amount of effort. For example, proving how certain numbers were encoded into a table column required as much work as the proofs of the actual interesting invariants of those numbers.

For zk-applications in general this is an unavoidable problem. But zkVMs in particular have some additional structure which we can make use of. They are usually emulating some 32-bit or 64-bit instruction set, so the numbers involved are constrained to be between 0 and a certain value (e.g. 2^32 or 2^64). The operations involved in the zk-constraints often fall into two classes:

* Packing multiple integers into a single field element by shifting and adding them, like a constraint w = (x*2^64 + y*2^32 + z) mod p, where x, y, and z are 32-bit integers. The intention of the programmer is that the sum is (much) smaller than the field order p. 
* Constraints representing ALU operations on registers. For example, the implementation of an addition instruction might involve a constraint r = (x + y) mod p, where x and y are 32-bit numbers. Again, the intention of the programmer is to treat the operation as an addition of integers, and because the numbers are much smaller than p there is no risk of the equation "wrapping around".

In these cases, it is often possible to "factor" the proofs into two parts. First, prove that all the numbers involved in the equations are small enough that there can be no wraparound, and second do the rest of the correctness proofs while ignoring the modulo-p part of the equations. 

In this work, we apply this strategy in two sets of tactics: one for proving injectivity of integer-packing operations, and one to simplify equations involving range-constrained numbers. We evaluate the work by using the tactics to prove some goals related to the correctness of the  zkWasm zkVM (which we had set aside as outside the scope of our previous verification effort). The tactics are set up in the same way as we modeled constraints for the zkWasm project, so they should be useful for any project written in Halo2, or adaptable to any zk-prover model that uses polynomial constraints over typed table columns.

## Machine Model

We assume a shallow embedding into Rocq where the Halo2 tables are postulated as `Parameter`s. For example, a table `etable` is modeled by assuming there is a function `etable_values` which maps each (column, row) pair to the contents of a cell. 

```coq
Inductive etable_cols :=
(* Common config, from etable/mod.rs *)
| enabled_cell
| ops_cell : OpcodeClass -> etable_cols
| rest_mops_cell
| rest_jops_cell
| input_index_cell
| context_input_index_cell
| context_output_index_cell
| external_host_call_index_cell
| sp_cell
| mpages_cell
| frame_id_cell
| eid_cell
| fid_cell
(*...*)

Parameter etable_values : etable_cols -> Z -> Z.
Parameter etable_numRow : Z.
```

The circuits are translated as a set of `Axioms` about properties that the table satisfies. This can be done by manually hand-translating them, or this could be the output of an automated tool.

To represent the gates, we provide a Rocq function `pgate` which expands into an assertion that a set of polynomials evaluate to zero modulo p for each row of a table (the standard form of PLONKish gate constraints). This way the constraints can be translated line by line, e.g. 

```rust
meta.create_gate("bit table: 2. acc u32", |meta| {
   vec![compose_u32_if_bit!(result), acc_u32_if_popcnt!(result)]
}
```
becomes

```coq
Axiom bit_table_gate_2 : pgate bit_table (fun get =>
      compose_u32_if_bit get val_res :: acc_u32_if_popcnt get val_res :: nil).
```

zkWasm, similar to other zk-projects, uses a set of "allocator" utility functions to add type-constraints to the table columns. Columns can be typed as bools, 32- or 64-bit integers, or ``common range'' numbers (0 ≤ x < 2^k, where k is a global parameter). For example, if the programmer declares a column using `allocator.alloc_u32_state_cell()`, behind the scenes the allocator code adds four additional columns for the bytes of the word, and arithmetic and lookup constraints to force the column to range over 32-bit numbers. In our development these helper functions are treated as trusted and we add axioms specifying them.

```coq
Definition iscommon c := forall i, 0 <= etable_values c i < common.

Axiom eid_common: iscommon eid_cell. 
```

This is the crucial point for the present tactics: we add the range assumptions such as `eid_common` to a global hint database, and use them to satisfy the required preconditions.

## Reasoning about injectivity of integer-packing

zkVMs often have reason to pack multiple integers into a single field element. The most common case is for instruction decoding/encoding, where the opcode/registers/immediates of an instruction are combined into single word. The zkVM has a lookup-constraint corresponding to an instruction fetch operation. In the corresponding correctness proofs, we need to prove that the instruction encoding is injective, so that the fetched word can only correspond to a single instruction.

This injectivity proof is very tedious to do as an ad-hoc proof in Rocq. However, it's possible to do it in a systematic way. We prove a lemma saying that the operation (x,y) ↦ (x<<s)+y is injective if 0 ≤ y < 2^s$.

```
Lemma shift_plus_inj : forall {x x' y y' s},
    0 <= s ->
    Z.shiftl x s + y = Z.shiftl x' s + y' ->
    0 <= y < 2^s ->
    0 <= y' < 2^s ->
    x = x' /\ y = y'.
```

Then, because the instruction encoding function consists of shifting and adding the many different parts, we can use an LTac script to apply this lemma recursively. However, each time we apply this operation, we need to prove the side condition that y and y' are small enough. This is done through a Hint database of lemmas. 


### Evaluation

We apply this approach to prove the injectivity of the zkWasm instruction encode operation (lemma `opcode_of_instruction_inj`). Whereas building a similar proof by listing each step manually would take thousands of lines of proof script, here it can be solved by a 53 lines long tactic.

The tactics are not specific to the opcode instruction function, which we demonstrate by also applying them to zkWasm's `encode_br_table_entry` function (which packs together six integers that represent the target of a jump instruction into a single word). When we manually proved injectivity of a similar function `encode_frame_table_entry` in the zkWasm verification project it took 200 lines of fiddly proof to find the right argument. Here it is done by just two steps, first re-distribute the shifts in an obvious way, 

```coq
(fid * Z.shiftl 1 FID_SHIFT + iid * Z.shiftl 1 IID_SHIFT + index * Z.shiftl 1 INDEX_SHIFT + drop * Z.shiftl 1 DROP_SHIFT + keep * Z.shiftl 1 KEEP_SHIFT + dst_pc)
  =
  Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl (Z.shiftl fid 32 + iid) 32 + index) 32 + drop) 32 + keep) 32 + dst_pc
```

and then the injectivity of the latter operation is proven through a single tactic invocation, using the size lemmas for the side conditions.


## Reasoning about integers mod p in the gate constraints.

The PLONKish polynomial constraints are of course evaluated modulo the field order p, so once we expand out the definition of `pgate`, for example one constraint, as represented inside the Coq theorem prover, may say 

```coq
Gate_p: 
  forall i, 0 <= i < mtable_numrows ->
 (mtable_values start_eid_cell i + mtable_values eid_diff_cell i + 1 - mtable_values end_eid_cell i) mod p = 0.
```

As we mentioned above, Rocq’s automation tactics for modular arithmetic are weak, so these constraints are inconvenient to reason about. It would be much easier if it just said

```
Gate: 
  forall i, 0 <= i < mtable_numrows ->
 (mtable_values start_eid_cell i + mtable_values eid_diff_cell i + 1 - mtable_values end_eid_cell i) = 0.
```

The concept of this work is that it is often possible to divide the proofs into two steps: first prove that (because the numbers involved are small enough), the `Gate_p` equation implies the `Gate` equation, and then do all the rest of the proofs in terms that. We define a property `moddable` which means that the mod operations can be omitted from an expression `e`, and then a series of lemmas to prove `moddable e` for complex expressions `e`.

```coq
Definition moddable (e:Z) :=
  (e mod field_order) = 0 -> (e = 0).
```

### Rules for `moddable`

In order to explore this concept, we survey a  set of gates from the zkWasm project in order to deduce a set of rules that suffices to prove them. Ultimately, this is an empirical question: are the gates in fact written in a way that makes it possible to divide the proofs in this way?

The two most basic rules say that the product of two moddable expressions is moddable (because p is a prime number), and that an expression is moddable if its absolute value is provably in the range -p < e < p. 

```coq
Lemma moddable_mul : forall x y ,
    moddable x -> moddable y -> moddable (x*y).

Lemma moddable_absbounded : forall x,
    0 <= Z.abs x < field_order ->
    moddable x.
```

A simple zkVM gate for implementing an ADD instruction may look something like `(enabled_add)(lhs + rhs - result) mod p = 0`. Here the `enabled_bit` is 1 if the current instruction is an ADD and 0 otherwise, so if the rule is not enabled the equation is vacuously true, but otherwise it states the equality  `result = lhs + rhs`.  The two rules above suffice to get rid of the `mod p` operation, by first using the multiplication rule and then using the range information for the variables.

The above rules suffice for many of the zkWasm gates, particularly the ones in the "Memory" and "Unary operations" groups. However, in our survey we also found examples of gate equations that do not fit into those patterns.

**Gates that use single unbounded numbers**

For example, zkWasm's OpUnary constraints contain one gate (part of the implementation of the  "count trailing zeros" wasm instruction) with the equation `(ctz_degree_helper - aux1 * lookup_pow_modulus * 2) mod p = 0`. Here the `aux1` and `lookup_pow_modulus` columns are typed, so we know those numbers are small, but the `ctz_degree_helper` is untyped and can contain any field element.

This kind of equation can still be proven to not wrap around, but it requires a different reasoning principle:

```coq
Lemma moddable_sub : forall x y,
    0 <= x < field_order ->
    0 <= y < field_order ->
    moddable (x-y).
```

In our development we provide both of these principles. Similarly expressions like `(x - y - z)` can also be handled provided that both `y` and `z` are typed so the quantity `x+y` does not overflow.

A zk-programmer may prefer to leave off the type annotations on columns in this way in order to optimize the constraint system. For example, in the above example,  the range checks constraints on `ctz_degree_helper` could be omitted. However, reasoning using subtraction in this way is less easy to automate than the "absolute value bound" principle, because we now care about the sign of the quantities rather than just the magnitude. For example, in an expression like (x - y + z) it is safe to omit range constraints on all the variables *if* it is known that (z ≤ y). 
 
**Gates that use application-specific information**

Another pattern that shows up are gates where it is safe to omit range constraints, but the reasoning requires propagating information from one part of the expression to another subexpression. For example, the zkWasm implemenatation of the ROTR instruction involves a constraint

```
(ops_BinShift * is_rotr * (res * lookup_pow_modulus - round * lookup_pow_modulus - rem * size_modulus)) mod p = 0
```
There is no type-constraint on the `size_modulus` column, and in isolation there is no way to know that the inner expression does not wrap around. However, there are other gate-constraints that force this column to be a 64-bit number. Those other constraints are only active if the `ops_BinShift` bit is enabled. There are two consequences. First, we need a new reasoning principle to propagate information across multiplications:

```coq
Lemma moddable_mul' : forall x y ,
    moddable x -> (x<>0 -> moddable y) -> moddable (x*y).
```
Second, we can't hope to do these proofs completely automatically. The programmer will need to manually prove a lemma about the range of the `size_modulus` column, and then manually invoke that lemma in the proof about the gate. 

**Gates that involve intentional wraparound**

By contrast, there are not many examples of gates where the programmer really intended the equation to be over a finite field and not over integers in general. The main idiom that comes up is to assert that a given variable is nonzero by saying that it has a multiplicative inverse. There is one example in the unary operations, with the equation `(operand*operand_inv - 1 + operand_is_zero) mod p = 0`. Here, the actual property that is needed for the rest of the proof is that "if `operand_is_zero`=0 then `operand`≠0", and this can be proven easily from the equation as given, but modulo operation is needed in the equation.

### Evaluation

We try the modulo-*p* tactics on four groups of equations from the zkWasm zkVM: `MTable` (memory representation, 29 equations grouped into 16 "gates"), `OpBinShift` (left- and right-shift instructions, 18 equations grouped into 14 gates), `OpUnary` (unary arithmetic instructions, 16 equations grouped into 6 gates), and `OpStore` (the memory STORE instruction,  19 equations grouped into 15 gates).

Of these, 72 out of the 82 equations (88%) can be reduced to integer equations using our tactics. 


| Module    | Equations | Inverse idiom | Tricky optimization| Successful |
|-----------|-----------|---------------|--------------------|------------|
| MTable    | 29        | 1             | 0                  | 28/29      |
| BinShift  | 18        | 0             | 2                  | 16/18      |
| Unary     | 16        | 1             | 0                  | 15/16      |
| Store     | 19        | 0             | 6                  | 13/19      |
| total     | 82        | 2             | 8                  | 72/82      |

This record is sufficiently encouraging that we believe this application-specific approach is practical. Further, note that 8 of the 10 equations that our tactics failed to handle used unlimited (untyped) columns as an optimization. They are not intended to actually wrap around, rather they are optimizing the number of constraints by leaving one variable in the expression unlimited. This makes it harder to reason about, but this presents a tradeoff between performance and ease of reasoning: the programmer *could* have added more type annotations to make these tactics work better.

## Using the Tactics

The repository is divided into our framework for modelling Halo2 applications (`Shared.v`, `CommonModel.v`), the lemmas about injectivity (`IntegerFunctions.v`, `InjectivityHelper.v`), the tactics for simplifying gates modulo-*p* (`Moddable.v`), and the evaluation examples from the zkWasm development (the `zkWasm` subdirectory).

To use the modulo-*p* tactics for your own development, the steps are as follows. First, define the columns of the table of interest (see `zkWasm/MTableModel.v` for an example, or `zkWasm/ETableModel.v` for a larger table). Then translate the Halo2 gates into Rocq axioms using the `pgate` function (again, see `zkWasm/MTableModel.v`).

In order to make use of the type-column information, you also need to add a few lemmas to the moddable database. In our example, this is done in the `zkWasm/ModdableETable.v` file. These are routine lemmas such as:

```coq
Lemma etable_isbit_bounded : forall c i,
    isbit c ->
      0 <= etable_values c i < 2.
Proof.
  intros c i Hbit.
  unfold isbit in Hbit.
  pose proof (Hbit i) as [H | H]; rewrite H; simpl; lia.
Qed.
```

These need to be stated separately for each table, because the table-column argument `c` has different types.

Then the per-gate proofs are done using the `pgate_to_gate` function. For example, the `zkWasm/MTableModel.v` file contains an axiom `pgate_mc3`, and the following definition (in `zkWasm/MTableGates.v`) converts it into a definition `gate_mc3` with the same equations stated over ℤ instead of ℤ/p:

```coq
Program Definition gate_mc3 := pgate_to_gate _ pgate_mc3.
Next Obligation.
  repeat (split; auto).
  - eauto 25 with moddable.
  - eauto 25 with moddable.
Qed.
```

This invocation creates one subgoal for each equation in the gate, asking the user to show that the equation is “moddable.” For simple cases (as above), they can be solved in a single line using the moddable hint database that we provide. For more complicated cases, the user can prove them manually.

## Compiling the evaluation examples

The examples we evaluate the tactics on are based on our verification of zkWasm, so compiling the project uses the same steps as that repo. The easiest is via [opam](https://opam.ocaml.org/).

First install Coq 8.17.1. 

```shell
opam install coq=8.17.1
```

Then download WasmCert (check out the specific version we used) and install it.

```shell
git clone git@github.com:WasmCert/WasmCert-Coq.git
cd WasmCert-Coq; git checkout 3977eda9994a257dfd46e2904e0130504322e9e8
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
```

The other two dependencies are:

```shell
opam install coq-mathcomp-zify coq-mathcomp-algebra-tactics
```

Finally, this repo can be compiled by

```shell
cd src
make
```