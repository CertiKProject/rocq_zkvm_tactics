(* Copyright (C) 2025 CertiK. *)

Require Import ZArith.
Require Import Shared.
Require Import CommonModel.

Require Import Lia.

Open Scope Z_scope.

Require Import ZArith.Znumtheory.
Require Import Wasm.numerics.

Definition moddable (x:Z) :=
  x mod field_order = 0 -> x = 0.

Lemma moddable_spec : forall e,
    e mod field_order = 0 -> moddable e -> e = 0.
Proof.
  unfold moddable; tauto.
Qed.  

Lemma prime_nonzero : forall {x} ,  prime x -> x<>0.
Proof. inversion 1. lia. Qed.

Lemma field_order_positive : 0 < field_order.
Proof. pose  int_lt_order. lia. Qed.
  
Lemma integral_domain : forall x y,
    (x*y) mod field_order = 0 ->
    (x mod field_order = 0) \/ (y mod field_order = 0).
Proof.
  intros x y H.
  apply (Zmod_divide (x*y) field_order (prime_nonzero field_order_prime)) in H.
  apply  (prime_mult _ field_order_prime) in H.
  destruct H as [H|H]; apply Zdivide_mod in H; auto.
Qed.

Lemma moddable_mul' : forall x y ,
    moddable x -> (x<>0 -> moddable y) -> moddable (x*y).
Proof.
  intros x y Hx Hy Heq.  
  apply integral_domain in Heq.
  destruct Heq as [Heq | Heq].
  - apply Hx in Heq. lia.
  - destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
    + lia.
    apply (Hy Hx0) in Heq. lia.
Qed.

Lemma moddable_mul : forall x y ,
    moddable x -> moddable y -> moddable (x*y).
Proof.
  intros x y.
  pose (moddable_mul' x y).
  tauto.
Qed.

Lemma moddable_absbounded : forall x,
    0 <= Z.abs x < field_order ->
    moddable x.
Proof.
  intros x Hx H.
  destruct (Z_lt_ge_dec x 0).
  - rewrite Z.abs_neq in Hx by lia .
    apply Z_mod_zero_opp in H.
    2: {
      destruct field_order_prime. lia.
    }
    rewrite Zmod_small in H by lia.
    lia.
  - rewrite Z.abs_eq in Hx by lia.
    rewrite Zmod_small in H by lia.
    lia.
Qed.

Lemma bounded_absbounded : forall x b,
    0 <= x < b ->
    0 <= Z.abs x < b.
Proof.
  intros x b H.
  split.
  - lia.
  - apply Z.abs_lt; lia.
Qed.    

Lemma moddable_bounded : forall x,
    0 <= x < field_order ->
    moddable x.
Proof.
  intros.
  eauto using moddable_absbounded, bounded_absbounded.
Qed.

Lemma moddable_sub : forall x y,
    0 <= x < field_order ->
    0 <= y < field_order ->
    moddable (x-y).
Proof.
  intros x y Hx Hy.
  apply moddable_absbounded.
  lia.
Qed.

Lemma field_order_big : 411376139330301510538742295639337626245683966408394965837152256 < field_order.
Proof.
  exact CommonModel.encode_instruction_table_entry_field_order.
Qed.


Lemma common_small :  262144 <= common < 4294967296.
Proof.
  split.
  exact  eighteen_le_common. exact common_le_2_32.
Qed.

Lemma one_bit_bounded : forall x,
    0 <= Z.abs x < 2 ->
    0 <= Z.abs x < field_order.
Proof. pose field_order_big; lia. Qed.

Lemma two_bits_bounded : forall x y,
    0 <= x < 2 ->
    0 <= y < 2 ->
    0 <= x + y < field_order.
Proof. pose field_order_big; lia. Qed.

Lemma three_bits_bounded : forall x y z,
    0 <= x < 2 ->
    0 <= y < 2 ->
    0 <= z < 2 ->
    0 <= x + y + z < field_order.
Proof. pose field_order_big; lia. Qed.

Lemma four_bits_bounded : forall x y z w,
    0 <= x < 2 ->
    0 <= y < 2 ->
    0 <= z < 2 ->
    0 <= w < 2 ->
    0 <= x + y + z + w < field_order.
Proof. pose field_order_big; lia. Qed.

Lemma bit_and_bound : forall b x y,
    0 <=  x < 2 ->
    0 <= y < b ->
    0 <= (x*y) < b.
Proof.
  intros.
  destruct (Z_lt_ge_dec x 1).
  - replace x with 0 by lia; lia.
  - replace x with 1 by lia; lia.
Qed.

Lemma and_bit_bound : forall b x y,
    0 <=  x < b ->
    0 <=  y < 2 ->
    0 <=  (x*y) < b.
Proof.
  intros.
  destruct (Z_lt_ge_dec y 1).
  - replace y with 0 by lia; lia.
  - replace y with 1 by lia; lia.
Qed.

Lemma common_bounded : forall x,
    0 <= x < common ->
    0 <= x < field_order.
Proof. pose field_order_big. pose common_small. lia. Qed.

  
Lemma two_common_bounded : forall x y,
    0 <= x < common ->
    0 <= y < common ->
    0 <= x + y < field_order.
Proof. pose field_order_big. pose common_small. lia. Qed.

Lemma three_common_bounded : forall x y z,
    0 <= x < common ->
    0 <= y < common ->
    0 <= z < common ->
    0 <= x + y + z < field_order.
Proof. pose field_order_big. pose common_small. lia. Qed.

Lemma four_common_bounded : forall x y z w,
    0 <= x < common ->
    0 <= y < common ->
    0 <= z < common ->
    0 <= w < common ->
    0 <= x + y + z + w < field_order.
Proof. pose field_order_big. pose common_small. lia. Qed.
  
Lemma five_common_bounded : forall x y z w v,
    0 <= x < common ->
    0 <= y < common ->
    0 <= z < common ->
    0 <= w < common ->
    0 <= v < common ->
    0 <= x + y + z + w + v < field_order.
Proof. pose field_order_big. pose common_small. lia. Qed.

Lemma bit_common : forall x,
    0 <= x < 2 ->
    0 <= x < common.
Proof. pose field_order_big. pose common_small. lia. Qed.


Lemma const_1_common :
  0 <= 1 < common.
Proof. pose field_order_big. pose common_small. lia. Qed.

Lemma u16_bounded : forall x,
    0 <= x < 2^16 ->
    0 <= x < field_order.
Proof.  pose field_order_big. lia. Qed.

Lemma two_u16_bounded : forall x y,
    0 <= x < 2^16 ->
    0 <= y < 2^16 ->
    0 <= x + y < field_order.
Proof.  pose field_order_big. lia. Qed.

Lemma three_u16_bounded : forall x y z,
    0 <= x < 2^16 ->
    0 <= y < 2^16 ->
    0 <= z < 2^16 ->
    0 <= x + y + z < field_order.
Proof.  pose field_order_big. lia. Qed.

Lemma four_u16_bounded : forall x y z w,
    0 <= x < 2^16 ->
    0 <= y < 2^16 ->
    0 <= z < 2^16 ->
    0 <= w < 2^16 ->
    0 <= x + y + z + w < field_order.
Proof. pose field_order_big. lia. Qed.

Lemma u64_bounded : forall x,
    0 <= x < 2^64 ->
    0 <= x < field_order.
Proof. pose field_order_big. lia. Qed.

#[global] Hint Resolve moddable_mul | 1 : moddable.
#[export] Hint Resolve one_bit_bounded bit_and_bound and_bit_bound bit_common const_1_common  : moddable.
                                                      
Lemma pgate_to_gate : forall {t : table} {exprs: (colNames t -> Z -> Z) -> list Z},
  (forall n, 0 <= n ->
             let es := exprs (fun c i => value t c ((n + i))) in
             ForallP (fun z =>  moddable z) es)
    -> pgate t exprs -> gate t exprs.
Proof.
  unfold pgate, gate.
  intros t exprs.
  intros Hbound Hgate n Hrange.
  specialize (Hbound n Hrange).
  specialize (Hgate n Hrange).
  revert Hbound Hgate.
  generalize (exprs (fun (c : colNames t) (i : Z) => value t c (n + i))) as es.
  induction es.
  - simpl. tauto.
  - simpl in *.
    intros [Hbound Hbound_rest] [Hgate Hgate_rest].
    split.
    +
      apply Hbound; auto.
    + apply IHes; eauto.
Qed.

Lemma abs_distr_add : forall x y b ,
    0 <= Z.abs x + Z.abs y < b ->
    0 <= Z.abs (x + y) < b.
Proof.
  intros.
  assert (e := Z.abs_triangle x y).
  lia.
Qed.
  
Lemma abs_distr_sub : forall x y b ,
    0 <= Z.abs x + Z.abs y < b ->
    0 <= Z.abs (x - y) < b.
  intros.
  assert (e := Z.abs_sub_triangle x y).
  lia.
Qed.

Lemma absbound_pppm: forall b x y z w,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs w < b ->
    0 <= Z.abs (x + y + z - w) < b.
Proof.
  intros.
  assert (e1 := Z.abs_sub_triangle (x+y+z) w).
  assert (e2 := Z.abs_triangle (x+y) z).
  assert (e3 := Z.abs_triangle x y).
  lia.
Qed.  

Lemma absbound_ppm: forall b x y z ,
    0 <= Z.abs x + Z.abs y + Z.abs z < b ->
    0 <= Z.abs (x + y - z ) < b.
Proof.
  intros.
  assert (e1 := Z.abs_sub_triangle (x+y) z).
  assert (e2 := Z.abs_triangle x y).
  lia.
Qed.  

Lemma absbound_pmmm: forall b x y z w,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs w < b ->
    0 <= Z.abs (x - y - z - w) < b.
Proof.
  intros.
  assert (e1 := Z.abs_sub_triangle (x-y-z) w).
  assert (e2 := Z.abs_sub_triangle (x-y) z).
  assert (e3 := Z.abs_sub_triangle x y).
  lia.
Qed.

Lemma absbound_pmmmm: forall b x y z w v,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs w + Z.abs v < b ->
    0 <= Z.abs (x - y - z - w - v) < b.
Proof.
  intros.
  replace (x - y - z - w - v) with (x - (y + z + w + v)) by lia.
  assert (e1 := Z.abs_sub_triangle x (y + z + w + v)).
  assert (e2 := Z.abs_triangle (y + z + w) v).
  assert (e3 := Z.abs_triangle (y + z) w).
  assert (e4 := Z.abs_triangle (y) z).
  lia.
Qed.

Lemma absbound_pmm: forall b x y z ,
    0 <= Z.abs x + Z.abs y + Z.abs z < b ->
    0 <= Z.abs (x - y - z ) < b.
Proof.
  intros.
  replace (x - y - z) with (x - (y + z)) by lia.
  assert (e1 := Z.abs_sub_triangle x (y + z)).
  assert (e2 := Z.abs_triangle y z).
  lia.
Qed.

Lemma moddable_pmm: forall x y z,
    0 <= x < field_order ->
    0 <=  y + z  < field_order ->
    moddable (x - y - z).
Proof.
  intros.
  replace (x - y - z) with (x - (y+z)) by lia.
  apply moddable_sub; lia.
Qed.


Lemma moddable_ppm: forall x y z,
    0 <= x + y < field_order ->
    0 <=  z  < field_order ->
    moddable (x + y - z).
Proof.
  intros.
  apply moddable_sub; lia.
Qed.
  
Lemma moddable_pm: forall x y,
    0 <= x < field_order ->
    0 <= y < field_order ->
    moddable (x - y).
Proof.
  apply moddable_sub; lia.
Qed.

Lemma absbound_ppmpm: forall b x y z v w,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs v + Z.abs w < b ->
    0 <= Z.abs (x - y - z + v - w) < b.
Proof.
  intros.
  assert (e1 := Z.abs_sub_triangle (x-y-z+v) w).
  assert (e2 := Z.abs_triangle (x-y-z) v).
  assert (e3 := Z.abs_sub_triangle (x -y) z).
  assert (e4 := Z.abs_sub_triangle (x) y).
  lia.
Qed.

Lemma absbound_ppmp: forall b x y z w,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs w < b ->
    0 <= Z.abs (x + y - z + w) < b.
Proof.
  intros.
  assert (e1 := Z.abs_triangle (x+y-z) w).
  assert (e2 := Z.abs_sub_triangle (x+y) z).
  assert (e3 := Z.abs_triangle x y).
  lia.
Qed.

Lemma absbound_pmp: forall b x y z,
    0 <= Z.abs x + Z.abs y + Z.abs z  < b ->
    0 <= Z.abs (x - y + z) < b.
Proof.
  intros.
  assert (e1 := Z.abs_triangle (x-y) z).
  assert (e2 := Z.abs_sub_triangle x y).
  lia.
Qed.

Lemma moddable_pmmm: forall x y z w,
    0 <= x < field_order ->
    0 <= y + z +  w < field_order ->
    moddable (x - y - z - w ).
Proof.
  intros.
  replace (x - y - z - w ) with (x - (y + z + w )) by lia.
  apply moddable_sub; auto.
Qed.

Lemma moddable_pmmmm: forall x y z w v,
    0 <= x < field_order ->
    0 <= y + z +  w + v < field_order ->
    moddable (x - y - z - w - v).
Proof.
  intros.
  replace (x - y - z - w - v) with (x - (y+z+w+v)) by lia.
  apply moddable_sub; lia.
Qed.

Lemma moddable_ppmm: forall x y z w,
    0 <= x + y < field_order ->
    0 <= z + w < field_order ->
    moddable (x + y - z - w).
Proof.
  intros.
  replace (x + y - z - w) with (x + y - (z + w)) by lia.
  apply moddable_sub; lia.
Qed.

Lemma moddable_pppm: forall x y z w,
    0 <= x + y + z < field_order ->
    0 <= w < field_order ->
    moddable (x + y + z - w).
Proof.
  intros.
  apply moddable_sub; lia.
Qed.

Lemma moddable_ppppm: forall x y z w v,
    0 <= x + y + z + w < field_order ->
    0 <= v < field_order ->
    moddable (x + y + z + w - v).
Proof.
  intros.
  apply moddable_sub; lia.
Qed.


#[export] Hint Resolve  two_bits_bounded  three_bits_bounded four_bits_bounded
common_bounded two_common_bounded  three_common_bounded four_common_bounded five_common_bounded
u16_bounded two_u16_bounded  three_u16_bounded four_u16_bounded u64_bounded
  : moddable.

Lemma minus_1_mod: -1 mod field_order <> 0.
Proof.
  intros H.
  pose (l := prime_ge_2 field_order field_order_prime).
  assert (H' := Z_mod_zero_opp (-1) field_order ltac:(lia) H).
  clear H.
  change (-(-1)) with 1 in *.
  rewrite Z.mod_1_l in H'; lia.
Qed.


(**** Constants **)

Lemma const_2_common :
  0 <= 2 < common.
Proof. pose common_small. lia. Qed.

Lemma const_3_common :
  0 <= 3 < common.
Proof. pose common_small. lia. Qed.

Lemma const_4_common :
  0 <= 4 < common.
Proof. pose common_small. lia. Qed.

Lemma const_5_common :
  0 <= 5 < common.
Proof. pose common_small. lia. Qed.

Lemma const_6_common :
  0 <= 6 < common.
Proof. pose common_small. lia. Qed.

Lemma const_7_common :
  0 <= 7 < common.
Proof. pose common_small. lia. Qed.

Lemma const_8_common :
  0 <= 8 < common.
Proof. pose common_small. lia. Qed.

Lemma const_9_common :
  0 <=  9 < common.
Proof. pose common_small. lia. Qed.

Lemma const_32_common :
  0 <= 32 < common.
Proof. pose common_small. lia. Qed.

Lemma const_64_common :
  0 <= 64 < common.
Proof. pose common_small. lia. Qed.

Lemma const_128_common :
  0 <= 128 < common.
Proof. pose common_small. lia. Qed.

Lemma const_32767_common :
  0 <= 32767 < common.
Proof. pose common_small. lia. Qed.

Lemma const_32768_common :
  0 <=  32768 < common.
Proof. pose common_small. lia. Qed.

#[global] Hint Resolve const_2_common const_3_common const_4_common const_5_common const_6_common const_7_common const_8_common const_9_common const_32_common const_64_common const_128_common const_32767_common const_32768_common : moddable.


Lemma u16_common : forall x,
    0 <= x < 2^16 ->
    0 <= x < common.
Proof. pose common_small. lia. Qed.

Lemma two_u16_common : forall x y,
    0 <= x < 2^16 ->
    0 <= y < 2^16 ->
    0 <= x+y < common.
Proof.  pose common_small. lia. Qed.

Lemma two_u64_bounded : forall x y,
    0 <= x < 2^64 ->
    0 <= y < 2^64 ->
    0 <= x + y < field_order.
Proof.  pose field_order_big. lia. Qed.

Lemma three_u64_bounded : forall x y z,
    0 <= x < 2^64 ->
    0 <= y < 2^64 ->
    0 <= z < 2^64 ->
    0 <= x + y + z < field_order.
Proof. pose field_order_big. lia. Qed.

Lemma const_1_u64 : 0 <= 1 < 2^64.
Proof. pose field_order_big. lia. Qed.

#[global] Hint Resolve u16_common two_u16_common two_u64_bounded three_u64_bounded : moddable.

Lemma u64_mul_u128_u192 : forall x y,
    0 <= x < 2^64 ->
    0 <= y < 2^128 ->
    0 <= (x*y) < 2^192.
Proof.
  intros.
  change (2^192) with (2^(64+128)).
  rewrite Z.pow_add_r by lia.
  split.
    lia.
    apply Zmult_lt_compat; lia.
Qed.
  
Lemma u192_bounded : forall x,
    0 <= x < 2^192 -> 0 <= x < field_order.
Proof.
  pose field_order_big. lia.
Qed.

Lemma u128_bounded : forall x,
    0 <= x < 2^128 -> 0 <= x < field_order.
Proof.
  pose field_order_big. lia.
Qed.

Lemma u128_bounded' : forall x,
    1 <= x < 2^128 -> 0 <= x < field_order.
Proof.
  pose field_order_big. lia.
Qed.

Lemma u64_plus_u192_bounded : forall x y,
      0 <= x < 2^64 ->
      0 <= y < 2^192 ->
      0 <= x+y < field_order.
Proof.
  intros.
  pose field_order_big.
  lia.
Qed.  

Lemma u64_plus_u192_plus_u64_bounded : forall x y z,
      0 <= x < 2^64 ->
      0 <= y < 2^192 ->
      0 <= z < 2^64 ->
      0 <= x+y+z < field_order.
Proof.
  intros.
  pose field_order_big.
  lia.
Qed.  

#[global] Hint Resolve const_1_u64 u128_bounded u128_bounded' u64_mul_u128_u192 u64_plus_u192_plus_u64_bounded u64_plus_u192_bounded u192_bounded : moddable.


Lemma common_u64 : forall x,
    0 <= x < common ->
    0 <= x < 2^64.
Proof.
  intros.
  change (2^64) with 18446744073709551616.  
  pose common_small.
  lia.
Qed.  

Lemma u8_u64 : forall x,
    0 <= x < 2^8 ->
    0 <= x < 2^64.
Proof. intros. lia. Qed.
  
Lemma absbound_ppp: forall b x y z,
    0 <= Z.abs x + Z.abs y + Z.abs z < b ->
    0 <= Z.abs (x + y + z) < b.
Proof.
  intros.
  assert (e2 := Z.abs_triangle (x+y) z).
  assert (e3 := Z.abs_triangle x y).
  lia.
Qed.

Lemma absbound_pppp: forall b x y z w,
    0 <= Z.abs x + Z.abs y + Z.abs z + Z.abs w < b ->
    0 <= Z.abs (x + y + z + w) < b.
Proof.
  intros.
  assert (e1 := Z.abs_triangle (x+y+z) w).
  assert (e2 := Z.abs_triangle (x+y) z).
  assert (e3 := Z.abs_triangle x y).
  lia.
Qed.  

Ltac moddable_by_difference :=
  match goal with
  | [|- moddable (_ - _ - _ - _ - _)] => apply moddable_pmmmm
  | [|- moddable (_ + _ + _ - _)] => apply moddable_pppm
  | [|- moddable (_ + _ - _ - _)] => apply moddable_ppmm
  | [|- moddable (_ - _ - _ - _)] => apply moddable_pmmm
  | [|- moddable (_ + _ - _)] => apply moddable_ppm
  | [|- moddable (_ - _ - _)] => apply moddable_pmm
  | [|- moddable (_ - _)] => apply moddable_pm
  end.

Ltac absbound_by_sum :=
  match goal with
  | [|- 0 <= Z.abs (_ + _ + _ + _) < _ ] => apply absbound_pppp
  | [|- 0 <= Z.abs (_ + _ + _ - _) < _ ] => apply absbound_pppm
  | [|- 0 <= Z.abs (_ + _ + _ - _) < _ ] => apply absbound_pppm
  | [|- 0 <= Z.abs (_ + _ - _ + _) < _ ] => apply absbound_ppmp
  | [|- 0 <= Z.abs (_ - _ - _ - _) < _ ] => apply absbound_pmmm
  | [|- 0 <= Z.abs (_ + _ + _) < _ ] => apply absbound_ppp
  | [|- 0 <= Z.abs (_ + _ - _) < _ ] => apply absbound_ppm
  | [|- 0 <= Z.abs (_ - _ + _) < _ ] => apply absbound_pmp
  | [|- 0 <= Z.abs (_ + _) < _ ] => apply abs_distr_add
  | [|- 0 <= Z.abs (_ - _) < _ ] => apply abs_distr_sub
  end.

#[global] Hint Resolve  absbound_pmmmm five_common_bounded : moddable.

#[global] Hint Extern 4 (moddable _) => moddable_by_difference : moddable.

#[global] Hint Resolve moddable_absbounded | 5 : moddable.

#[global] Hint Extern 4 (0 <= _ < _) => absbound_by_sum : moddable.

#[global] Hint Resolve const_2_common const_3_common const_4_common const_5_common const_6_common const_7_common const_8_common const_9_common : moddable. 

#[global] Hint Resolve abs_distr_sub : moddable.
#[global] Hint Resolve const_1_u64 : moddable.
#[global] Hint Resolve bounded_absbounded : moddable.
