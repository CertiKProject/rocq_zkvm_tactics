(* Copyright (C) 2025 CertiK. *)

Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Wasm.numerics.

Require Import Shared.

Definition Z_of_bool (b: bool) : Z :=
  match b with
    | true => 1
    | false => 0
  end.


Definition Z_of_bool_opp (b: bool) : Z :=
  match b with
    | true => 0
    | false => 1
  end.

(* Same definition as in WasmCert *)
Definition popcnt (x: Z) :=
  (Z.of_nat
     (seq.count (fun b : eqtype.Equality.sort eqtype.bool_eqType => eqtype.eq_op b true)
        (Wasm_int.Int64.power_index_to_bits Wasm_int.Int64.wordsize
           (Zbits.Z_one_bits Wasm_int.Int64.wordsize x 0)))).

Lemma lor_xI:
  forall x,
  Z.pos x~1 = Z.lor (Z.pos x * 2) 1.
Proof.
  intros.
  replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
  assert (Z.land (Z.pos x * 2) 1 = 0) as Hxor.
  {
    replace 2 with (2 ^ 1) by reflexivity.
    rewrite <- Z.shiftl_mul_pow2; [|lia].
    Z.bitwise.
    reflexivity.
  }
  rewrite Z.add_nocarry_lxor; [|assumption].
  rewrite Z.lxor_lor; [|assumption].
  reflexivity.
Qed.

Lemma lor_xO:
  forall x,
  Z.pos x~0 = Z.pos x * 2.
Proof.
  intros. lia.
Qed.

Lemma testbit_xI':
  forall (x: positive) (i: Z) b,
    0 <= i ->
    Z.testbit (Z.pos x) i = b ->
    Z.testbit (Z.pos x~1) (i + 1) = b /\
    Z.testbit (Z.pos x~1) 0 = true.
Proof.
  intros x i b Hi H.
  pose proof (lor_xI x) as Hdecomp.
  split.
  - rewrite Hdecomp.
    rewrite Z.lor_spec.
    assert (i + 1 = 0 \/ i + 1 > 0) as [H'|H'] by lia.
    + lia.
    + replace 2 with (2 ^ 1) by lia.
      replace ((i + 1)) with (1 + i) by lia.
      rewrite Z.mul_pow2_bits_add; [|lia].
      rewrite H.
      replace (1) with (1 mod 2 ^ 1) at 1 by reflexivity.
      rewrite Z.mod_pow2_bits_high; [|lia].
      rewrite Bool.orb_false_r.
      reflexivity.
  - rewrite Hdecomp.
    rewrite Z.lor_spec.
    assert (Z.testbit 1 0 = true) as H1.
    {
      unfold Z.testbit.
      reflexivity.
    }
    rewrite H1.
    rewrite Bool.orb_true_r.
    reflexivity.
Qed.

Lemma testbit_xI:
  forall (x: positive) (i: Z),
    0 <= i ->
    Z.testbit (Z.pos x~1) (i + 1) = Z.testbit (Z.pos x) i.
Proof.
  intros until i. intros Hi.
  remember (Z.testbit (Z.pos x) i) as b. symmetry in Heqb.
  apply testbit_xI' in Heqb; [|assumption].
  destruct Heqb as [H _].
  assumption.
Qed.

Lemma testbit_xI'':
  forall (x: positive) (i: Z),
    1 <= i ->
    Z.testbit (Z.pos x~1) i = Z.testbit (Z.pos x) (i - 1).
Proof.
  intros until i. intros Hi.
  assert (i = i - 1 + 1) as H by lia.
  rewrite H.
  rewrite testbit_xI; [|lia].
  replace ((i - 1 + 1 - 1)) with (i - 1) by lia.
  reflexivity.
Qed.

Lemma testbit_xI_0:
  forall x,
  Z.testbit (Z.pos x~1) 0 = true.
Proof.
  intros.
  pose proof (lor_xI x) as Hdecomp.
  rewrite Hdecomp.
  rewrite Z.lor_spec.
  assert (Z.testbit 1 0 = true) as H1 by (unfold Z.testbit; reflexivity).
  rewrite H1.
  rewrite Bool.orb_true_r.
  reflexivity.
Qed.

Lemma testbit_xO':
  forall (x: positive) (i: Z) b,
    0 <= i ->
    Z.testbit (Z.pos x) i = b ->
    Z.testbit (Z.pos x~0) (i + 1) = b /\
    Z.testbit (Z.pos x~0) 0 = false.
Proof.
  intros until b. intros Hi Hb.
  assert (Z.pos x~0 = Z.pos x * 2) as Hdecomp by lia.
  rewrite Hdecomp.
  split.
  - replace 2 with (2 ^ 1) by lia.
    replace (i + 1) with (1 + i) by lia.
    rewrite Z.mul_pow2_bits_add; [|lia].
    assumption.
  - replace 2 with (2 ^ 1) by lia.
    rewrite Z.mul_pow2_bits_low; [|lia].
    reflexivity.
Qed.  

Lemma testbit_xO:
  forall (x: positive) (i: Z),
    0 <= i ->
    Z.testbit (Z.pos x~0) (i + 1) = Z.testbit (Z.pos x) i.
Proof.
  intros until i. intros Hi.
  remember (Z.testbit (Z.pos x) i) as b. symmetry in Heqb.
  apply testbit_xO' in Heqb; [|assumption].
  destruct Heqb as [H _].
  assumption.
Qed.

Lemma testbit_xO'':
  forall (x: positive) (i: Z),
    1 <= i ->
    Z.testbit (Z.pos x~0) i = Z.testbit (Z.pos x) (i - 1).
Proof.
  intros until i. intros Hi.
  assert (i = i - 1 + 1) as H by lia.
  rewrite H.
  rewrite testbit_xO; [|lia].
  replace ((i - 1 + 1 - 1)) with (i - 1) by lia.
  reflexivity.
Qed.

Lemma testbit_xO_0:
  forall x,
  Z.testbit (Z.pos x~0) 0 = false.
Proof.
  intros.
  pose proof (lor_xO x) as Hdecomp.
  rewrite Hdecomp.
  replace 2 with (2 ^ 1) by lia.
  rewrite Z.mul_pow2_bits_low; [|lia].
  reflexivity.
Qed.

Lemma xI_bound: forall x n,
  0 <= n ->
  0 <= Z.pos x < 2^n -> 0 <= Z.pos x~1 < 2^(n + 1).
Proof.
  intros x n Hn Hx.
  split; [lia|].
  replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
  assert (Z.pos x * 2 < 2 ^ n * 2) as Hx' by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r.
  lia.
Qed.

Lemma xO_bound: forall x n,
  0 <= n ->
  0 <= Z.pos x < 2^n -> 0 <= Z.pos x~0 < 2^(n + 1).
Proof.
  intros x n Hn Hx.
  split; [lia|].
  replace (Z.pos x~0) with (Z.pos x * 2) by lia.
  assert (Z.pos x * 2 < 2 ^ n * 2) as Hx' by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r.
  lia.
Qed.

Lemma bound_spec_n_l : forall x n,
  0 <= n ->
  0 <= x < 2^n -> (forall k,  n <= k -> Z.testbit x k = false).
Proof.
  destruct x as [|x|x].
  - intros n Hn H k Hk. rewrite Z.bits_0. reflexivity.
  - induction x.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        lia.
      * rewrite testbit_xI''; [|lia].
        assert (0 <= n - 1) as Hn'' by lia.
        assert (0 <= Z.pos x < 2 ^ (n - 1)) as Hx'.
        {
          split; [lia|].
          replace (Z.pos x~1) with (Z.pos x * 2 + 1) in Hx by lia.
          assert (Z.pos x * 2 < 2 ^ n) as Hx'' by lia.
          replace (n) with (n - 1 + 1) in Hx'' by lia.
          rewrite Z.pow_add_r in Hx''; [|lia|lia].
          rewrite Z.pow_1_r in Hx''.
          lia.
        }
        eapply (IHx (n - 1) Hn'' Hx' (k - 1)); try eassumption.
        lia.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        lia.
      * rewrite testbit_xO''; [|lia].
        assert (0 <= n - 1) as Hn'' by lia.
        assert (0 <= Z.pos x < 2 ^ (n - 1)) as Hx'.
        {
          split; [lia|].
          replace (Z.pos x~0) with (Z.pos x * 2) in Hx by lia.
          assert (Z.pos x * 2 < 2 ^ n) as Hx'' by lia.
          replace (n) with (n - 1 + 1) in Hx'' by lia.
          rewrite Z.pow_add_r in Hx''; [|lia|lia].
          rewrite Z.pow_1_r in Hx''.
          lia.
        }
        eapply (IHx (n - 1) Hn'' Hx' (k - 1)); try eassumption.
        lia.
    + intros n Hn Hx k Hk.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n. lia.
      * rewrite Z.bits_above_log2; [reflexivity|lia|].
        simpl. lia.
  - lia.
Qed.

Lemma negb_false_inv:
  forall b,
  negb b = false -> b = true.
Proof. intros. destruct b; auto. Qed.

Lemma negb_true_inv:
  forall b,
  negb b = true -> b = false.
Proof. intros. destruct b; auto. Qed.

Lemma testbit_Zneg_true':
  forall x,
    exists n, forall k, n < k -> Z.testbit (Z.neg x) k = true.
Proof.
  intros x.
  pose proof (Z.bits_iff_neg_ex (Z.neg x)) as H.
  assert (Z.neg x < 0) as Hx by lia.
  apply H in Hx.
  eapply Hx.
Qed.

Lemma testbit_Zneg_true:
  forall x,
    exists n, forall k, n <= k -> Z.testbit (Z.neg x) k = true.
Proof.
  intros x.
  pose proof (testbit_Zneg_true' x) as H.
  destruct H as [n H].
  exists (n + 1).
  intros k Hk.
  apply H.
  lia.
Qed.

Lemma testbit_Zneg_true_n:
  forall x,
    exists n, Z.testbit (Z.neg x) n = true.
Proof.
  intros x.
  pose proof (testbit_Zneg_true x) as H.
  destruct H as [n H].
  exists n.
  apply H.
  lia.
Qed.

Lemma zero_spec:
  forall x,
    (forall n, 0 <= n -> Z.testbit x n = false) ->
    x = 0.
Proof.
  intros x H.
  Z.bitwise.
  apply (H m).
  assumption.
Qed.

Lemma one_spec:
  Z.testbit 1 0 = true.
Proof. reflexivity. Qed.

Lemma bound_spec_n_r : forall x n,
  0 <= n ->
  0 <= x ->
  (forall k,  n <= k -> Z.testbit x k = false) -> 0 <= x < 2^n.
Proof.
  destruct x as [|x|x].
  - intros n Hn Hx H. lia.
  - induction x.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        specialize (H 0).
        rewrite testbit_xI_0 in H.
        discriminate H; reflexivity.
      * split; [lia|].
        replace (Z.pos x~1) with (Z.pos x * 2 + 1) by lia.
        replace (n) with (n - 1 + 1) by lia.
        replace (2 ^ (n - 1 + 1)) with (2 ^ (n - 1) * 2) by (rewrite Z.pow_add_r; lia).
        assert (Z.pos x * 2 < 2 ^ (n - 1) * 2) as H'.
        {
          apply Z.mul_lt_mono_pos_r; [lia|].
          eapply (IHx (n - 1)); [lia|lia|].
          intros k Hk.
          specialize (H (k + 1)).
          rewrite testbit_xI in H; [|lia].
          apply H.
          lia.
        }
        lia.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n.
        assert (Z.pos x~0 = 0) as Hx'.
        {
          apply zero_spec in H. assumption.
        }
        rewrite Hx'. lia.
      * split; [lia|].
        replace (Z.pos x~0) with (Z.pos x * 2) by lia.
        replace (n) with (n - 1 + 1) by lia.
        replace (2 ^ (n - 1 + 1)) with (2 ^ (n - 1) * 2) by (rewrite Z.pow_add_r; lia).
        apply Z.mul_lt_mono_pos_r; [lia|].
        eapply (IHx (n - 1)); [lia|lia|].
        intros k Hk.
        specialize (H (k + 1)).
        rewrite testbit_xO in H; [|lia].
        apply H.
        lia.
    + intros n Hn Hx H.
      assert (n = 0 \/ n > 0) as [Hn'|Hn'] by lia.
      * subst n. specialize (H 0).
        rewrite one_spec in H.
        discriminate H.
        reflexivity.
      * replace 1 with (1 ^ n) by (apply Z.pow_1_l; lia).
        split; [lia|].
        apply Z.pow_lt_mono_l; lia.
  - lia.
Qed.


Lemma bound_spec_n : forall x n,
  0 <= n ->
  0 <= x ->
  0 <= x < 2^n <-> (forall k,  n <= k -> Z.testbit x k = false).
Proof.
  split.
  - eapply bound_spec_n_l; eauto.
  - eapply bound_spec_n_r; eauto.
Qed.

Lemma bound_spec : forall x,
  0 <= x ->
  0 <= x < 256 <-> (forall k,  8 <= k -> Z.testbit x k = false).
Proof.
  intros x Hx.
  eapply (bound_spec_n x 8); eauto.
  lia.
Qed.

Lemma lor_bound_r:
  forall n m x y,
    0 <= n <= m ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ m ->
    0 <= Z.lor x y < 2 ^ m.
Proof.
  intros until y.
  intros Hnm Hx Hy.
  generalize Hx Hy.
  do 2 (rewrite bound_spec_n; [|lia|lia]).
  rewrite bound_spec_n; [|lia|].
  intros Hx' Hy' i Hi.
  rewrite Z.lor_spec.
  specialize (Hx' i).
  specialize (Hy' i).
  rewrite Hx'; [|lia].
  rewrite Hy'; [|lia].
  lia.
  apply Z.lor_nonneg.
  split; lia.
Qed.


Lemma plus_lor_helper_n : forall n a b,
    0 <= n ->
    0 <= a < 2^n ->
    Z.land a (Z.shiftl b n) = 0.
Proof.
  intros n a b nbound abound.
  apply Zbits.equal_same_bits. intros k kbound.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  destruct (Z.lt_decidable k n) as [H|H].
  - rewrite Z.shiftl_spec_low by auto.
    rewrite Bool.andb_false_r.
    reflexivity.
  - pose proof (bound_spec_n a n) as Ha.
    destruct Ha as [Ha _]. lia. lia.
    rewrite Ha by lia.
    rewrite Bool.andb_false_l.
    reflexivity.
Qed.   

Lemma plus_lor_n : forall n a b,
    0 <= n ->
    0 <= a < 2^n ->
    a + Z.shiftl b n = Z.lor a (Z.shiftl b n).
Proof.
  intros n a b nbound abound.
  rewrite Z.add_nocarry_lxor by (auto using plus_lor_helper_n).
  rewrite Z.lxor_lor by (auto using plus_lor_helper_n).
  reflexivity.
Qed.

