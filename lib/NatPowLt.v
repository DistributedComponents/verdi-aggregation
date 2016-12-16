Require Import Omega.

Lemma lt_2xp1 : forall x i, i < x -> 1 + 2 * i < x + x.
Proof.
intros; omega.
Qed.

Lemma lt_2xp : forall x i : nat, i < x -> 2 * i < x + x.
Proof.
intros; omega.
Qed.

Lemma nat_pow_succ_r : forall n p : nat,
    n ^ (S p) = n * n ^ p.
Proof.
  auto.
Qed.

Lemma nat_mul_lt_cancel_l : forall k n m : nat,
    k <> 0 ->
    k * n < k * m ->
    n < m.
Proof.
  intros.
  apply Nat.div_lt_upper_bound in H0; try auto.
  rewrite Nat.mul_comm in H0.
  rewrite Nat.div_mul in H0; auto.
Qed.

Lemma lt_div2_2pow_even : forall n' m,
    2 * m < 2 ^ (S n') ->
    m < 2 ^ n'.
Proof.
  intros.
  apply nat_mul_lt_cancel_l with (k:=2); eauto.
Qed.

Lemma lt_div2_2pow : forall n' m,
    m < 2 ^ (S n') ->
    Nat.div2 m < 2 ^ n'.
Proof.
  intros.
  pose proof Nat.div2_odd m.
  destruct (Nat.odd m) eqn:?H;
    eapply lt_div2_2pow_even;
    omega.
Qed.
