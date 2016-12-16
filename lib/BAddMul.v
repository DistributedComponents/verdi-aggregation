Require Export Bvector ZArith Zdigits.
Require Import Program.Equality Znumtheory.
Require Import BBase.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Set Strict Implicit.

(* <add, mul> ring *)

Lemma add_0_l :
  forall n (v : Bvector n), add (zero n) v = v.
Proof.
  intros.
  unfold add, zero.
  rewrite Z_to_binary_to_Z; firstorder.
  apply binary_to_Z_to_binary.
Qed.

Lemma add_comm :
  forall n (a b : Bvector n), add a b = add b a.
Proof.
  intros.
  unfold add.
  f_equal.
  lia.
Qed.

Lemma add_assoc :
  forall n (a b c : Bvector n), add a (add b c) = add (add a b) c.
Proof.
  intros.
  unfold add.
  apply Z_to_binary_eqm.
  repeat rewrite Z_to_binary_to_Z_mod.
  unfold eqm.
  rewrite Zplus_mod_idemp_l.
  rewrite Zplus_mod_idemp_r.
  f_equal.
  lia.
Qed.

Lemma mul_1_l :
  forall n (v : Bvector n), mul (one n) v = v.
Proof.
  unfold mul, one.
  (* need to get rid of n = 0 first *)
  induction v as [| b n v'].
  constructor.
  rewrite Z_to_binary_to_Z; firstorder.
  rewrite Z.mul_1_l.
  apply binary_to_Z_to_binary.
Qed.

Lemma mul_comm :
  forall n (a b : Bvector n), mul a b = mul b a.
Proof.
  intros.
  unfold mul.
  f_equal.
  ring.
Qed.

Lemma mul_assoc :
  forall n (a b c : Bvector n), mul a (mul b c) = mul (mul a b) c.
Proof.
  intros.
  unfold mul.
  apply Z_to_binary_eqm.
  repeat rewrite Z_to_binary_to_Z_mod.
  unfold eqm.
  rewrite Zmult_mod_idemp_l.
  rewrite Zmult_mod_idemp_r.
  f_equal.
  ring.
Qed.

Definition distr_l :
  forall n (a b c : Bvector n), mul (add a b) c = add (mul a c) (mul b c).
Proof.
  intros.
  unfold add, mul.
  apply Z_to_binary_eqm.
  repeat rewrite Z_to_binary_to_Z_mod.
  unfold eqm.
  rewrite Zmult_mod_idemp_l.
  rewrite <- Zplus_mod.
  f_equal.
  ring.
Qed.

Lemma sub_def :
  forall n (a b : Bvector n), sub a b = add a (opp b).
Proof.
  intros.
  unfold add, sub, opp.
  apply Z_to_binary_eqm.
  repeat rewrite Z_to_binary_to_Z_mod.
  unfold eqm.
  replace (- binary_value b) with (0 - binary_value b) by auto.
  rewrite Zplus_mod_idemp_r.
  f_equal.
Qed.

Lemma opp_def :
  forall n (v : Bvector n), add v (opp v) = zero n.
Proof.
  intros.
  rewrite <- sub_def.
  unfold sub, zero.
  f_equal.
  lia.
Qed.

Definition add_mul_ring n : ring_theory (zero n) (one n) (@add n) (@mul n) (@sub n) (@opp n) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
    (@add_0_l _) (@add_comm _) (@add_assoc _)
    (@mul_1_l _) (@mul_comm _) (@mul_assoc _)
    (@distr_l _) (@sub_def _) (@opp_def _).

(* move *)

Lemma Zminus_mod_eqm : forall a b c : Z,
  eqm c (a - b) 0 <-> eqm c a b.
Proof.
  unfold eqm; split; rewrite Zmod_0_l; intros H.
  - rewrite <- (Zminus_0_r a).
    rewrite <- H.
    rewrite Zminus_mod_idemp_r.
    f_equal.
    lia.
  - rewrite Zminus_mod.
    replace (a mod c - b mod c) with 0 by lia.
    apply Zmod_0_l.
Qed.

Lemma sub_move_0_r :
  forall n (a b : Bvector n), sub a b = zero n <-> a = b.
Proof.
  split; intros H.
  - apply binary_value_eq.
    unfold sub, zero in H.
    rewrite <- Z_to_binary_eqm in H.
    rewrite Zminus_mod_eqm in H.
    unfold eqm in H.
    pose proof (binary_value_pos_bound a).
    pose proof (binary_value_pos_bound b).
    rewrite (Zmod_small (_ a)), (Zmod_small (_ b)) in H; firstorder.
  - rewrite sub_def.
    subst.
    apply opp_def.
Qed.
