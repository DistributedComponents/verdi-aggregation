Require Export Bvector ZArith Zdigits.
Require Import Program.Equality Znumtheory.
Require Export BDef.
Require Import Program.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Set Strict Implicit.

(* useful for b2z lemmas in Zbits *)
Lemma bit_value_b2z :
  forall b, bit_value b = Z.b2z b.
Proof.
  destruct b; auto.
Qed.

Lemma bit_value_eq :
  forall b1 b2, bit_value b1 = bit_value b2 -> b1 = b2.
Proof.
  intros.
  apply Z.b2z_inj.
  generalize (bit_value_b2z b1) (bit_value_b2z b2).
  tauto.
Qed.

Lemma binary_value_eq :
  forall n (v1 v2 : Bvector n), binary_value v1 = binary_value v2 -> v1 = v2.
Proof.
  refine (@Vector.rect2 _ _ _ _ _); auto.
  intros ? ? ? H b1 b2 IH.
  repeat rewrite binary_value_Sn in *.
  assert (v1 = v2).
  destruct b1, b2; unfold bit_value in *; firstorder.
  subst v2.
  rewrite Z.add_cancel_r in *.
  f_equal.
  now apply bit_value_eq.
Qed.

Lemma binary_value_bound :
  forall n (v : Bvector n), binary_value v < two_power_nat n.
Proof.
  induction v as [| b n v' IHv].
  - firstorder.
  - rewrite two_power_nat_S.
    rewrite binary_value_Sn.
    destruct b; unfold bit_value; lia.
Qed.

Lemma binary_value_pos_bound :
  forall n (v : Bvector n), 0 <= binary_value v < two_power_nat n.
Proof.
  split.
  generalize (binary_value_pos n v); firstorder.
  apply binary_value_bound.
Qed.

Lemma two_power_nat_le_mono : forall (a b : nat),
  (a <= b)%nat -> two_power_nat a <= two_power_nat b.
Proof.
  intros.
  repeat rewrite two_power_nat_equiv.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma binary_value_mod_lt : forall m n (v : Bvector n),
  (n <= m)% nat ->
  binary_value v = (binary_value v) mod (two_power_nat m).
Proof.
  intros.
  apply eq_sym.
  apply Zmod_small.
  pose proof (binary_value_pos_bound v).
  firstorder.
  apply Z.lt_le_trans with (m:=two_power_nat n); auto.
  apply two_power_nat_le_mono.
  lia.
Qed.

Lemma binary_value_mod : forall n (v : Bvector n),
  binary_value v = (binary_value v) mod (two_power_nat n).
Proof.
  intros.
  now apply binary_value_mod_lt.
Qed.

(* signed representation *)

Lemma msb_Sn : forall n (v : Bvector (S n)) h,
  msb (h :: v) = msb v.
Proof.
  intros.
  unfold msb, testbit.
  rewrite binary_value_Sn.
  rewrite <- (Z.testbit_succ_r (binary_value v) h _); try lia.
  rewrite bit_value_b2z.
  f_equal; zify; lia.
Qed.

Lemma binary_value_range_msb_0 : forall n (v : Bvector (S n)),
  msb v = false -> binary_value v < two_power_nat n.
Proof.
  dependent destruction v.
  revert h.
  induction v as [| a n v' IHv]; intros.
  destruct h; firstorder; inversion H.
  rewrite msb_Sn, binary_value_Sn, two_power_nat_S in *.
  generalize (IHv h).
  destruct h; unfold bit_value; firstorder.
Qed.

Lemma binary_value_range_msb_1 : forall n (v : Bvector (S n)),
  msb v = true -> two_power_nat n <= binary_value v.
Proof.
  dependent destruction v.
  revert h.
  induction v as [| a n v' IHv]; intros.
  destruct h; firstorder.
  rewrite msb_Sn, binary_value_Sn, two_power_nat_S in *.
  destruct h; unfold bit_value; firstorder.
Qed.

Lemma two_compl_value_binary_value_msb_0 : forall n (v : Bvector (S n)),
  msb v = false -> two_compl_value v = binary_value v.
Proof.
  dependent destruction v.
  revert h.
  induction v as [| a n v' IHv]; intros.
  destruct h; firstorder; inversion H.
  repeat rewrite two_compl_value_Sn, binary_value_Sn.
  rewrite msb_Sn in *.
  generalize (IHv a).
  destruct h; unfold bit_value; firstorder.
Qed.

Lemma two_compl_value_binary_value_msb_1 : forall n (v : Bvector (S n)),
  msb v = true -> two_compl_value v = binary_value v - two_power_nat (S n).
Proof.
  dependent destruction v.
  revert h.
  induction v as [| a n v' IHv]; intros.
  destruct h; firstorder; inversion H.
  rewrite msb_Sn in *.
  generalize (IHv a).
  repeat rewrite binary_value_Sn.
  repeat rewrite two_power_nat_S.
  rewrite two_compl_value_Sn.
  destruct h; unfold bit_value; firstorder.
Qed.

Lemma two_compl_value_range_msb_0 : forall n (v : Bvector (S n)),
  msb v = false -> 0 <= two_compl_value v < two_power_nat n.
Proof.
  intros.
  generalize (two_compl_value_binary_value_msb_0 v).
  generalize (binary_value_range_msb_0 v).
  generalize (binary_value_pos_bound v).
  rewrite two_power_nat_S.
  firstorder.
Qed.

Lemma two_compl_value_range_msb_1 : forall n (v : Bvector (S n)),
  msb v = true -> - (two_power_nat n) <= two_compl_value v < 0.
Proof.
  intros.
  generalize (two_compl_value_binary_value_msb_1 v).
  generalize (binary_value_range_msb_1 v).
  generalize (binary_value_pos_bound v).
  rewrite two_power_nat_S.
  firstorder.
Qed.

Lemma two_compl_value_range : forall n (v : Bvector (S n)),
  - (two_power_nat n) <= two_compl_value v < two_power_nat n.
Proof.
  intros.
  destruct (sumbool_of_bool (msb v));
  generalize (two_compl_value_range_msb_0 v);
  generalize (two_compl_value_range_msb_1 v);
  firstorder.
Qed.

Lemma Zmod_add :
  forall a b c : Z, (a + b * c) mod c = a mod c.
Proof.
  intros.
  destruct (Z.eq_dec c 0).
  - f_equal.
    subst.
    lia.
  - now apply Z.mod_add.
Qed.

Lemma two_compl_value_mod : forall n (v : Bvector (S n)),
  binary_value v = (two_compl_value v) mod (two_power_nat (S n)).
Proof.
  intros.
  destruct (sumbool_of_bool (msb v)).
  - rewrite two_compl_value_binary_value_msb_1; auto.
    rewrite <- Z.add_opp_r.
    rewrite (Zmod_add _ (-1) _).
    apply binary_value_mod.
  - rewrite two_compl_value_binary_value_msb_0; auto.
    apply binary_value_mod.
Qed.

Lemma two_compl_value_binary_value_eqm : forall n (v : Bvector (S n)),
  eqm (two_power_nat (S n)) (two_compl_value v) (binary_value v).
Proof.
  intros.
  unfold eqm.
  rewrite <- two_compl_value_mod.
  apply binary_value_mod.
Qed.

Lemma Z_to_binary_mod :
  forall (n:nat) (z:Z),
  Z_to_binary n z = Z_to_binary n (z mod two_power_nat n).
Proof.
  induction n as [| n IHn]; simpl; auto.
  intros.
  (* normalize *)
  rewrite two_power_nat_equiv in *.
  repeat rewrite Z.div2_div.
  f_equal.
  - repeat rewrite <- Z.bit0_odd.
    rewrite Z.mod_pow2_bits_low; firstorder.
  - rewrite IHn.
    f_equal.
    apply Z.bits_inj'.
    unfold Z.eqf; intros i Hi.
    rewrite Z.div2_bits; auto.
    (* high bits are all 0s *)
    destruct (Z.lt_ge_cases i (Z.of_nat n)).
    + repeat rewrite Z.mod_pow2_bits_low; zify; firstorder.
      apply Z.div2_bits; auto.
    + repeat rewrite Z.mod_pow2_bits_high; zify; firstorder.
Qed.

Lemma Z_to_binary_to_Z_mod :
  forall n z, binary_value (Z_to_binary n z) = z mod two_power_nat n.
Proof.
  intros.
  rewrite Z_to_binary_mod.
  apply Z_to_binary_to_Z; generalize (Z_mod_lt z (two_power_nat n)); firstorder.
Qed.

Lemma Z_to_binary_eqm :
  forall n x y, eqm (two_power_nat n) x y <-> Z_to_binary n x =  Z_to_binary n y.
Proof.
  split; intros H.
  - rewrite Z_to_binary_mod.
    rewrite H.
    rewrite <- Z_to_binary_mod.
    trivial.
  - assert (binary_value (Z_to_binary n x) = binary_value (Z_to_binary n y)).
    congruence.
    now repeat rewrite Z_to_binary_to_Z_mod in *.
Qed.

(* another redundant function *)
Lemma Zmod2_div2 : forall z,
  Zmod2 z = Z.div2 z.
Proof.
  intros.
  destruct z; try (destruct p); auto.
  destruct p; auto.
Qed.

(* the two Z->Bvector conversions are equivalent *)
Lemma Z_to_two_compl_Z_to_binary : forall n z,
  Z_to_two_compl n z = Z_to_binary (S n) z.
Proof.
  induction n; intros.
  destruct z; auto.
  rewrite Z_to_two_compl_Sn_z.
  rewrite Z_to_binary_Sn_z.
  rewrite Zmod2_div2.
  rewrite IHn.
  auto.
Qed.

(* easier to use than two_compl_to_Z_to_two_compl *)
Lemma two_compl_to_Z_to_binary : forall n (v : Bvector (S n)),
  Z_to_binary (S n) (two_compl_value v) = v.
Proof.
  dependent destruction v.
  rewrite <- Z_to_two_compl_Z_to_binary.
  apply two_compl_to_Z_to_two_compl.
Qed.

(* Lemma two_compl_to_Z_to_binary_gt : forall m n (v : Bvector (S n)), *)
(*   (n <= m)%nat ->  *)
(*   Z_to_binary (S m) (two_compl_value v) = zero_cast (S m) v. *)
(* Proof. *)
(*   intros. *)
(*   dependent destruction v. *)
(*   rewrite <- Z_to_two_compl_Z_to_binary. *)
(*   pose proof two_compl_to_Z_to_two_compl. *)
(*   unfold zero_cast. *)
(*   rewrite binary_to_Z_to_binary. *)

Lemma bv_distr_sub:
  forall {n : nat} (i1 i2: Bvector n),
    binary_value i1 >= binary_value i2 ->
    binary_value (sub i1 i2) =
    binary_value i1 - binary_value i2.
Proof.
  unfold sub; intros.
  pose proof (binary_value_pos_bound i1).
  pose proof (binary_value_pos_bound i2).
  rewrite Z_to_binary_to_Z; lia.
Qed.

Lemma bv_distr_add:
  forall {n : nat} (i1 i2: Bvector n),
    binary_value i1 + binary_value i2 < two_power_nat n ->
    binary_value (add i1 i2) = binary_value i1 + binary_value i2.
Proof.
  unfold add; intros.
  pose proof (binary_value_pos_bound i1).
  pose proof (binary_value_pos_bound i2).
  rewrite Z_to_binary_to_Z; lia.
Qed.

Lemma bv_distr_mul :
  forall {n : nat} (i1 i2 : Bvector n),
    0 <= binary_value i1 * binary_value i2 < two_power_nat n ->
    binary_value (mul i1 i2) = binary_value i1 * binary_value i2.
Proof.
  unfold mul; intros.
  pose proof (binary_value_pos_bound i1).
  pose proof (binary_value_pos_bound i2).
  rewrite Z_to_binary_to_Z; auto.
  lia.
  lia.
Qed.
