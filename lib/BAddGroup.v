Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.ssreflect.div.
Require Import mathcomp.ssreflect.path.
Require Import mathcomp.ssreflect.bigop.
Require Import mathcomp.ssreflect.prime.
Require Import mathcomp.ssreflect.finset.

Require Import mathcomp.fingroup.fingroup.

Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.finalg.

Require Import Bvector ZArith Zdigits.
Require Import BBase.
Require Import BAddMul.

Require Import NatPowLt.

Section BitVector.

Variable n : nat.

Definition Bvector_eqMixin := EqMixin (compareP (VectorEq.eq_dec bool eqb eqb_true_iff n)).
Canonical Structure Bvector_eqType := Eval hnf in EqType (Bvector n) Bvector_eqMixin.

Lemma Bvector_add0b : left_id (zero n) add.
Proof. exact: add_0_l. Qed.

Lemma Bvector_addNb : left_inverse (zero n) opp add.
Proof.
rewrite /left_inverse /= => x.
by rewrite add_comm opp_def.
Qed.

Lemma Bvector_addA : associative (@add n).
Proof. exact: add_assoc. Qed.

Lemma Bvector_addC : commutative (@add n).
Proof. exact: add_comm. Qed.

Lemma Bvector_mul1b : left_id (one n) mul.
Proof. exact: mul_1_l. Qed.

Lemma Bvector_mulA : associative (@mul n).
Proof. exact: mul_assoc. Qed.

Lemma Bvector_mulC : commutative (@mul n).
Proof. exact: mul_comm. Qed.

Lemma Bvector_mul_addl : left_distributive (@mul n) (@add n).
Proof. exact: distr_l. Qed.

Definition Bvector_to_bitseq (v : Bvector n) : bitseq := Vector.to_list v.

Fixpoint bitseq_to_Bvector_aux k (bs : bitseq) : option (Bvector k) :=
match k, bs with
| 0, [::] => Some Bnil
| 0, (_ :: _)%SEQ => None
| S k', [::] => None
| S k', (b :: bs')%SEQ =>
  match bitseq_to_Bvector_aux k' bs' with
  | None => None
  | Some v => Some (Bcons b k' v)
  end
end.

Definition bitseq_to_Bvector (b : bitseq) : option (Bvector n) :=
(bitseq_to_Bvector_aux n) b.

Lemma pcancel_Bvector_bitseq : pcancel Bvector_to_bitseq bitseq_to_Bvector.
Proof.
rewrite /pcancel => v.
rewrite /bitseq_to_Bvector /Bvector_to_bitseq.
elim: v => //=.
move => b n' v H_eq.
by rewrite H_eq.
Qed.

Definition Bvector_countMixin := PcanCountMixin pcancel_Bvector_bitseq.
Definition Bvector_choiceMixin := CountChoiceMixin Bvector_countMixin.
Canonical Structure Bvector_ChoiceType := Eval hnf in ChoiceType (Bvector n) Bvector_choiceMixin.
Canonical Structure Bvector_CountType := Eval hnf in CountType (Bvector n) Bvector_countMixin.

Definition Bvector_zmodMixin := ZmodMixin Bvector_addA Bvector_addC Bvector_add0b Bvector_addNb.
Canonical Bvector_zmodType := Eval hnf in ZmodType (Bvector n) Bvector_zmodMixin.

Lemma Bvector_to_I2k : forall k, Bvector k -> 'I_(2^k).
refine (nat_rect _ _ _); intros.
- apply (@Ordinal 1 0).
  auto with arith.
- inversion H.
  subst.
  have i := X H1.
  apply (@Ordinal _ (Nat.b2n h + 2 * i)).
  have H_ltn := ltn_ord i.
  destruct h.
  * rewrite /Nat.b2n.
    move: H_ltn.
    case: i => i H_lt.
    rewrite /=.
    set x := 2 ^ n0.
    have ->: (x + (x + 0)%coq_nat)%coq_nat = x + x by auto with arith.
    move/ltP => H_lt'.
    apply lt_2xp1 in H_lt'.
    by apply/ltP.
  * rewrite /Nat.b2n.
    have ->: 0 + 2 * i = 2 * i by auto with arith.
    simpl.
    move: H_ltn.
    set x := 2 ^ n0.
    have ->: (x + (x + 0)%coq_nat)%coq_nat = x + x by auto with arith.
    move/ltP => H_lt.
    apply lt_2xp in H_lt.
    by apply/ltP.
Defined.

Definition Bvector_to_I2n := Bvector_to_I2k n.

Lemma I2k_to_Bvector : forall k, 'I_(2^k) -> Bvector k.
simple induction k.
- rewrite /= => i.
  exact: Bnil.
- move => n' IH.
  case => m H_lt.
  set b := Nat.odd m.
  move/ltP: H_lt => H_lt.
  have H_lt' := lt_div2_2pow _ _ H_lt.
  move/ltP: H_lt'.
  set k' := Nat.div2 m.
  move => H_lt'.
  set v' := IH (@Ordinal (2^n') k' H_lt').
  exact: (Bcons b n' v').
Defined.

Definition I2n_to_Bvector (i : 'I_(2^n)) : option (Bvector n) := Some (I2k_to_Bvector n i).

Lemma I2k_to_Bvector_eq : forall k m m' H_m H_m',
    m = m' ->
    I2k_to_Bvector k (@Ordinal (2^k) m H_m)  =
    I2k_to_Bvector k (@Ordinal (2^k) m' H_m').
Proof.
move => k m m' H_m H_m' H_eq.
move: H_m'.
rewrite -H_eq.
move => H_m' {H_eq m'}.
elim: k m H_m H_m' => //.
move => n' IH m H_m H_m'.
simpl.
rewrite /ssr_have.
have IH' := IH (Nat.div2 m) (introT ltP (lt_div2_2pow n' m (elimTF ltP H_m))) (introT ltP (lt_div2_2pow n' m (elimTF ltP H_m'))).
by rewrite IH'.
Qed.

Lemma I2k_to_Bvector_Sn :
    forall (k:nat) (b:bool) (i : 'I_(2^(S k))) (i' : 'I_(2^k)),
      nat_of_ord i = Nat.b2n b + 2 * (nat_of_ord i') ->
      I2k_to_Bvector (S k) i = Bcons b k (I2k_to_Bvector k i').
Proof.
move => k b.
case => i H_i.
case => i' H_i' /= H_eq.
rewrite /ssr_have /=.
case H_o: (Nat.odd i).
  apply Nat.odd_spec in H_o.
  inversion H_o.
  case: b H_eq => /=.
  * move => H_eq.
    rewrite (I2k_to_Bvector_eq _ (Nat.div2 i) i') //.
    rewrite H_eq.
    by rewrite (Nat.div2_succ_double i').
  * have ->: 0 + (2 * i') = 2 * i' by auto with arith.
    move => H_eq.
    rewrite H in H_eq.
    contradict H_eq.
    exact: odd_even_lem.
have H_or := Nat.Even_or_Odd i.
case: H_or => H_even; last by apply Nat.odd_spec in H_even; rewrite H_o in H_even.
inversion H_even.
rewrite H_eq in H.
case: b H_eq H => H_eq H.
- contradict H.
  have ->: Nat.b2n true = 1 by done.  
  have ->: 1 + 2 * i' = 2 * i' + 1 by auto with arith.
  exact: odd_even_lem.
- rewrite /Nat.b2n in H.
  rewrite H in H_eq.
  rewrite (I2k_to_Bvector_eq _ (Nat.div2 i) i') //.
  rewrite H_eq.
  rewrite -H.
  have ->: 0 + 2 * i' = 2 * i' by done.
  exact: Nat.div2_double.
Qed.

Lemma Bvector_to_I2k_Sn :
    forall (k:nat) (b:bool) (v:Bvector k) i i',
      Bvector_to_I2k k v = i ->
      Bvector_to_I2k (S k) (b :: v) = i' ->
      nat_of_ord i' = Nat.b2n b + 2 * (nat_of_ord i).
Proof.
move => k b v.
case => m H_m.
case => m' H_m'.
move => H_eq H_eq'.
rewrite /=.
rewrite /= /ssr_have /= in H_eq'.
destruct b.
- rewrite /eq_rect_r /= in H_eq'.
  rewrite /eq_ind_r /eq_ind /eq_rect /= in H_eq'.
  move: H_eq'.
  case.
  rewrite /= H_eq.
  move => H_eq'.
  by rewrite H_eq'.
- rewrite /eq_rect_r /= in H_eq'.
  rewrite /eq_ind_r /eq_ind /eq_rect /= in H_eq'.
  move: H_eq'.
  case.
  rewrite /= H_eq.
  move => H_eq'.
  by rewrite H_eq'.
Qed.

Lemma pcancel_Bvector_to_I2n : pcancel Bvector_to_I2n I2n_to_Bvector.
Proof.
rewrite /pcancel.
rewrite /I2n_to_Bvector /Bvector_to_I2n.
elim => //.
move => b k v H_eq.
injection H_eq.
set i := Bvector_to_I2k k v.
set i' := Bvector_to_I2k k.+1 (b :: v).
have H_i_eq: i = i by done.
have H_i'_eq: i' = i' by done.
have H_BI := Bvector_to_I2k_Sn _ _ _ _ _ H_i_eq H_i'_eq.
have H_IB := I2k_to_Bvector_Sn _ _ _ _ H_BI.
move => H_eq'.
rewrite H_eq' in H_IB.
by rewrite H_IB.
Qed.

Definition Bvector_finMixin := PcanFinMixin pcancel_Bvector_to_I2n.
Canonical Structure Bvector_finType := Eval hnf in FinType (Bvector n) Bvector_finMixin.
Canonical Bvector_finZmodType := Eval hnf in [finZmodType of Bvector n].
Canonical Bvector_baseFinGroupType := Eval hnf in [baseFinGroupType of Bvector n for +%R].
Canonical Bvector_finGroupType := Eval hnf in [finGroupType of Bvector n for +%R].

Import GroupScope.

Lemma Bvector_mulgC : @commutative (Bvector n) _ mulg.
Proof. exact: Bvector_addC. Qed.

End BitVector.
