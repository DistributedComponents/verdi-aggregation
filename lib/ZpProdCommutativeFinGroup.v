Require Import AggregationDefinitions.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.
Require Import mathcomp.fingroup.gproduct.

Require Import mathcomp.algebra.zmodp.

Require Import StructTact.Fin.

Module CFG (N1 N2 : NatValue) <: CommutativeFinGroup.
  Definition gT := prod_group (Zp_finGroupType N1.n) (Zp_finGroupType N2.n).
  Lemma mulgC : @commutative gT _ mulg.
  Proof.
  rewrite /mulg /FinGroup.mul /= /extprod_mulg /= /commutative.
  case => a b; case => a' b'.
  by rewrite (@Zp_mulgC N1.n) (@Zp_mulgC N2.n).
  Qed.
End CFG.
