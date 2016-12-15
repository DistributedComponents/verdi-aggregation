Require Import AggregationDefinitions.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.
Require Import mathcomp.fingroup.gproduct.

Module ProdCFG (CFG1 CFG2 : CommutativeFinGroup) <: CommutativeFinGroup.
  Definition gT := prod_group CFG1.gT CFG2.gT.
  Lemma mulgC : @commutative gT _ mulg.
  Proof.
  rewrite /mulg /FinGroup.mul /= /extprod_mulg /= /commutative.
  case => a b; case => a' b' /=.
  by rewrite CFG1.mulgC CFG2.mulgC.
  Qed.
End ProdCFG.
