Require Import AggregationDefinitions.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.

Require Import mathcomp.algebra.zmodp.

Require Import StructTact.Fin.

Module CFG (Import N : NatValue) <: CommutativeFinGroup.
  Definition gT := Zp_finGroupType n.
  Definition mulgC : @commutative gT _ mulg := @Zp_mulgC n.
End CFG.
