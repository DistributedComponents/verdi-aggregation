Require Import AggregationDefinitions.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.

Require Import mathcomp.algebra.zmodp.

Require Import commfingroup.

Require Import StructTact.Fin.

Section ZpCommFinGroup.

Variable n : nat.

Definition Zp_commFinGroupMixin := CommFinGroupMixin (@Zp_mulgC n).
Canonical Zp_commFinGroup := Eval hnf in CommFinGroupType (Zp_finGroupType n) Zp_commFinGroupMixin.

End ZpCommFinGroup.
