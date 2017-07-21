From mathcomp
Require Import ssreflect ssrfun fingroup gproduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Module CommFinGroup.

Structure mixin_of (gT : finGroupType) := Mixin {
  _ : commutative (@mulg gT)
}.

Structure type : Type := Pack {
  sort : finGroupType;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Module Import Exports.
Coercion sort : type >-> finGroupType.
Notation commFinGroupType := type.
Notation CommFinGroupMixin := Mixin.
Notation CommFinGroupType T m := (@Pack T m).
End Exports.

End CommFinGroup.
Export CommFinGroup.Exports.

Section CommFinGroupIdentities.

Variable T : commFinGroupType.
Local Notation mulgT := (@mulg T).

Lemma mulgC : @commutative T _ mulgT.
Proof. by case: T => ? []. Qed.

End CommFinGroupIdentities.

Section CommProdGroup.

Variable gT1 gT2 : commFinGroupType.

Lemma extprod_mulgC : @commutative (prod_group gT1 gT2) _ mulg.
Proof.
rewrite /mulg /FinGroup.mul /= /extprod_mulg /= /commutative.
case => a b; case => a' b'.
by rewrite (@mulgC gT1) (@mulgC gT2).
Qed.

Definition extprod_commFinGroupMixin := Eval hnf in CommFinGroup.Mixin extprod_mulgC.
Canonical extprod_commFinGroup := CommFinGroupType _ extprod_commFinGroupMixin.

End CommProdGroup.
