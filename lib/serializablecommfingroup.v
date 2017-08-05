From mathcomp
Require Import ssreflect ssrfun fingroup.

Require Import commfingroup.
Require Import Cheerios.Cheerios.
Require Import serializable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Module SerializableCommFinGroup.

Structure mixin_of (gT : commFinGroupType) := Mixin {
  ser_gT : gT -> IOStreamWriter.t ;
  deser_gT : ByteListReader.t gT ;
  _ : serialize_deserialize_id_spec ser_gT deser_gT
}.

Structure type : Type := Pack {
  sort : commFinGroupType;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Module Import Exports.
Coercion sort : type >-> commFinGroupType.
Coercion mixin : type >-> mixin_of.
Notation serializableCommFinGroupType := type.
Notation SerializableCommFinGroupMixin := Mixin.
Notation SerializableCommFinGroupType T m := (@Pack T m).
End Exports.

End SerializableCommFinGroup.
Export SerializableCommFinGroup.Exports.

Section SerializableCommGroupDefs.

Variable gT : serializableCommFinGroupType.

Lemma ser_gT_deser_gT_id : 
  serialize_deserialize_id_spec (SerializableCommFinGroup.ser_gT gT) (SerializableCommFinGroup.deser_gT gT).
Proof. by case: gT => ? []. Qed.

Definition serCFG_serializableMixin := SerializableMixin ser_gT_deser_gT_id.

Canonical serCFG_serializableType := Eval hnf in SerializableType gT serCFG_serializableMixin.

End SerializableCommGroupDefs.
