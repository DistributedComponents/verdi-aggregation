From mathcomp
Require Import ssreflect ssrfun fingroup.

Require Import commfingroup.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Module SerializableCommFinGroup.

Structure mixin_of (gT : commFinGroupType) := Mixin {
  serialize : gT -> IOStreamWriter.t ;
  deserialize : ByteListReader.t gT ;
  _ : serialize_deserialize_id_spec serialize deserialize
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

Section SerializerDefs.

Variable T : serializableCommFinGroupType.

Lemma serializeg_deserializeg_id : 
  serialize_deserialize_id_spec (SerializableCommFinGroup.serialize T) (SerializableCommFinGroup.deserialize T).
Proof. by case: T => ? []. Qed.

Global Instance FinGroupSerializer : Serializer T :=
  {
    serialize := SerializableCommFinGroup.serialize T ;
    deserialize := SerializableCommFinGroup.deserialize T ;
    serialize_deserialize_id := serializeg_deserializeg_id
  }.

End SerializerDefs.
