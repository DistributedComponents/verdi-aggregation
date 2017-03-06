From mathcomp
Require Import ssreflect ssrfun fingroup.

Require Import Cheerios.Cheerios.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Module SerializableFinGroup.

Structure mixin_of (gT : finGroupType) := Mixin {
  serialize : gT -> list bool ;
  deserialize : list bool -> option (gT * list bool) ;
  _ : serialize_deserialize_id_spec serialize deserialize
}.

Structure type : Type := Pack {
  sort : finGroupType;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Module Import Exports.
Coercion sort : type >-> finGroupType.
Coercion mixin : type >-> mixin_of.
Notation serializableFinGroupType := type.
Notation SerializableFinGroupMixin := Mixin.
Notation SerializableFinGroupType T m := (@Pack T m).
End Exports.

End SerializableFinGroup.
Export SerializableFinGroup.Exports.

Section SerializeOps.

Variable T : serializableFinGroupType.

Definition serializeg := SerializableFinGroup.serialize T.
Definition deserializeg := SerializableFinGroup.deserialize T.

End SerializeOps.

Section SerializerDefs.

Variable T : serializableFinGroupType.

Global Instance FinGroupSerializer : Serializer T :=
  {
    serialize := @serializeg T ;
    deserialize := @deserializeg T
  }.
Proof.
by case: T => ? [].
Defined.

End SerializerDefs.
