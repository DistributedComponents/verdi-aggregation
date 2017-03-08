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
  serialize : gT -> list bool ;
  deserialize : list bool -> option (gT * list bool) ;
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

Section SerializeOps.

Variable T : serializableCommFinGroupType.

Definition serializeg := SerializableCommFinGroup.serialize T.
Definition deserializeg := SerializableCommFinGroup.deserialize T.

End SerializeOps.

Section SerializerDefs.

Variable T : serializableCommFinGroupType.

Lemma serializeg_deserializeg_id : serialize_deserialize_id_spec (@serializeg T) (@deserializeg T).
Proof. by case: T => ? []. Qed.

Global Instance FinGroupSerializer : Serializer T :=
  {
    serialize := @serializeg T ;
    deserialize := @deserializeg T ;
    serialize_deserialize_id := serializeg_deserializeg_id
  }.

End SerializerDefs.
