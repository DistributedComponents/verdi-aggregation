Require Import Cheerios.Cheerios.

From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun bigop eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Serializable.

Structure mixin_of (T : Type) := Mixin {
  ser : T -> IOStreamWriter.t;
  deser : ByteListReader.t T;
  _ : serialize_deserialize_id_spec ser deser
}.

Structure type : Type := Pack {
  sort : Type;
  _ : mixin_of sort
}.

Definition mixin T :=
  let: Pack _ m := T return mixin_of (sort T) in m.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Coercion mixin : type >-> mixin_of.
Notation serializableType := type.
Notation SerializableMixin := Mixin.
Notation SerializableType T m := (@Pack T m).
End Exports.

End Serializable.
Export Serializable.Exports.

Section SerializableOperations.

Variable T : serializableType.

Definition ser : T -> IOStreamWriter.t := Serializable.ser T.
Definition deser : ByteListReader.t T := Serializable.deser T.

End SerializableOperations.

Section SerializableProps.

Variable T : serializableType.

Local Notation serT := (@ser T).
Local Notation deserT := (@deser T).

Lemma ser_deser_id : serialize_deserialize_id_spec serT deserT.
Proof. by case: T => ? []. Qed.

Global Instance serializable_Serializer : Serializer T :=
  {
    serialize := serT ;
    deserialize := deserT ;
    serialize_deserialize_id := ser_deser_id
  }.

End SerializableProps.
