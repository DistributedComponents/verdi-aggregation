Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import AggregationDefinitions.
Require Import TreeAux.

Require Import Sumbool.
Require String.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require mathcomp.fingroup.fingroup.

Require Import commfingroup.
Require Import serializablecommfingroup.

Require Import TreeAggregationDynamic.

Require Import Cheerios.Cheerios.

Require Import VerdiCheerios.SerializedParams.

Import DeserializerNotations.

Module Type SerializableCommutativeFinGroup.
  Parameter gT : serializableCommFinGroupType.
  Module CFG <: CommutativeFinGroup.
    Definition gT := SerializableCommFinGroup.sort gT.
  End CFG.
End SerializableCommutativeFinGroup.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module TreeAggregationSerialized (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import SCFG : SerializableCommutativeFinGroup) 
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap)
 (Import AD : ADefs NT NOT NSet NOTC NMap SCFG.CFG).

Module TANS := TreeAggregation NT NOT NSet NOTC NMap RNT SCFG.CFG ANT TA AD.
Import TANS.

Import fingroup.GroupScope.

Definition option_lv_serialize (lvo : option lv) : list bool :=
match lvo with
| None => [false]
| Some lv => [true] ++ serialize lv
end.

Definition option_lv_deserialize : deserializer (option lv) :=
tag <- deserialize ;;
match tag with
| false => ret None
| true => Some <$> deserialize
end.

Lemma option_lv_serialize_deserialize_id :
  serialize_deserialize_id_spec option_lv_serialize option_lv_deserialize.
Proof.
rewrite /option_lv_serialize /option_lv_deserialize.
case; serialize_deserialize_id_crush.
by rewrite /= nat_serialize_deserialize_id.
Qed.

Instance option_lv_Serialize : Serializer (option lv) :=
  {
    serialize := option_lv_serialize ;
    deserialize := option_lv_deserialize ;
    serialize_deserialize_id := option_lv_serialize_deserialize_id
  }.

Definition Msg_serialize (msg: Msg) : list bool :=
  match msg with
  | Aggregate m => 
    [false; false] ++ serialize m
  | Fail => 
    [false; true]
  | Level lvo => 
    [true; false] ++ serialize lvo
  | New => 
    [true; true]
  end.

Definition Msg_deserialize : deserializer Msg :=
  tag1 <- deserialize ;;
  tag2 <- deserialize ;;
  match tag1, tag2 with
  | false, false => 
    m <- deserialize ;;
    ret (Aggregate m)
  | false, true => 
    ret Fail
  | true, false =>
    lvo <- deserialize ;;
    ret (Level lvo)
  | true, true => 
    ret New
  end.

Lemma Msg_serialize_deserialize_id :
  serialize_deserialize_id_spec Msg_serialize Msg_deserialize.
Proof.
rewrite /Msg_serialize /Msg_deserialize.
case; serialize_deserialize_id_crush.
- by rewrite /= serializeg_deserializeg_id.
- by rewrite /= option_lv_serialize_deserialize_id.
Qed.

Instance Msg_Serializer : Serializer Msg :=
  {
    serialize := Msg_serialize ;
    deserialize := Msg_deserialize ;
    serialize_deserialize_id := Msg_serialize_deserialize_id
  }.

Definition Input_serialize (inp : Input) : list bool :=
  match inp with
  | Local m => 
    [false; false; false] ++ serialize m
  | SendAggregate => 
    [false; false; true]
  | AggregateRequest s => 
    [false; true; false] ++ serialize s
  | LevelRequest s =>
    [false; true; true] ++ serialize s
  | Broadcast => 
    [true; false; false]
  end.

Definition Input_deserialize : deserializer Input :=
  tag1 <- deserialize ;;
  tag2 <- deserialize ;;
  tag3 <- deserialize ;;
  match tag1, tag2, tag3 with
  | false, false, false => 
    m <- deserialize ;;
    ret (Local m)
  | false, false, true => 
    ret SendAggregate
  | false, true, false =>
    s <- deserialize ;;
    ret (AggregateRequest s)
  | false, true, true =>
    s <- deserialize ;;
    ret (LevelRequest s)
  | true, false, false =>
    ret Broadcast
  | _, _, _ => fail
  end.

Lemma Input_serialize_deserialize_id :
  serialize_deserialize_id_spec Input_serialize Input_deserialize.
Proof.
rewrite /Input_serialize /Input_deserialize.
case; serialize_deserialize_id_crush.
- by rewrite /= serializeg_deserializeg_id.
- by rewrite /= string_serialize_deserialize_id.
- by rewrite /= string_serialize_deserialize_id.
Qed.

Instance Input_Serializer : Serializer Input :=
  {
    serialize := Input_serialize ;
    deserialize := Input_deserialize ;
    serialize_deserialize_id := Input_serialize_deserialize_id
  }.

Definition Output_serialize (out : Output) : list bool :=
  match out with
  | AggregateResponse s m => 
    [false] ++ serialize s ++ serialize m
  | LevelResponse s lvo => 
    [true] ++ serialize s ++ serialize lvo
  end.

Definition Output_deserialize : deserializer Output :=
  tag <- deserialize ;;
  match tag with
  | false =>
    s <- deserialize ;;
    m <- deserialize ;;
    ret (AggregateResponse s m)
  | true =>
    s <- deserialize ;;
    lvo <- deserialize ;;
    ret (LevelResponse s lvo)
  end.

Lemma Output_serialize_deserialize_id :
  serialize_deserialize_id_spec Output_serialize Output_deserialize.
Proof.
rewrite /Output_serialize /Output_deserialize.
case; serialize_deserialize_id_crush.
- by rewrite /= string_serialize_deserialize_id serializeg_deserializeg_id.
- by rewrite /= string_serialize_deserialize_id option_lv_serialize_deserialize_id.
Qed.

Instance Output_Serializer : Serializer Output :=
  {
    serialize := Output_serialize ;
    deserialize := Output_deserialize ;
    serialize_deserialize_id := Output_serialize_deserialize_id
  }.

Definition TreeAggregation_SerializedBaseParams :=
serialized_base_params.

Definition TreeAggregation_SerializedMultiParams :=
serialized_multi_params.

Definition TreeAggregation_SerializedNameOverlayParams :=
serialized_name_overlay_params.

Definition TreeAggregation_SerializedFailMsgParams :=
serialized_fail_msg_params.

Definition TreeAggregation_SerializedNewMsgParams :=
serialized_new_msg_params.

End TreeAggregationSerialized.
