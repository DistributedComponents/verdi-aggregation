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
Require Import serializable.
Require Import serializablecommfingroup.

Require Import TreeAggregationDynamic.

Require Import Cheerios.Cheerios.
Require Import VerdiCheerios.SerializedMsgParams.

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

Notation "a $ b" := 
  (IOStreamWriter.append (fun _ => a) (fun _ => b))
    (at level 100, right associativity).

Definition Msg_serialize (msg: Msg) :=
  match msg with
  | Aggregate m => 
    serialize x00 $ serialize m
  | Fail => serialize x01
  | Level lvo => 
    serialize x02 $ serialize lvo
  | New => serialize x03
  end.

Definition Msg_deserialize : ByteListReader.t Msg :=
  tag <- deserialize ;;
  match tag with
  | x00 =>
    m <- deserialize ;;
    ByteListReader.ret (Aggregate m)
  | x01 => ByteListReader.ret Fail
  | x02 =>
    lvo <- deserialize ;;
    ByteListReader.ret (Level lvo)
  | x03 => ByteListReader.ret New
  | _ => ByteListReader.error
  end.

Lemma Msg_serialize_deserialize_id :
  serialize_deserialize_id_spec Msg_serialize Msg_deserialize.
Proof.
rewrite /Msg_serialize /Msg_deserialize.
case; repeat (cheerios_crush; simpl).
rewrite (@serialize_deserialize_id _ (serializable_Serializer _)).
by cheerios_crush. 
Qed.

Instance Msg_Serializer : Serializer Msg :=
  {
    serialize := Msg_serialize ;
    deserialize := Msg_deserialize ;
    serialize_deserialize_id := Msg_serialize_deserialize_id
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
