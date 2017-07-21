Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.

Require Import TreeAux.
Require Import ZTreeAggregationDynamic.

Require Import Sumbool.
Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Module ZTreeAggregationCorrect (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap).

Module ZTG := ZTreeAggregation NT NOT NSet NOTC NMap RNT ANT TA.
Import ZTG.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Definition sum_aggregate (ns : list name) (state : name -> option data) :=
fold_right (fun d z => z + d.(aggregate)) 0 (filterMap state ns).

Definition sum_aggregate_msg := fold_right (fun m z => z + match m with Aggregate z' => z' | _ => 0 end) 0.

Definition sum_aggregate_msg_to (ns : list name) (packets : name -> name -> list msg) (n : name) :=
fold_right (fun n' z => z + sum_aggregate_msg (packets n' n)) 0 ns.

Definition sum_aggregate_msg_to_all (ns : list name) (packets : name -> name -> list msg) :=
fold_right (fun n z => z + sum_aggregate_msg_to ns packets n) 0 ns.

Definition conserves_network_mass net :=
  length net.(odnwNodes) = 
  (sum_aggregate net.(odnwNodes) net.(odnwState) + sum_aggregate_msg_to_all net.(odnwNodes) net.(odnwPackets)).

Lemma ZTreeAggregation_conserves_network_mass :
  forall net tr,
    step_ordered_dynamic_star step_ordered_dynamic_init net tr ->
    conserves_network_mass net.
Proof.
Admitted.

End ZTreeAggregationCorrect.
