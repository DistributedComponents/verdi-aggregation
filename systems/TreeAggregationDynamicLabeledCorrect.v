Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.

Require Import TreeAux.
Require Import TreeAggregationDynamicLabeled.

Require Import AggregationDefinitions.

Require Import InfSeqExt.infseq.

Require Import Relation_Definitions.
Require Import Relation_Operators.

Require Import Sumbool.
Require String.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import commfingroup.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module TreeAggregationCorrect (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import CFG : CommutativeFinGroup)
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap)
 (Import AD : ADefs NT NOT NSet NOTC NMap CFG).

Module TG := TreeAggregation NT NOT NSet NOTC NMap RNT CFG ANT TA AD.

Import TG.

Definition node_aggregate (state : name -> option data) (n : name) :=
  match state n with
  | None => 1%g
  | Some d => d.(aggregate)
  end.

Definition connected (ns : list name) :=
  forall n n', In n ns -> In n' ns ->
  n = n' \/ (clos_trans name adjacent_to) n n'.

Instance AggregationData_Data : AggregationData Data :=
  {
    aggr_local := local ;
    aggr_aggregate := aggregate ;
    aggr_adjacent := adjacent ;
    aggr_balance := balance
  }.

Theorem churn_free_stabilization : 
  forall s, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
       connected (hd s).(evt_a).(snd).(odnwNodes) ->
       lb_step_execution lb_step_ordered_dynamic_failure s ->
       weak_fairness lb_step_ordered_dynamic_failure Tau s ->
       forall n, root n -> In n (hd s).(evt_a).(snd).(odnwNodes) ->
       eventually (always (now (fun e =>
                                  sum_local 
                                    (Nodes_data_opt 
                                       (remove_all name_eq_dec e.(evt_a).(fst) e.(evt_a).(snd).(odnwNodes))
                                       e.(evt_a).(snd).(odnwState)) =
                                  node_aggregate e.(evt_a).(snd).(odnwState) n))) s.
Proof.
Admitted.

End TreeAggregationCorrect.
