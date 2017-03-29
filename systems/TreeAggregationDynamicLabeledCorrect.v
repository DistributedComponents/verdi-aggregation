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

Definition sum_local_nodes (net : ordered_dynamic_network) (nodes : list Net.name) : m :=
  sum_local (filterMap net.(odnwState) nodes).

Definition aggregation_msg (m : Msg) : bool :=
  match m with
  | Aggregate _ => true
  | _ => false
  end.

Inductive root_path_length (failed : list name) : name -> nat -> Prop :=
| root_path_length_self : forall n,
    ~ In n failed ->
    root n ->
    root_path_length failed n 0
| root_path_length_proxy : forall n n' k,
    root_path_length failed n k ->
    ~ In n' failed ->
    adjacent_to n n' ->
    root_path_length failed n' (S k).

Definition min_root_path_length (failed : list name) (n : name) (k : nat) : Prop :=
  root_path_length failed n k /\ (forall k', root_path_length failed n k' -> k <= k').

Definition leaf_node (net : ordered_dynamic_network) (failed : list name) (n : name) (d : data) : Prop :=
  In n net.(odnwNodes) /\
  ~ In n failed /\
  net.(odnwState) n = Some d /\
  forall n' d' l l',
    In n' net.(odnwNodes) ->
    ~ In n' failed ->
    net.(odnwState) n' = Some d' ->
    min_root_path_length failed n' l' ->
    min_root_path_length failed n l ->
    l' <= l.

Lemma leaf_nodes_eventually_have_unit :
  forall s failed n d,
    event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
    leaf_node (snd (hd s).(evt_a)) failed n d ->
    lb_step_execution lb_step_ordered_dynamic_failure s ->
    eventually (always (now (fun e =>
                               exists d,
                                 (snd e.(evt_a)).(odnwState) n = Some d /\
                                 aggregate d = 1%g))) s.
Proof.
Admitted.

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
