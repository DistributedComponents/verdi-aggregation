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

Require Import AAC_tactics.AAC.

Set Bullet Behavior "Strict Subproofs".

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

Module ADCFGAACInstances := CFGAACInstances CFG.
Import ADCFGAACInstances.

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

Instance AggregationMsg_TreeAggregation : AggregationMsg :=
  {
    aggr_msg := msg ;
    aggr_msg_eq_dec := msg_eq_dec ;
    aggr_fail := Fail ;
    aggr_of := fun mg => match mg with | Aggregate m' => m' | _ => 1%g end
  }.

Definition sum_local_nodes (net : ordered_dynamic_network) (nodes : list name) : m :=
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
    continuously (now (fun e =>
                         exists d,
                           (snd e.(evt_a)).(odnwState) n = Some d /\
                           aggregate d = 1%g)) s.
Proof.
Admitted.

Definition non_root_nodes_have_unit
           (failed : list name)
           (e : event (list name * ordered_dynamic_network)
                      Label
                      (name * (input + output))) :=
  forall n,
    ~ root n ->
    In n (snd e.(evt_a)).(odnwNodes) ->
    ~ In n failed ->
    exists d,
      (snd e.(evt_a)).(odnwState) n = Some d /\
      aggregate d = 1%g.

Lemma non_root_nodes_eventually_have_unit :
  forall s failed,
    event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
    failed = fst (hd s).(evt_a) ->
    lb_step_execution lb_step_ordered_dynamic_failure s ->
    continuously (now (non_root_nodes_have_unit failed)) s.
Proof.
Admitted.

Definition mass_conserved_opt_event
           (failed : list name)
           (e : event (list name * ordered_dynamic_network)
                      Label
                      (name * (input + output))) : Prop :=
  let (failed, net) := e.(evt_a) in
  conserves_network_mass_opt
    (remove_all name_eq_dec failed net.(odnwNodes))
    net.(odnwNodes) net.(odnwPackets) net.(odnwState).

Lemma mass_always_conserved :
  forall s failed,
    event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
    failed = fst (hd s).(evt_a) ->
    lb_step_execution lb_step_ordered_dynamic_failure s ->
    always (now (mass_conserved_opt_event failed)) s.
Proof.
Admitted.

Definition no_fail_incoming_active_event
           (failed : list name)
           (e : event (list name * ordered_dynamic_network)
                      Label
                      (name * (input + output))) : Prop :=
  forall src dst,
    In dst e.(evt_a).(snd).(odnwNodes) ->
    ~ In dst failed ->
    ~ In Fail (e.(evt_a).(snd).(odnwPackets) src dst).

Definition no_aggregate_incoming_active_event
           (failed : list name)
           (e : event (list name * ordered_dynamic_network)
                      Label
                      (name * (input + output))) : Prop :=
  forall src dst,
    In dst e.(evt_a).(snd).(odnwNodes) ->
    ~ In dst failed ->
    forall v,
      ~ In (Aggregate v) (e.(evt_a).(snd).(odnwPackets) src dst).

Lemma fail_msgs_stop :
  forall failed s,
    failed = (hd s).(evt_a).(fst) ->
    event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
    lb_step_execution lb_step_ordered_dynamic_failure s ->
    continuously (now (no_fail_incoming_active_event failed)) s.
Proof.
Admitted.

Definition correct_root_aggregate
           (n : name)
           (e : event (list name * ordered_dynamic_network)
                      Label
                      (name * (input + output))) : Prop :=
  sum_local
    (Nodes_data_opt
       (remove_all name_eq_dec e.(evt_a).(fst) e.(evt_a).(snd).(odnwNodes))
       e.(evt_a).(snd).(odnwState)) =
  node_aggregate e.(evt_a).(snd).(odnwState) n.

(* This lemma lets us prove stabilization once we prove that its hypotheses
   about the network eventually hold. *)
Lemma no_noise_means_correct_root_aggregate :
  forall e n,
    root n ->
    In n e.(evt_a).(snd).(odnwNodes) ->
    ~ In n e.(evt_a).(fst) ->
    mass_conserved_opt_event e.(evt_a).(fst) e ->
    no_fail_incoming_active_event e.(evt_a).(fst) e ->
    no_aggregate_incoming_active_event e.(evt_a).(fst) e ->
    non_root_nodes_have_unit e.(evt_a).(fst) e ->
    correct_root_aggregate n e.
Proof.
  unfold mass_conserved_opt_event, conserves_network_mass_opt, correct_root_aggregate.
  intros.
  break_let; simpl in *.
  remember (remove_all name_eq_dec l o.(odnwNodes)) as live_nodes.
  assert (sum_fail_balance_incoming_active_opt o.(odnwNodes) live_nodes o.(odnwPackets) o.(odnwState) = 1%g).
  {
    unfold no_fail_incoming_active_event in *.
    unfold sum_fail_balance_incoming_active_opt.
    admit.
  }
  assert (sum_aggregate_msg_incoming_active o.(odnwNodes) live_nodes o.(odnwPackets) = 1%g).
  {
    unfold sum_aggregate_msg_incoming_active.
    unfold sum_aggregate_msg_incoming.
    unfold no_aggregate_incoming_active_event in *.
    unfold sum_aggregate_msg.
    unfold aggregate_sum_fold.
    admit.
  }
  repeat find_rewrite.
  gsimpl.
Admitted.

Theorem churn_free_stabilization :
  forall s, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) ->
       connected (hd s).(evt_a).(snd).(odnwNodes) ->
       lb_step_execution lb_step_ordered_dynamic_failure s ->
       weak_fairness lb_step_ordered_dynamic_failure Tau s ->
       forall n, root n -> In n (hd s).(evt_a).(snd).(odnwNodes) ->
       continuously (now (correct_root_aggregate n)) s.
Proof.
  intros.
  find_copy_eapply_lem_hyp fail_msgs_stop; eauto.
  find_copy_eapply_lem_hyp non_root_nodes_eventually_have_unit; eauto.
  pose proof (continuously_and_tl H5 H6).
Admitted.

End TreeAggregationCorrect.
