Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.DynamicNetLemmas.

Require Import FailureRecorderDynamic.

Require Import MSetFacts.
Require Import MSetProperties.
Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module FailureRecorderCorrect (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (Import ANT : AdjacentNameType NT).

Module FR := FailureRecorder NT NOT NSet ANT.
Import FR.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Lemma Failure_self_channel_empty : 
forall onet failed tr, 
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
 forall n, onet.(odnwPackets) n n = [].
Proof.
move => onet failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: onet = snd (failed, onet) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n.
  case (name_eq_dec h n) => H_dec; last by rewrite collate_ls_neq_to // collate_neq.
  rewrite H_dec collate_ls_not_related; last exact: adjacent_to_irreflexive.
  by rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
    rewrite /= /update2.
    by case sumbool_and => H_dec; first by break_and; repeat find_rewrite; find_higher_order_rewrite.
  rewrite /= /update2.
  by case sumbool_and => H_dec; first by break_and; repeat find_rewrite; find_higher_order_rewrite.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => n.
  case (name_eq_dec h n) => H_dec; last by rewrite collate_neq.
  rewrite H_dec.
  rewrite collate_map2snd_not_related //; last exact: adjacent_to_irreflexive.
Qed.

Lemma Failure_not_failed_no_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, In n (odnwNodes onet) -> ~ In n failed ->
  forall n', ~ In Fail (onet.(odnwPackets) n n').
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n H_a H_f n'.
  simpl in *.
  break_or_hyp.
    case (name_eq_dec n n') => H_dec.
      rewrite -H_dec {H_dec n'}.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; move => H_in; case: H2; move: H_in; exact: in_remove_all_was_in.
      rewrite collate_map2snd_not_in; last by move => H_in; case: H2; move: H_in; exact: in_remove_all_was_in.
      by rewrite (Failure_self_channel_empty H).
    rewrite collate_ls_neq_to //.
    case (adjacent_to_dec n n') => H_dec'.
      case (In_dec name_eq_dec n' failed) => H_in_f.
        rewrite collate_map2snd_in //.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H).
      case (In_dec name_eq_dec n' (odnwNodes net)) => H_in.
        rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup H).
        move => H_in'.
        find_apply_lem_hyp in_app_or.
        simpl in *.
        break_or_hyp; last by break_or_hyp.
        contradict H0.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
      rewrite collate_map2snd_not_in; last by move => H_in'; case: H_in; move: H_in'; exact: in_remove_all_was_in.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
    rewrite collate_map2snd_not_related //. 
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H).
  have H_neq: h <> n by move => H_eq; repeat find_rewrite.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec {n' H_dec}.
    case (adjacent_to_dec h n) => H_dec.
      rewrite collate_ls_NoDup_in.
      * rewrite collate_neq //.
        move => H_in.
        find_apply_lem_hyp in_app_or.
        simpl in *.
        break_or_hyp; last by break_or_hyp.
        contradict H3.
        by eauto.
      * apply: NoDup_filter_rel.
        apply: NoDup_remove_all.
        by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
      * apply: related_filter_rel => //.
        exact: in_remove_all_preserve.
    rewrite collate_ls_not_in; last by move => H_in; find_apply_lem_hyp filter_rel_related; break_and.
    rewrite collate_neq //.
    by eauto.
  rewrite collate_ls_neq_to //.
  rewrite collate_neq //.
  by eauto.
- move => n H_a H_f n'.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
    contradict H0.
    simpl in *.
    rewrite /update2.
    case sumbool_and => H_and; last by eauto.
    break_and; repeat find_rewrite.
    have IH := IHrefl_trans_1n_trace1 _ H_a H_f n'.
    find_rewrite.
    by case: IH; left.
  contradict H0.
  simpl in *.
  rewrite /update2.
  case sumbool_and => H_and; last by eauto.
  break_and; repeat find_rewrite.
  have IH := IHrefl_trans_1n_trace1 _ H_a H_f n'.
  find_rewrite.
  move => H_in.
  case: IH.
  by right.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => n H_a H_f n'.
  have H_neq: h <> n by eauto.
  have H_not_in: ~ In n failed by eauto.
  rewrite collate_neq //.
  by eauto.
Qed.

Lemma Failure_inactive_no_incoming :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n' n = [].
Proof.
move => onet failed tr H.
have ->: onet = snd (failed, onet) by [].
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in n'.
  have H_neq: h <> n by eauto.
  have H_not_in: ~ In n (odnwNodes net) by eauto.
  rewrite collate_ls_neq_to //.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map2snd_not_in; last by move => H_in'; case: H_not_in; move: H_in'; exact: in_remove_all_was_in.
    by auto.
  rewrite collate_neq //.
  by auto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases; simpl in *.
    rewrite /update2.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  rewrite /update2.
  break_if; break_and; last by eauto.
  by repeat find_rewrite; eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => n H_in n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_in.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map2snd_not_in; last by move => H_in'; case: H_in; move: H_in'; exact: in_remove_all_was_in.
    by auto.
  rewrite collate_neq //.
  by auto.
Qed.

Section SingleNodeInv.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variable n : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_fail : 
  forall onet failed tr n',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    forall d, onet.(odnwState) n = Some d ->
    P d ->
    P (mkData (NSet.remove n' d.(adjacent))).

Hypothesis recv_new : 
  forall onet failed tr n',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    forall d, onet.(odnwState) n = Some d ->
    P d ->
    P (mkData (NSet.add n' d.(adjacent))).

Theorem P_inv_n : forall d, onet.(odnwState) n = Some d -> P d.
Proof.
move: onet failed tr H_step active not_failed.
clear onet failed tr H_step active not_failed.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_ordered_dynamic_failure_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_a H_f d.
  rewrite /update /=.
  case name_eq_dec => H_dec H_eq; first by find_inversion.
  by break_or_hyp; eauto.
- simpl in *.
  rewrite /update.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases; break_if.
  * repeat find_rewrite.
    find_injection.
    destruct d0.
    simpl in *.
    repeat find_rewrite.
    by eauto.
  * by eauto.
  * repeat find_rewrite.
    find_injection.
    destruct d0.
    simpl in *.
    repeat find_rewrite.
    by eauto.
  * by eauto.
- simpl in *.
  rewrite /update.
  find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => H_a H_f.
  by eauto.
Qed.

End SingleNodeInv.

Section SingleNodeInvOut.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init_empty : P (InitData n) [].

Hypothesis after_init_adjacent : P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n' onet.(odnwNodes) ->
  ~ In n failed ->
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  In n' failed ->
  n' <> n ->
  (*adjacent_to n n' ->*)
  onet.(odnwPackets) n' n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.remove n' d.(adjacent))) (onet.(odnwPackets) n n').

Hypothesis recv_fail_from_neq :
  forall onet failed tr from ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  In from failed ->  
  from <> n ->
  from <> n' ->
  onet.(odnwPackets) from n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.remove from d.(adjacent))) (onet.(odnwPackets) n n').

Hypothesis recv_new_from_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n' <> n ->
  (*adjacent_to n n' ->*)
  onet.(odnwPackets) n' n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.add n' d.(adjacent))) (onet.(odnwPackets) n n').

Hypothesis recv_new_from_neq :
  forall onet failed tr from ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  from <> n ->
  from <> n' ->
  onet.(odnwPackets) from n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.add from d.(adjacent))) (onet.(odnwPackets) n n').

Hypothesis recv_new_from_out_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  ~ In n' failed ->
  n <> n' ->
  (*adjacent_to n n' ->*)
  onet.(odnwPackets) n n' = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P d ms.

Theorem P_inv_n_out : forall d, onet.(odnwState) n = Some d -> P d (onet.(odnwPackets) n n').
Proof.
move: onet failed tr H_step active not_failed.
clear onet failed tr H_step active not_failed.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3 4}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_ordered_dynamic_failure_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => H_a H_f d.
  rewrite /update /=.
  case name_eq_dec => H_dec H_eq.
    repeat find_rewrite.
    find_injection.
    case (name_eq_dec h n') => H_dec.
      repeat find_reverse_rewrite.
      rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
      rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
      by rewrite (Failure_self_channel_empty s1).
    rewrite collate_ls_neq_to //.
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_map2snd_not_in; last by move => H_in; case: H_a'; move: H_in; exact: in_remove_all_was_in.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_map2snd_not_in //; last by move => H_in; move: H_in H_f'; apply: in_remove_all_not_in.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (adjacent_to_dec h n') => H_dec'.
      rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    rewrite collate_map2snd_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
  break_or_hyp => //.
  set f := collate _ _ _ _.
  have H_eq_f: f n n' = odnwPackets net n n' by rewrite /f collate_neq //; auto.
  rewrite (collate_ls_f_eq _ _ name_eq_dec _ _ _ _ _ _ _ H_eq_f) {H_eq_f f}.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_ls_neq_to //; eauto.  
  repeat find_reverse_rewrite.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_ls_not_related //; eauto.
  rewrite collate_ls_NoDup_in.
  * have H_p: P d (odnwPackets net n h) by eauto.
    move: H_p.
    rewrite (Failure_inactive_no_incoming s1) //=.
    by eauto.
  * apply: NoDup_filter_rel.
    apply: NoDup_remove_all.
    by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
  * apply: related_filter_rel => //.
    exact: in_remove_all_preserve.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => /=.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
    case (in_dec name_eq_dec from failed0) => H_from_failed; last first.
      have H_f := Failure_not_failed_no_fail s1 _ H_from_nodes H_from_failed to.
      rewrite H3 in H_f.
      by case: H_f; left.
    have H_neq: from <> to by move => H_eq; rewrite H_eq in H_from_failed.      
    move: H6.
    rewrite /update.
    break_if => H_eq.
      find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; first by break_and.
      case: o => H_eq; case (name_eq_dec from n') => H_eq'.
      + rewrite H_eq'.
        rewrite H_eq' in H_from_nodes H_from_failed H_eq H3.
        apply (@recv_fail_from_eq _ failed0 tr1 ms) => //.
        exact: H8.
      + apply (@recv_fail_from_neq _ failed0 tr1 _ ms) => //.
        exact: H8.
      + rewrite H_eq'.
        rewrite H_eq' in H_from_nodes H_from_failed H_eq H3.
        apply (@recv_fail_from_eq _ failed0 tr1 ms) => //.
          move => H_eq''.
          by rewrite H_eq'' in H_eq.
        exact: H8.
      + apply (@recv_fail_from_neq _ failed0 tr1 _ ms) => //.
        exact: H8.
    rewrite /update2.
    break_if.
      break_and.
      by rewrite H in H_from_failed.
    exact: H8.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
    have H_neq: from <> to.
      move => H_eq.
      by rewrite H_eq (Failure_self_channel_empty s1) in H3.      
    move: H6.
    rewrite /update.
    break_if => H_eq.
      find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; first by break_and.
      case: o => H_eq; case (name_eq_dec from n') => H_eq'.
      * rewrite H_eq'.
        rewrite H_eq' in H_from_nodes H_eq H3.
        apply (@recv_new_from_eq _ failed0 tr1 ms) => //.
        exact: H8.
      * apply (@recv_new_from_neq _ failed0 tr1 _ ms) => //.
        exact: H8.
      + rewrite H_eq'.
        rewrite H_eq' in H_from_nodes H_eq H3.
        apply (@recv_new_from_eq _ failed0 tr1 ms) => //.
          move => H_eq''.
          by rewrite H_eq'' in H_eq.
        exact: H8.
      + apply (@recv_new_from_neq _ failed0 tr1 _ ms) => //.
        exact: H8.
    rewrite /update2.
    break_if.
      break_and.
      rewrite H H4 in H3 H_neq H_from_nodes H0 H1.
      have H_p := H8 d0 H_eq.
      move: H_p.
      exact: (@recv_new_from_out_eq _ failed0 tr1 ms).
    exact: H8.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => H_in_nodes H_in_failed d H_eq_d.
  have H_neq: h <> n by auto.
  have H_not_in: ~ In n failed0 by auto.
  rewrite collate_neq //.
  exact: IHs1.
Qed.

End SingleNodeInvOut.

Section SingleNodeInvIn.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis after_init_new :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n' onet.(odnwNodes) ->
  ~ In n' failed ->
  adjacent_to n' n ->  
  P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  ~ In n' onet.(odnwNodes) ->  
  adjacent_to n' n ->  
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  In n' failed ->
  n' <> n ->
  onet.(odnwPackets) n' n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P (mkData (NSet.remove n' d.(adjacent))) ms.

Hypothesis recv_fail_from_neq :
  forall onet failed tr from ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  In from failed ->
  from <> n ->
  from <> n' ->
  onet.(odnwPackets) from n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P (mkData (NSet.remove from d.(adjacent))) (onet.(odnwPackets) n' n).

Hypothesis recv_new_from_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n' <> n ->
  onet.(odnwPackets) n' n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P (mkData (NSet.add n' d.(adjacent))) ms.

Hypothesis recv_new_from_neq :
  forall onet failed tr from ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  from <> n ->
  from <> n' ->
  onet.(odnwPackets) from n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P (mkData (NSet.add from d.(adjacent))) (onet.(odnwPackets) n' n).

Hypothesis send_fail : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    In n' onet.(odnwNodes) ->
    ~ In n' failed ->
    adjacent_to n' n ->
    n' <> n ->    
    forall d, onet.(odnwState) n = Some d ->
     P d (onet.(odnwPackets) n' n) ->
     P d (odnwPackets onet n' n ++ [Fail]).

Theorem P_inv_n_in : forall d, onet.(odnwState) n = Some d -> P d (onet.(odnwPackets) n' n).
Proof.
move: onet failed tr H_step active not_failed.
clear onet failed tr H_step active not_failed.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3 4}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_ordered_dynamic_failure_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => H_a H_f d.
  rewrite /update /=.
  case name_eq_dec => H_dec H_eq.
    repeat find_rewrite.
    find_injection.
    case (name_eq_dec h n') => H_dec.
      repeat find_reverse_rewrite.
      rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
      rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
      by rewrite (Failure_self_channel_empty s1).
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_ls_not_in_related; last by eauto using in_remove_all_was_in.
      rewrite collate_neq //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_ls_in_remove_all //.
      rewrite collate_neq //.
      by rewrite (Failure_inactive_no_incoming s1).
    case (adjacent_to_dec h n') => H_dec'; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Failure_inactive_no_incoming s1).
    rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite collate_neq //.
    rewrite (Failure_inactive_no_incoming s1) //=.
    apply adjacent_to_symmetric in H_dec'.
    exact: (after_init_new s1).
  have H_neq: h <> n by auto.
  rewrite collate_ls_neq_to //.
  break_or_hyp => //.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_neq //; exact: IHs1.
  rewrite -H_dec'.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_map2snd_not_related //; rewrite H_dec'; exact: IHs1.
  rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
  have IH := IHs1 H H_f _ H_eq.
  move: IH.
  rewrite -H_dec'.
  rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //=.
  rewrite H_dec' in H0 H_adj.
  exact: (after_adjacent s1).
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => /=.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
    case (in_dec name_eq_dec from failed0) => H_from_failed; last first.
      have H_f := Failure_not_failed_no_fail s1 _ H_from_nodes H_from_failed to.
      rewrite H3 in H_f.
      by case: H_f; left.
    have H_neq: from <> to by move => H_eq; rewrite H_eq in H_from_failed.
    move: H6.
    rewrite /update.
    break_if => H_eq.
      find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if.
        break_and.
        rewrite H.
        rewrite H in H_neq H_from_nodes H_from_failed H3.
        apply (recv_fail_from_eq s1) => //.
        exact: H8.
      break_or_hyp => //.
      apply (@recv_fail_from_neq _ _ _ _ ms s1) => //.
      exact: H8.
    rewrite /update2.
    break_if; first by break_and; find_rewrite.
    exact: H8.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
    have H_neq: from <> to.
      move => H_eq.
      by rewrite H_eq (Failure_self_channel_empty s1) in H3.
    move: H6.
    rewrite /update.
    break_if => H_eq.
      find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if.
        break_and.
        rewrite H.
        rewrite H in H_neq H3 H_from_nodes.
        apply (recv_new_from_eq s1) => //.
        exact: H8.
      break_or_hyp => //.
      apply (@recv_new_from_neq _ _ _ _ ms s1) => //.
      exact: H8.
    rewrite /update2.
    break_if; first by break_and; find_rewrite.
    exact: H8.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => H_in_nodes H_in_failed d H_eq_d.
  have H_neq: h <> n by auto.
  have H_not_in: ~ In n failed0 by auto.
  case (name_eq_dec h n') => H_dec.
    rewrite H_dec.
    case (adjacent_to_dec n' n) => H_dec'; last by rewrite collate_map2snd_not_related //; exact: IHs1.
    rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite H_dec in H_neq H0 H1.
    apply (send_fail s1) => //.
    exact: IHs1.
  rewrite collate_neq //.
  exact: IHs1.
Qed.
      
End SingleNodeInvIn.

Lemma Failure_node_not_adjacent_self : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 ~ In n failed ->
 forall d, odnwState net n = Some d ->
 ~ NSet.In n d.(adjacent).
Proof.
move => net failed tr H_st.
move => n H_n H_f d0 H_eq.
pose P_curr (d : Data) (l : list Msg) :=
  ~ NSet.In n (adjacent d).
rewrite -/(P_curr _ (net.(odnwPackets) n n)).
move: H_eq; generalize d0 => {d0}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto with set.
- by auto with set.
- by eauto with set.
- by eauto with set.
Qed.

Lemma Failure_in_after_all_fail_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), before_all New Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  before_all New Fail l.
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto.
- by auto.
- move => onet failed tr ms H_st H_in H_f H_in' H_f' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq in H_bef.
  apply before_all_head_not_in in H_bef => //.
  exact: before_all_not_in.
- move => onet failed tr ms H_st H_in H_f H_in' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq in H_bef.
  rewrite /= in H_bef.
  break_or_hyp; last by break_and.
  exact: before_all_not_in.
- move => onet failed tr H_st H_in H_f H_in' H_f' H_adj H_neq d H_eq H_bef.
  exact: before_all_neq_append.
Qed.

Lemma Failure_le_one_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) New <= 1.
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  count_occ Msg_eq_dec l New <= 1.
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto.
- move => onet failed tr ms H_st H_in H_f H_in' H_f' H_neq H_eq d H_eq' H_bef.
  by rewrite H_eq /= in H_bef.
- move => onet failed tr ms H_st H_in H_f H_in' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq /= in H_bef.
  by auto with arith.
- move => onet failed tr H_st H_in H_f H_in' H_f' H_adj H_neq d H_eq H_bef.
  rewrite count_occ_app /=.
  by ring_simplify.
Qed.

Lemma Failure_le_one_fail : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) Fail <= 1.
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  count_occ Msg_eq_dec l Fail <= 1.
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto.
- by auto.
- move => onet failed tr ms H_st H_in H_f H_in' H_f' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq /= in H_bef.
  by auto with arith.
- move => onet failed tr ms H_st H_in H_f H_in' H_neq H_eq d H_eq' H_bef.
  by rewrite H_eq /= in H_bef.
- move => onet failed tr H_st H_in H_f H_in' H_f' H_adj H_neq d H_eq H_bef.
  rewrite count_occ_app /=.
  have H_not_in := Failure_not_failed_no_fail H_st _ H_in' H_f' n.
  have H_cnt := @count_occ_not_In _ Msg_eq_dec.
  apply H_cnt in H_not_in.
  rewrite H_not_in.
  by auto with arith.
Qed.

Lemma Failure_not_adjacent_no_incoming : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
    forall n, In n (odnwNodes onet) -> ~ In n failed ->
         forall n', ~ adjacent_to n n' ->
               onet.(odnwPackets) n' n = [].
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  ~ adjacent_to n n' -> l = [].
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => //=.
- by intuition by (find_apply_lem_hyp adjacent_to_symmetric).
- by intuition by (find_apply_lem_hyp adjacent_to_symmetric).
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_neq H_eq d H_eq' H_bef H_adj.
  concludes.
  by find_rewrite.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_neq H_eq d H_eq' H_bef H_adj.
  concludes.
  by find_rewrite.
- by intuition by (find_apply_lem_hyp adjacent_to_symmetric).
Qed.

Lemma Failure_in_new_failed_incoming_fail : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
    forall n, In n (odnwNodes onet) -> ~ In n failed ->
         forall n', In n' failed ->
               In New (onet.(odnwPackets) n' n) ->
               In Fail (onet.(odnwPackets) n' n).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 4 5}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n H_in_n H_in_f n' H_in_f'.
  have H_neq: n <> n' by move => H_eq; rewrite H_eq in H_in_f.
  have H_neq': h <> n'.
    move => H_eq.
    rewrite -H_eq in H_in_f'.
    by apply (ordered_dynamic_failed_then_initialized H) in H_in_f'.
  case: H_in_n => H_in_n.
    rewrite H_in_n.
    rewrite H_in_n in H2.
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Failure_inactive_no_incoming H).
  have H_neq_h: h <> n by move => H_eq; rewrite -H_eq in H_in_n.
  rewrite collate_ls_neq_to //.
  rewrite collate_neq //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in_n H_in_f n' H_in_f'.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
    move: H0.
    rewrite /= /update2.
    break_if.
      break_and.
      move => H_in.
      rewrite -H6 in H_in_n H_in_f.
      have H_bef := Failure_in_after_all_fail_new H _ H_in_n H_in_f from.
      contradict H_in.
      rewrite H5 in H_bef.
      move: H_bef.
      exact: before_all_head_not_in.
    exact: IHrefl_trans_1n_trace1.
  move: H0.
  rewrite /= /update2.
  break_if.
    break_and.
    move => H_in.
    rewrite -H6 in H_in_n H_in_f.
    have H_le := Failure_le_one_new H _ H_in_n H_in_f from.
    rewrite H5 /= in H_le.
    apply (@count_occ_In _ Msg_eq_dec) in H_in.
    by omega.
  exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => n H_in_n H_in_f n' H_in_f'.
  have H_neq: h <> n by auto.
  have H_in_n_f: ~ In n failed0 by auto.
  case: H_in_f' => H_in_f'.
    rewrite -H_in_f'.
    case (adjacent_to_dec h n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      move => H_in.
      have H_adj': ~ adjacent_to n h.
        move => H_adj.
        by apply adjacent_to_symmetric in H_adj.
      have H_emp := Failure_not_adjacent_no_incoming H H_in_n H_in_n_f H_adj'.
      by rewrite H_emp in H_in.
    rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup H).
    move => H_in.
    apply in_or_app.
    by right; left.
  have H_neq': h <> n' by move => H_eq; rewrite -H_eq in H_in_f'.
  rewrite collate_neq //.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma Failure_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
          forall d, onet.(odnwState) n = Some d ->
               NSet.In n' d.(adjacent) ->
               adjacent_to n' n.
Proof.
move => net failed tr H_st.
move => n n' H_n H_f d0 H_eq.
pose P_curr (d : Data) (l : list Msg) :=
  NSet.In n' d.(adjacent) -> adjacent_to n' n.
rewrite -/(P_curr _ (net.(odnwPackets) n' n)).
move: H_eq; generalize d0 => {d0}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => //=.
- move => H_ins.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_neq H_eq d H_eq' H_bef H_ins.
  by find_apply_lem_hyp NSetFacts.remove_1.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_from H_f_from H_neq H_neq' H_eq d H_eq' H_bef H_ins.
  find_apply_lem_hyp NSetFacts.remove_3.
  exact: H_bef.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_neq H_eq d H_eq' H_bef H_ins.
  case (adjacent_to_dec n' n) => H_dec //.
  have H_adj': ~ adjacent_to n n' by move => H_adj'; apply adjacent_to_symmetric in H_adj'.
  have H_emp := Failure_not_adjacent_no_incoming H_st H_in_n H_in_f H_adj'.
  by rewrite H_emp in H_eq.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_from_in H_neq H_neq' H_eq d H_eq' H_bef H_ins.
  find_apply_lem_hyp NSetFacts.add_3 => //.
  exact: H_bef.
Qed.
 
Lemma Failure_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
       forall d, onet.(odnwState) n = Some d ->
            NSet.In n' d.(adjacent) ->
            (In n' (odnwNodes onet) /\ ~ In n' failed) \/ (In n' (odnwNodes onet) /\ In n' failed /\ In Fail (onet.(odnwPackets) n' n)).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3 4 6 8}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n n' H_or H_in_f d H_eq H_ins.
  move: H_eq.
  rewrite /update.
  break_if => H_eq.
    find_inversion.
    rewrite /= in H_ins.
    by apply NSetFacts.empty_1 in H_ins.
  break_or_hyp => //.
  simpl in *.
  have IH := IHrefl_trans_1n_trace1 _ _ H0 H_in_f _ H_eq H_ins.
  break_or_hyp; break_and; first by left; split; first by right.  
  have H_neq: h <> n' by move => H_eq'; rewrite -H_eq' in H3.
  right.
  split; first by right.
  split => //.
  rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_not_in.
  by rewrite collate_neq.
- move => n n' H_in_n H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
    move: H8.
    rewrite /= /update.
    break_if => H_eq.
      find_inversion.
      destruct d0.
      simpl in *.
      rewrite H9 in H10.
      have H_neq: from <> n' by move => H_eq; rewrite H_eq in H10; find_apply_lem_hyp NSetFacts.remove_1.
      rewrite /update2.
      break_if; first by break_and.
      break_or_hyp => //.
      find_apply_lem_hyp NSetFacts.remove_3.
      move: H4 H10.
      exact: IHrefl_trans_1n_trace1.
    rewrite /update2.
    break_if; first by break_and; find_rewrite.    
    move: H_eq H10.
    exact: IHrefl_trans_1n_trace1.
  move: H8.
  rewrite /= /update.
  break_if => H_eq.
    find_inversion.
    destruct d0.
    simpl in *.
    rewrite H9 in H10.
    rewrite /update2.
    break_if.
      break_and.
      rewrite H0 in H5.
      case (in_dec name_eq_dec n' net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H) // in H5.
      case (in_dec name_eq_dec n' failed0) => H_dec'; last by left.
      right; split => //.
      split => //.
      have H_in := Failure_in_new_failed_incoming_fail H _ H_in_n H_in_f _ H_dec'.
      rewrite H5 /= in H_in.
      suff H_suff: New = Fail \/ In Fail ms by case: H_suff.
      apply: H_in.
      by left.
    break_or_hyp => //.
    find_apply_lem_hyp NSetFacts.add_3 => //.
    move: H4 H10.
    exact: IHrefl_trans_1n_trace1.
  rewrite /update2.
  break_if; first by break_and; find_rewrite.
  move: H_eq H10.
  exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => n n' H_in_n H_in_f d H_eq H_ins.
  have H_neq: h <> n by auto.
  have H_in: ~ In n failed0 by auto.
  case (name_eq_dec h n') => H_dec.
    rewrite H_dec in H2 H3.
    right.
    split => //.
    split; first by left.
    rewrite -H_dec.
    rewrite -H_dec in H_ins.
    have H_adj := Failure_in_adj_adjacent_to H _ H_in_n H_in H_eq H_ins.
    rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup H).
    apply in_or_app.
    by right; left.
  rewrite collate_neq //.
  have IH := IHrefl_trans_1n_trace1 _ _ H_in_n H_in _ H_eq H_ins.
  case: IH => /= IH; break_and.
    left; split => //.
    move => H_or.
    by break_or_hyp.
  right; split => //; split => //.
  by right.
Qed.

Lemma Failure_new_incoming_not_in_adj :
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->        
        forall (n' : name), In New (net.(odnwPackets) n' n) ->
                       forall d, net.(odnwState) n = Some d ->
                            ~ NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st.
move => n H_n H_f n' H_in d0 H_eq.
move: H_in.
pose P_curr (d : Data) (l : list Msg) :=
  In New l -> ~ NSet.In n' d.(adjacent).
rewrite -/(P_curr _ _ ).
move: H_eq; generalize d0 => {d0}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_adj H_bef.
  exact: NSetFacts.empty_1.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_adj d H_eq H_bef H_in.
  move => H_ins.
  have H_or := Failure_in_adj_or_incoming_fail H_st _ H_in_n H_in_f H_eq H_ins.
  by case: H_or => H_or; break_and.
- by eauto with set.
- by eauto with set.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_neq H_eq d H_eq' H_bef H_in.
  have H_le := Failure_le_one_new H_st _ H_in_n H_in_f n'.
  rewrite H_eq /= in H_le.
  apply (@count_occ_In _ Msg_eq_dec) in H_in.
  by omega.
- by eauto with set.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_adj H_neq d H_eq H_bef H_ins.
  apply: H_bef.
  apply in_app_or in H_ins.
  case: H_ins => H_ins //.
  by case: H_ins.
Qed.

Section DualNodeInv.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variables n n' : name.

Hypothesis active_n : In n (odnwNodes onet).

Hypothesis active_n' : In n' (odnwNodes onet).

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

Hypothesis after_init : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    n' = n ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    P (InitData n) (InitData n) [] [].

Hypothesis after_init_fst_not_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    ~ adjacent_to n n' ->
    forall d, onet.(odnwState) n' = Some d ->
    P (InitData n) d [] [].

Hypothesis after_init_snd_not_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
     In n (odnwNodes onet) -> 
     ~ In n failed ->
     ~ In n' (odnwNodes onet) ->
     ~ In n' failed ->
     n' <> n ->
     ~ adjacent_to n n' ->
     forall d, onet.(odnwState) n = Some d ->
     P d (InitData n') [] [].
      
Hypothesis after_init_fst_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n n' ->
    forall d, onet.(odnwState) n' = Some d ->
    P (InitData n) d [New] [New].

Hypothesis after_init_snd_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
     In n (odnwNodes onet) -> 
    ~ In n failed ->
    ~ In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n n' ->
    forall d, onet.(odnwState) n = Some d ->
    P d (InitData n') [New] [New].

Hypothesis recv_fail_self :
  forall onet failed tr from ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    In from failed ->
    from <> n ->    
    adjacent_to from n ->
    onet.(odnwPackets) from n = Fail :: ms ->
    forall d, onet.(odnwState) n = Some d ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| adjacent := NSet.remove from (adjacent d) |} 
      {| adjacent := NSet.remove from (adjacent d) |} 
      [] [].

Hypothesis recv_fail_other_fst :
  forall onet failed tr from ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    from <> n ->
    from <> n' ->
    In from (odnwNodes onet) ->
    In from failed ->
    adjacent_to from n ->
    onet.(odnwPackets) from n = Fail :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| adjacent := NSet.remove from (adjacent d0) |} d1
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_fail_other_snd :
  forall onet failed tr from ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    from <> n ->
    from <> n' ->
    In from (odnwNodes onet) ->
    In from failed ->
    adjacent_to from n' ->
    onet.(odnwPackets) from n' = Fail :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| adjacent := NSet.remove from (adjacent d1) |}
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_new_self :
  forall onet failed tr from ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    from <> n ->
    adjacent_to from n ->
    onet.(odnwPackets) from n = New :: ms ->
    forall d, onet.(odnwState) n = Some d ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| adjacent := NSet.add from (adjacent d) |}
      {| adjacent := NSet.add from (adjacent d) |} 
      [] [].

Hypothesis recv_new_fst :
  forall onet failed tr ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n' n = New :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| adjacent := NSet.add n' (adjacent d0) |} d1
      (odnwPackets onet n n') ms.

Hypothesis recv_new_snd :
  forall onet failed tr ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n n' = New :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| adjacent := NSet.add n (adjacent d1) |}
      ms (odnwPackets onet n' n).

Hypothesis recv_new_fst_other :
  forall onet failed tr from ms,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n ->
   onet.(odnwPackets) from n = New :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P {| adjacent := NSet.add from (adjacent d0) |} d1
     (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_new_snd_other :
  forall onet failed tr from ms,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n' ->
   onet.(odnwPackets) from n' = New :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P d0 {| adjacent := NSet.add from (adjacent d1) |} 
     (odnwPackets onet n n') (odnwPackets onet n' n).

Theorem P_dual_inv : 
  forall d0, onet.(odnwState) n = Some d0 -> 
  forall d1, onet.(odnwState) n' = Some d1 -> 
  P d0 d1 (onet.(odnwPackets) n n') (onet.(odnwPackets) n' n).
Proof.
move: onet failed tr H_step active_n active_n' not_failed_n not_failed_n'.
clear onet failed tr H_step active_n active_n' not_failed_n not_failed_n'.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 2 5 6 7 8}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_n H_in_n' H_in_f H_in_f'.  
  rewrite /update.
  break_if; break_if.
  * move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
    rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
    rewrite (Failure_self_channel_empty s1).
    exact: (after_init s1).
  * case: H_in_n' => H_in_n'; first by find_rewrite.
    move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    rewrite collate_ls_neq_to; last by auto.
    case (adjacent_to_dec h n') => H_dec.
      rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      rewrite collate_neq //; last by auto.
      rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //.
      rewrite (Failure_inactive_no_incoming s1) //=.
      exact: (after_init_fst_adjacent s1).
    rewrite collate_map2snd_not_related //.
    rewrite collate_ls_not_related //.
    rewrite collate_neq //; last by auto.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //.
    rewrite (Failure_inactive_no_incoming s1) //.
    exact: (after_init_fst_not_adjacent s1).
  * move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    case: H_in_n => H_in_n; first by rewrite -H_in_n in n0.
    case (adjacent_to_dec h n) => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq; last by auto.
      rewrite collate_ls_neq_to; last by auto.
      rewrite collate_map2snd_not_related //.
      rewrite (Failure_inactive_no_incoming s1) //.
      rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //.
      have H_adj: ~ adjacent_to n h.
        move => H_adj.
        case: H_dec.
        exact: adjacent_to_symmetric.
      have H_neq: h <> n by auto.
      exact: (after_init_snd_not_adjacent s1).
    rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite collate_neq; last by auto.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite (Failure_inactive_no_incoming s1) //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //=.
    apply adjacent_to_symmetric in H_dec.
    have H_neq: h <> n by auto.
    exact: (after_init_snd_adjacent s1).
  * move => d0 H_eq d1 H_eq'.
    case: H_in_n => H_in_n; first by rewrite H_in_n in n0.
    case: H_in_n' => H_in_n'; first by rewrite H_in_n' in n1.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_neq; last by auto.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_neq; last by auto.
    exact: IHs1.
- move => H_in_n H_in_n' H_in_f H_in_f'.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  * move: H6 H9.
    rewrite /update /=.
    break_if; break_if => H_eq H_eq'.
    + repeat find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; first by break_and; rewrite H (Failure_self_channel_empty s1) in H3.
      break_or_hyp => //.
      have IH := H8 _ H2 _ H2.
      case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
      case (In_dec name_eq_dec from failed0) => H_from_f; last first.
        have H_f := Failure_not_failed_no_fail s1 _ H_from_in H_from_f to.
        rewrite H3 in H_f.
        by case: H_f; left.
      case (adjacent_to_dec from to) => H_dec; last first.
        rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
        move => H_adj.
        case: H_dec.
        exact: adjacent_to_symmetric.
      rewrite (Failure_self_channel_empty s1).
      exact: (recv_fail_self s1 _ _ _ _ _ _ _ H3).
    + find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2 /=.
      break_if; break_if => //=; first by break_and; rewrite -H in n0.
      - by break_and; break_or_hyp.
      - break_and.
        rewrite H in H3.
        have H_f := Failure_not_failed_no_fail s1 _ H_in_n' H_in_f' to.
        rewrite H3 in H_f.
        by case: H_f; left.
      - break_or_hyp => //.
        have H_neq: from <> to by move => H_eq; rewrite H_eq (Failure_self_channel_empty s1) in H3.
        case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
        case (In_dec name_eq_dec from failed0) => H_from_f; last first.
          have H_f := Failure_not_failed_no_fail s1 _ H_from_in H_from_f to.
          rewrite H3 in H_f.
          by case: H_f; left.
        have IH := H8 _ H2 _ H_eq'.
        case (adjacent_to_dec from to) => H_dec; last first.
          rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
          move => H_adj.
          case: H_dec.
          exact: adjacent_to_symmetric.
        exact: (recv_fail_other_fst s1 _ _ _ _ _ _ _ _ _ _ H3).
    + find_inversion.
      destruct d1.
      simpl in *.
      rewrite H7.
      rewrite /update2 /=.
      break_if; break_if => //=; first by break_and; rewrite H4 in n0.
      - break_and.
        rewrite H in H3.
        have H_f := Failure_not_failed_no_fail s1 _ H_in_n H_in_f to.
        rewrite H3 in H_f.
        by case: H_f; left.
      - by break_and; break_or_hyp.
      - case: o => o //.
        have H_neq: from <> to by move => H_eq'; rewrite H_eq' (Failure_self_channel_empty s1) in H3.
        case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
        case (In_dec name_eq_dec from failed0) => H_from_f; last first.
          have H_f := Failure_not_failed_no_fail s1 _ H_from_in H_from_f to.
          rewrite H3 in H_f.
          by case: H_f; left.
        have H_neq': to <> n by auto.
        have IH := H8 _ H_eq _ H2.
        case (adjacent_to_dec from to) => H_dec; last first.
          rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
          move => H_adj.
          case: H_dec.
          exact: adjacent_to_symmetric.
        exact: (recv_fail_other_snd s1 _ _ _ _ _ _ _ _ _ _ H3).
    + rewrite /update2.
      break_if; break_if => /=; first by break_and; break_and; rewrite -H6 in n1.      
      - break_and.
        by rewrite H4 in n1.
      - break_and.
        by rewrite H4 in n0.
      - exact: H8.
  * move: H6 H9.
    rewrite /update /=.
    break_if; break_if => H_eq H_eq'.
    + repeat find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; first by break_and; rewrite H (Failure_self_channel_empty s1) in H3.
      break_or_hyp => //.
      case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
      have IH := H8 _ H2 _ H2.
      case (adjacent_to_dec from to) => H_dec; last first.
        rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
        move => H_adj.
        case: H_dec.
        exact: adjacent_to_symmetric.
      rewrite (Failure_self_channel_empty s1).
      exact: (recv_new_self s1 _ _ _ _ _ _ H3).
    + repeat find_inversion.
      destruct d0.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; break_if; first by break_and; rewrite H6 in n0.
      - by break_and; rewrite H4 in n0.
      - break_and.
        have H_neq: from <> to by move => H_eq; rewrite H_eq (Failure_self_channel_empty s1) in H3.
        rewrite H in H3 H_neq.
        rewrite H.
        have IH := H8 _ H2 _ H_eq'.
        case (adjacent_to_dec n' to) => H_dec; last first.
          rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
          move => H_adj.
          case: H_dec.
          exact: adjacent_to_symmetric.
        exact: (recv_new_fst s1).
      - break_or_hyp => //.
        have IH := H8 _ H2 _ H_eq'.
        case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
        case (adjacent_to_dec from to) => H_dec; last first.
          rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
          move => H_adj.
          case: H_dec.
          exact: adjacent_to_symmetric.
        have H_neq: from <> to by move => H_eq; rewrite H_eq (Failure_self_channel_empty s1) in H3.
        exact: (recv_new_fst_other s1 _ _ _ _ _ _ _ _ _ H3).
    + find_inversion.
      destruct d1.
      simpl in *.
      rewrite H7.
      rewrite /update2.
      break_if; break_if; first by break_and; find_rewrite.
      - break_and.
        have H_neq: from <> to by move => H_eq'; rewrite H_eq' (Failure_self_channel_empty s1) in H3.
        rewrite H in H_neq H3.
        have IH := H8 _ H_eq _ H2.
        rewrite H.
        have H_neq': to <> n by auto.
        case (adjacent_to_dec to n) => H_dec; last by rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
        exact: (recv_new_snd s1).
      - by break_and; rewrite H4 in n0.
      - case: o => H_neq //.
        have IH := H8 _ H_eq _ H2.
        have H_neq': to <> n by auto.
        have H_neq'': from <> to by move => H_eq'; rewrite H_eq' (Failure_self_channel_empty s1) in H3.
        case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
        case (adjacent_to_dec from to) => H_dec; last first.
          rewrite (Failure_not_adjacent_no_incoming s1) // in H3.
          move => H_adj.
          case: H_dec.
          exact: adjacent_to_symmetric.
        exact: (recv_new_snd_other s1 _ _ _  _ _ _ _ _ _ H3).
    + rewrite /update2.
      break_if; break_if; first by break_and; rewrite H6 in n1.
      - by break_and; rewrite H4 in n1.
      - by break_and; rewrite H4 in n0.
      - exact: H8.
- move => H_in_n H_in_n' H_in_f H_in_f'.
  find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => H_in_n H_in_n' H_in_f H_in_f'.
  move => d0 H_eq d1 H_eq'.
  have H_neq: h <> n by auto.
  have H_neq': h <> n' by auto.
  have H_in'_f: ~ In n failed0 by auto.
  have H_in'_f': ~ In n' failed0 by auto.
  rewrite collate_neq //.
  rewrite collate_neq //.
  exact: IHs1.
Qed.

End DualNodeInv.

Lemma Failure_adjacent_to_no_incoming_new_n_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        adjacent_to n' n ->
        forall d, odnwState net n = Some d ->
         ~ In New (odnwPackets net n' n) ->
         NSet.In n' (adjacent d).
Proof.
move => onet failed tr H_st.
move => n n' H_in_n H_f H_in_n' H_f'.
move => H_adj d H_eq.
have H_adj': adjacent_to n n' by exact: adjacent_to_symmetric.
have H_neq: n' <> n by move => H_eq'; rewrite H_eq' in H_adj; apply adjacent_to_irreflexive in H_adj.
have [d' H_eq'] := ordered_dynamic_initialized_state H_st _ H_in_n'.
move: H_adj' H_neq {H_adj}.
pose P_curr (d0 : Data) (d1 : Data) (l0 : list Msg) (l1 : list Msg) :=
  adjacent_to n n' ->
  n' <> n -> ~ In New l1 -> NSet.In n' (adjacent d0).
rewrite -/(P_curr _ d' (odnwPackets onet n n') _).
move: H_eq'; generalize d' => {d'}.
move: H_eq; generalize d => {d}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' onet}.
- by intuition by eauto.
- by intuition by eauto.
- by auto with set.
- by auto with set.
- by auto with set.
Qed.

Lemma Failure_incoming_fail_then_incoming_new_or_in_adjacent : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
      (In New (net.(odnwPackets) n' n) /\ ~ NSet.In n' d.(adjacent)) \/ (~ In New (net.(odnwPackets) n' n) /\ NSet.In n' d.(adjacent)).
Proof.
move => net failed tr H_st.
move => n H_n H_f n' H_in d0 H_eq.
move: H_in.
pose P_curr (d : Data) (l : list Msg) :=
  In Fail l ->
  ((In New l /\ ~ NSet.In n' d.(adjacent)) \/
   (~ In New l /\ NSet.In n' d.(adjacent))).
rewrite -/(P_curr _ _).
move: H_eq; generalize d0 => {d0}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto with set.
- by firstorder.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_neq H_eq d H_eq' H_bef H_in.
  have H_le := Failure_le_one_fail H_st _ H_in_n H_in_f n'.
  rewrite H_eq /= in H_le.
  apply (@count_occ_In _ Msg_eq_dec) in H_in.
  by omega.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_from H_f_from H_neq H_neq' H_eq d H_eq' H_bef H_in.
  concludes.
  break_or_hyp; break_and.
    left; split => //.
    move => H_ins.
    by find_apply_lem_hyp NSetFacts.remove_3.
  right; split => //.
  exact: NSetFacts.remove_2.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_neq H_eq d H_eq' H_bef H_in.
  right.
  split; last by auto with set.
  have H_le := Failure_le_one_new H_st _ H_in_n H_in_f n'.
  rewrite H_eq /= in H_le.
  move => H_in'.
  apply (@count_occ_In _ Msg_eq_dec) in H_in'.
  by omega.
- move => net failed tr from ms H_st.
  move => H_in_n H_in_f H_in_from H_neq H_neq' H_eq d H_eq' H_bef H_in.
  concludes.
  break_or_hyp; break_and.
    left; split => //.
    by eauto with set.
  right.
  by eauto with set.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_adj H_neq d H_eq H_bef H_in.
  move {H_in H_bef}.
  case (in_dec Msg_eq_dec New (odnwPackets onet n' n)) => H_dec.
    have H_ins := Failure_new_incoming_not_in_adj H_st _ H_in_n H_in_f H_dec H_eq.
    left; split => //.
    apply in_or_app.
    by left.
  right.
  split.
    move => H_in.
    case: H_dec.
    apply in_app_or in H_in.
    case: H_in => H_in //.
    by case: H_in.
  move: H_dec.
  exact: (Failure_adjacent_to_no_incoming_new_n_adjacent H_st).
Qed. 

Lemma Failure_incoming_fail_then_new_or_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
       In New (net.(odnwPackets) n' n) \/ NSet.In n' (adjacent d).
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f n' H_in d H_eq.
have H_or := Failure_incoming_fail_then_incoming_new_or_in_adjacent H_st _ H_in_n H_in_f _ H_in H_eq.
break_or_hyp; break_and; first by left.
by right.
Qed.

Lemma Failure_head_fail_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', head (net.(odnwPackets) n' n) = Some Fail ->
   forall d, net.(odnwState) n = Some d -> 
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f n' H_eq d0 H_eq'.
move: H_eq.
pose P_curr (d : Data) (l : list Msg) :=
  hd_error l = Some Fail -> NSet.In n' (adjacent d).
rewrite -/(P_curr _ _).
move: H_eq'; generalize d0 => {d0}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_in_n failed H_in_f}.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq H_eq d H_eq' H_bef H_eq_f.
  destruct ms => //.
  destruct m => //.
  have H_cnt := Failure_le_one_fail H_st _ H_in_n H_in_f n'.
  rewrite H_eq /= in H_cnt.
  by omega.
- by auto with set.
- by auto with set.
- by auto with set.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_adj H_neq d H_eq H_bef H_eq'.
  case H_eqp: (odnwPackets onet n' n) => [|m ms].
    have H_s := Failure_adjacent_to_no_incoming_new_n_adjacent H_st H_in_n H_in_f H_in_n' H_in_f' H_adj H_eq.
    rewrite H_eqp in H_s.
    exact: H_s.
  rewrite H_eqp in H_eq'.
  destruct m => //.
  have H_f := Failure_not_failed_no_fail H_st _ H_in_n' H_in_f' n.
  rewrite H_eqp in H_f.
  by case: H_f; left.
Qed.

Lemma Failure_adjacent_or_incoming_new_reciprocal :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        forall d0, odnwState net n = Some d0 ->
        forall d1, odnwState net n' = Some d1 ->
        (NSet.In n' d0.(adjacent) \/ In New (net.(odnwPackets) n' n)) ->
        NSet.In n d1.(adjacent) \/ In New (net.(odnwPackets) n n').
Proof.
move => onet failed tr H_st.
move => n n' H_in_n H_f H_in_n' H_f'.
move => d0 H_eq d1 H_eq' H_ins.
have H_neq: n' <> n.
  move => H_eq_n.
  rewrite H_eq_n in H_ins.
  case: H_ins => H_ins; last by rewrite (Failure_self_channel_empty H_st) in H_ins.
  contradict H_ins.
  exact: (Failure_node_not_adjacent_self H_st).
move: H_neq H_ins.
pose P_curr (d : Data) (d' : Data) (l : list Msg) (l' : list Msg) :=
  n' <> n ->
  NSet.In n' (adjacent d) \/ In New l' ->
  NSet.In n (adjacent d') \/ In New l.
rewrite -/(P_curr _ _ _ _).
move: H_eq'; generalize d1 => {d1}.
move: H_eq; generalize d0 => {d0}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' onet}.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq H_neq'.
  case => //.
  move => H_ins.
  by apply NSetFacts.empty_1 in H_ins.
- move => onet failed tr H_st.
  move => H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq H_neq' H_bef.
  case: H_bef => H_bef //.
  apply (Failure_in_adj_adjacent_to H_st n) in H_bef => //.
  case: H_adj.
  exact: adjacent_to_symmetric.
- by auto with set.
- by auto with set.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq_n H_neq_from H_neq'_from H_in H_f H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_bef H_neq H_or.
  concludes.
  apply: H_bef.
  case: H_or => H_or; last by right.
  by left; find_apply_lem_hyp NSetFacts.remove_3.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq_n H_neq_from H_neq'_from H_in H_f H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_bef H_neq H_or.
  repeat concludes.
  case: H_bef => H_bef; last by right.
  left.
  exact: NSetFacts.remove_2.
- move => onet failed tr ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq_n H_adj H_eq d0 H_eq_d0 d1 H_eq_d1 H_bef H_neq' H_or.
  case (In_dec Msg_eq_dec New (odnwPackets onet n n')) => H_dec; first by right.
  left.
  apply adjacent_to_symmetric in H_adj.
  exact: (Failure_adjacent_to_no_incoming_new_n_adjacent H_st H_in_n').
- by auto with set.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq_n H_neq_from H_neq'_from H_f H_adj H_eq d0 H_eq_d0 d1 H_eq_d1 H_bef H_neq' H_or.
  concludes.
  apply: H_bef.
  case: H_or => H_or; last by right.
  left.
  by find_apply_lem_hyp NSetFacts.add_3.
- move => onet failed tr from ms H_st.
  move => H_in_n H_in_f H_in_n' H_in_f'.
  move => H_neq H_neq_from H_neq'_from H_from H_adj H_eq d0 H_eq_d0 d1 H_eq_d1 H_bef H_neq' H_or.
  repeat concludes.
  case: H_bef => H_bef; last by right.
  left.
  exact: NSetFacts.add_2.
Qed.

Lemma Failure_adjacent_then_adjacent_or_new_incoming :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        forall d0, odnwState net n = Some d0 ->
        forall d1, odnwState net n' = Some d1 ->
        NSet.In n' d0.(adjacent) ->
        NSet.In n d1.(adjacent) \/ In New (net.(odnwPackets) n n').
Proof.
move => net failed tr H_st.
move => n n' H_in_n H_in_f H_in_n' H_in_f'.
move => d0 H_eq_d0 d1 H_eq_d1 H_ins.
apply: (Failure_adjacent_or_incoming_new_reciprocal H_st _ H_in_n H_in_f H_in_n' H_in_f' H_eq_d0 H_eq_d1).
by left.
Qed.

Lemma Failure_fail_head_no_new :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
        forall n', head (net.(odnwPackets) n' n) = Some Fail ->
        ~ In New (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st. 
move => n H_in_n H_in_f n' H_eq.
have H_bef := Failure_in_after_all_fail_new H_st _ H_in_n H_in_f n'.
case (In_dec Msg_eq_dec New (odnwPackets net n' n)) => H_dec //.
destruct (odnwPackets net n' n) => //.
destruct m => //.
case: H_dec => H_dec //.
find_apply_lem_hyp in_split.
break_exists.
find_rewrite.
case: H_bef => H_bef.
  case: H_bef.
  apply in_or_app.
  by right; left.
by break_and.
Qed.

Lemma Failure_failed_adjacent_fail :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In n' failed ->
      forall d0, odnwState net n = Some d0 ->
      (NSet.In n' d0.(adjacent) \/ In New (net.(odnwPackets) n' n)) ->
      In Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f n' H_in_f' d0 H_eq_d0 H_or.
case: H_or => H_or.
  have H_c := Failure_in_adj_or_incoming_fail H_st _ H_in_n H_in_f H_eq_d0 H_or.
  by case: H_c => H_c; break_and.
exact: (Failure_in_new_failed_incoming_fail H_st _ H_in_n H_in_f _ H_in_f' H_or).
Qed.

Lemma Failure_in_new_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In New (odnwPackets net n' n) ->
            adjacent_to n' n.
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  In New l -> adjacent_to n' n.
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- move => onet failed tr ms H_st H_n H_f H_n' H_f' H_neq H_eq d H_eq' H_bef H_in.
  have H_bef' := Failure_in_after_all_fail_new H_st _ H_n H_f n'.
  rewrite H_eq /= in H_bef'.
  by break_or_hyp; break_and.
- move => net failed tr ms H_st H_n H_f H_n' H_neq H_eq d H_eq' H_bef H_in.
  have H_cnt := Failure_le_one_new H_st _ H_n H_f n'.
  rewrite H_eq /= in H_cnt.
  apply (@count_occ_In _ Msg_eq_dec) in H_in .
  by omega.
Qed.

Lemma Failure_inactive_not_in_adjacent :
forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed ->
  forall n', ~ In n' (odnwNodes net) ->
  forall d0, odnwState net n = Some d0 ->
  ~ NSet.In n' d0.(adjacent).
Proof.
move => net failed tr H.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3 4}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n H_in H_f n' H_in' d0 H_eq H_ins {H1}.
  destruct_update; repeat find_injection.
  * unfold InitData in *.
    simpl in *.
    by find_apply_lem_hyp NSetFacts.empty_1.
  * break_or_hyp => //.
    have H_neq: h <> n' by eauto.
    have H_inn: ~ In n' net0.(odnwNodes) by eauto.
    contradict H_ins.
    by eauto.
- move {H1}.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  * destruct_update; repeat find_injection; last by eauto.
    find_rewrite.
    case (name_eq_dec from n') => H_dec; first by subst; find_apply_lem_hyp NSetFacts.remove_1.
    find_apply_lem_hyp NSetFacts.remove_3.
    by eauto.
  * destruct_update; repeat find_injection; last by eauto.
    find_rewrite.
    case (name_eq_dec from n') => H_dec; first by subst; find_rewrite_lem (ordered_dynamic_no_outgoing_uninitialized H _ H10).
    find_apply_lem_hyp NSetFacts.add_3 => //.
    by eauto.
- by find_apply_lem_hyp input_handlers_IOHandler.
- by eauto.
Qed.

End FailureRecorderCorrect.
