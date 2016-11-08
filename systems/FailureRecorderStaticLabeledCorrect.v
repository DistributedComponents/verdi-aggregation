Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.

Require Import NameAdjacency.
Require Import FailureRecorderStaticLabeled.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.

Require Import Sumbool.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module FailureRecorderCorrect (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (Import ANT : AdjacentNameType NT) (Import A : Adjacency NT NOT NSet ANT).

Module FR := FailureRecorder NT NOT NSet ANT A.
Import FR.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Lemma Failure_node_not_adjacent_self : 
forall net failed tr n, 
 step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
 ~ In n failed ->
 ~ NSet.In n (onwState net n).(adjacent).
Proof.
move => net failed tr n H.
remember step_ordered_failure_init as y in *.
have ->: failed = fst (failed, net) by [].
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_ordered_failure_init /=.
  move => H_f.
  exact: not_adjacent_self.
move => H_f.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  rewrite /update /=.
  case name_eq_dec => H_dec /=; last exact: IHrefl_trans_1n_trace1.
  rewrite -H_dec in H3.
  net_handler_cases.
  find_apply_lem_hyp NSet.remove_spec.
  by break_and.
- by find_apply_lem_hyp input_handlers_IOHandler.
- exact: IHrefl_trans_1n_trace1.
Qed.

Lemma Failure_self_channel_empty : 
forall onet failed tr, 
 step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
 forall n, ~ In n failed ->
   onet.(onwPackets) n n = [].
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  rewrite /= /update2.
  case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
  move: H_dec => [H_dec H_dec'].
  rewrite H_dec H_dec' in H2.
  by rewrite IHrefl_trans_1n_trace1 in H2.
- by find_apply_lem_hyp input_handlers_IOHandler.
- move => n H_in.
  rewrite collate_neq.
  apply: IHrefl_trans_1n_trace1.
    move => H_in'.
    case: H_in.
    by right.
  move => H_eq.
  by case: H_in; left.
Qed.

Lemma Failure_not_failed_no_fail :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
move => n n' H_in.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  simpl in *.
  contradict H4.
  have H_in' := IHrefl_trans_1n_trace1 _ n' H_in.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec //.
  move: H_dec => [H_eq H_eq'].
  rewrite H_eq H_eq' in H2.
  rewrite H2 in H_in'.
  move => H_inn.
  case: H_in'.
  by right.
- by find_apply_lem_hyp input_handlers_IOHandler.
- rewrite /= in H_in.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_f: ~ In n failed by move => H_in''; case: H_in; right.
  rewrite collate_neq //.
  exact: IHrefl_trans_1n_trace1.
Qed.

Section SingleNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_failure_star step_ordered_failure_init (failed, onet) tr.

Variable n : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_fail : 
  forall onet failed tr n',
    step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) ->
    P (mkData (NSet.remove n' (onet.(onwState) n).(adjacent))).

Theorem P_inv_n : P (onwState onet n).
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_ordered_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  rewrite /update /=.
  case name_eq_dec => H_dec //.
  repeat find_rewrite.
  destruct d.
  simpl in *.
  aggressive_rewrite_goal.
  exact: (recv_fail _ H'_step1).
- by find_apply_lem_hyp input_handlers_IOHandler.
- move => H_in_f.
  apply: IHH'_step1.
  move => H'_in_f.
  case: H_in_f.
  by right.
Qed.

End SingleNodeInv.

Section SingleNodeInvOut.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_failure_star step_ordered_failure_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  ~ In n failed ->
  In n' failed ->
  n' <> n ->
  onet.(onwPackets) n' n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (NSet.remove n' (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n n').

Hypothesis recv_fail_from_neq :
  forall onet failed tr from ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  from <> n ->
  from <> n' ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (NSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n n').

Theorem P_inv_n_out : P (onet.(onwState) n) (onet.(onwPackets) n n').
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_ordered_failure_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  rewrite /update /=.
  case name_eq_dec => H_dec.
    rewrite -H_dec in H1 H6 H0.
    rewrite -H_dec /update2 /= {H_dec to H'_step2}.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq {H_eq from} in H6 H0. 
      by rewrite (Failure_self_channel_empty H'_step1) in H0.
    case: d H6 => /=.
    move => adjacent0 H_eq.
    rewrite H_eq {adjacent0 H_eq}.
    case: H_dec => H_dec.
      case (name_eq_dec from n') => H_dec'.
        rewrite H_dec'.
        rewrite H_dec' in H0 H_dec.
        case (In_dec name_eq_dec n' failed) => H_in; first exact: (recv_fail_from_eq H'_step1 _ _ _ H0).
        have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
        rewrite H0 in H_inl.
        by case: H_inl; left.
      case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_from_neq H'_step1 _ _ _ _ H0).
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.      
    case (name_eq_dec from n) => H_neq; first by rewrite H_neq (Failure_self_channel_empty H'_step1) in H0.
    case (name_eq_dec from n') => H_dec'.
      rewrite H_dec'.
      rewrite H_dec' in H0 H_dec.
      case (In_dec name_eq_dec n' failed) => H_in; first by apply: (recv_fail_from_eq H'_step1 _ _ _ H0) => //; auto.
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_from_neq H'_step1 _ _ _ _ H0).
    have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
    rewrite H0 in H_inl.
    by case: H_inl; left.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_eq H_eq'].
  rewrite H_eq H_eq' in H0 H1 H5 H_dec.
  have H_f := Failure_not_failed_no_fail H'_step1 _ n' H_in_f.
  rewrite H0 in H_f.
  by case: H_f; left.
- by find_apply_lem_hyp input_handlers_IOHandler.
- move => H_in.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_f: ~ In n failed by move => H_in'; case: H_in; right.
  rewrite collate_neq //.
  exact: IHH'_step1.
Qed.

End SingleNodeInvOut.

Section SingleNodeInvIn.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_failure_star step_ordered_failure_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_fail_neq :
  forall onet failed tr ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  ~ In n failed ->
  In n' failed ->
  n <> n' ->
  onet.(onwPackets) n' n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (NSet.remove n' (onet.(onwState) n).(adjacent))) ms.

Hypothesis recv_fail_other_neq :
  forall onet failed tr from ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  ~ In n failed ->
  n <> from ->
  n' <> from ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (NSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n' n).

Hypothesis fail_adjacent :
  forall onet failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    n' <> n ->
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (onwState onet n) (onwPackets onet n' n ++ [Fail]).

Theorem P_inv_n_in : P (onet.(onwState) n) (onet.(onwPackets) n' n).
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_ordered_failure_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  rewrite /update /=.
  case name_eq_dec => H_dec.
    rewrite -H_dec in H1 H6 H0.
    have H_neq: n <> from.
      move => H_eq.
      rewrite -H_eq in H0.
      by rewrite (Failure_self_channel_empty H'_step1) in H0.
    rewrite -H_dec /update2 /= {H_dec to H'_step2}.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq {H_eq from} in H0 H6 H_neq.
      case: d H6 => /= adjacent0 H_eq.
      rewrite H_eq {H_eq adjacent0}.
      case (In_dec name_eq_dec n' failed) => H_in; first exact: (recv_fail_neq H'_step1).
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    case: H_dec => H_dec //.
    case: d H6 => /= adjacent0 H_eq.
    rewrite H_eq {H_eq adjacent0}.
    apply: (recv_fail_other_neq H'_step1 _ _ _ H0) => //.
    move => H_neq'.
    by case: H_dec.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_eq H_eq'].
  by rewrite H_eq' in H_dec.
- by find_apply_lem_hyp input_handlers_IOHandler.
- move => H_in.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_f: ~ In n failed by move => H_in'; case: H_in; right.
  case (name_eq_dec h n') => H_dec.
    rewrite H_dec in H0 H_neq H_f.
    rewrite H_dec {H_dec h H'_step2 H_in}.
    case (adjacent_to_dec n' n) => H_dec.
      rewrite collate_map2snd_not_in_related //.
      * apply (fail_adjacent H'_step1) => //.
        exact: IHH'_step1.
      * exact: all_names_nodes.
      * exact: no_dup_nodes.
    rewrite collate_map2snd_not_related //.
    exact: IHH'_step1.
  rewrite collate_neq //.
  exact: IHH'_step1.
Qed.

End SingleNodeInvIn.

Section DualNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_failure_star step_ordered_failure_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

(* FIXME *)
Hypothesis after_init : P (InitData n) (InitData n') [] [].

Hypothesis recv_fail_self :
  forall onet failed tr from ms,
    step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    n' = n ->
    ~ In n failed ->
    onet.(onwPackets) from n = Fail :: ms ->
    n <> from ->
    P (onet.(onwState) n) (onet.(onwState) n) (onet.(onwPackets) n n) (onet.(onwPackets) n n) ->
    P (mkData (NSet.remove from (onet.(onwState) n).(adjacent)))
      (mkData (NSet.remove from (onet.(onwState) n).(adjacent)))
      (onet.(onwPackets) n n) (onet.(onwPackets) n n).

Hypothesis recv_fail_other :
  forall onet failed tr from ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    ~ In n failed ->
    ~ In n' failed ->
    onet.(onwPackets) from n = Fail :: ms ->
    n <> n' ->
    from <> n ->
    from <> n' ->
    P (onet.(onwState) n) (onet.(onwState) n') (onet.(onwPackets) n n') (onet.(onwPackets) n' n) ->
    P (mkData (NSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwState) n')
      (onet.(onwPackets) n n') (onet.(onwPackets) n' n).

Hypothesis recv_other_fail :
  forall onet failed tr from ms,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    ~ In n failed ->
    ~ In n' failed ->
    onet.(onwPackets) from n' = Fail :: ms ->
    n <> n' ->
    from <> n ->
    from <> n' ->
    P (onet.(onwState) n) (onet.(onwState) n') (onet.(onwPackets) n n') (onet.(onwPackets) n' n) ->
    P (onet.(onwState) n) (mkData (NSet.remove from (onet.(onwState) n').(adjacent))) 
      (onet.(onwPackets) n n') (onet.(onwPackets) n' n).

Theorem P_dual_inv : P (onet.(onwState) n) (onet.(onwState) n') (onet.(onwPackets) n n') (onet.(onwPackets) n' n).
Proof.
move: onet failed tr H_step not_failed_n not_failed_n'.
clear onet failed not_failed_n not_failed_n' tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {3 4 5 6}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_ordered_failure_init /= => H_in_f H_in_f'.
  exact: after_init.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- rewrite /= in IHH'_step1.
  move {H'_step2}.
  move => H_in_f H_in_f'.
  find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.
  rewrite /update /=.
  case name_eq_dec => H_dec_n.
    rewrite -H_dec_n.
    rewrite -H_dec_n {H_dec_n to} in H6 H7 H1 H0.
    case name_eq_dec => H_dec_n'.
      rewrite H_dec_n'.
      rewrite H_dec_n' in H_in_f' H7.
      rewrite /update2.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq in H0.
        by rewrite (Failure_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec //.
      case: d H6 => /= adjacent0 H_eq.
      rewrite H_eq {H_eq adjacent0}.
      apply (recv_fail_self H'_step1 H_dec_n' H1 H0) => //.
      move => H_neq.
      by rewrite H_neq in H_dec.
    case: d H6 => /= adjacent0 H_eq.
    rewrite H_eq {H_eq adjacent0}.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec'.
    * move: H_dec => [H_eq_n H_eq_n'].
      by rewrite H_eq_n' in H_dec_n'.
    * move: H_dec => [H_eq_n H_eq_n'].
      by rewrite H_eq_n' in H_dec_n'.    
    * move: H_dec' => [H_eq_n H_eq_n'].
      rewrite H_eq_n in H0.
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in_f'.
      case: H_inl.
      by rewrite H0; left.
    * case: H_dec' => H_dec' //.
      have H_neq: from <> n.
        move => H_eq'.
        rewrite H_eq' in H0.
        by rewrite (Failure_self_channel_empty H'_step1) in H0.
      move {H_dec}.
      apply (recv_fail_other H'_step1 H_in_f H_in_f' H0) => //.
      move => H_neq'.
      by rewrite H_neq' in H_dec_n'.
    case name_eq_dec => H_dec_n'.
      rewrite -H_dec_n'.
      rewrite -H_dec_n' {to H_dec_n'} in H0 H_dec_n H1 H6.
      case: d H6 => /= adjacent0 H_eq.
      rewrite H_eq {adjacent0 H_eq}.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec'.
      * move: H_dec' => [H_eq H_eq'].
        by rewrite H_eq' in H_dec_n.
      * move: H_dec => [H_eq H_eq'].
        rewrite H_eq in H0.
        have H_inl := Failure_not_failed_no_fail H'_step1 _ n' H_in_f.
        case: H_inl.
        rewrite H0.
        by left.
      * move: H_dec' => [H_eq H_eq'].
        by rewrite H_eq' in H_dec_n.
      * case: H_dec => H_dec //.
        have H_neq: from <> n'.
          move => H_eq'.
          rewrite H_eq' in H0.
          by rewrite (Failure_self_channel_empty H'_step1) in H0.
        move {H_dec'}.
        exact: (recv_other_fail H'_step1 H_in_f H_in_f' H0).
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec'.
      * move: H_dec => [H_eq H_eq'].
        by rewrite H_eq' in H_dec_n'.
      * move: H_dec => [H_eq H_eq'].
        by rewrite H_eq' in H_dec_n'.
      * move: H_dec' => [H_eq H_eq'].
        by rewrite H_eq' in H_dec_n.
      * exact: H7.
- rewrite /= in IHH'_step1.
  move {H'_step2}.
  move => H_in_f H_in_f'.
  find_apply_lem_hyp input_handlers_IOHandler; break_exists.
  by io_handler_cases.
- rewrite /= in IHH'_step1.
  move => H_nor H_nor'.
  have H_neq: h <> n.
    move => H_eq.
    case: H_nor.
    by left.
  have H_in_f: ~ In n failed.
    move => H_in_f.
    case: H_nor.
    by right.    
  have H_neq': h <> n'.
    move => H_eq.
    case: H_nor'.
    by left.
  have H_in_f': ~ In n' failed.
    move => H_in_f'.
    case: H_nor'.
    by right.
  have IH := IHH'_step1 H_in_f H_in_f'.
  move {H_nor H_nor' IHH'_step1}.
  rewrite collate_neq //.
  by rewrite collate_neq.
Qed.

End DualNodeInv.

Lemma Failure_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall (n n' : name),
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st.
move => n n' H_f.
pose P_curr (d : Data) := NSet.In n' d.(adjacent) -> adjacent_to n' n.
rewrite -/(P_curr _).
apply: (P_inv_n H_st); rewrite /P_curr //= {P_curr net tr H_st failed H_f}.
- move => H_ins.
  apply adjacent_to_node_adjacency in H_ins.
  apply filter_rel_related in H_ins.
  move: H_ins => [H_in H_adj].
  by apply adjacent_to_symmetric in H_adj.
- move => net failed tr n0 H_st H_in_f IH H_adj.
  apply: IH.
  by apply NSetFacts.remove_3 in H_adj.
Qed.

Lemma Failure_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 5}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /= {H_init}.
  move => n n' H_ins.
  by left.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => n n' H_in_f H_ins.
  find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases.  
  rewrite /= /update2 {H1}.
  case (sumbool_and _ _ _ _) => H_dec.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' {H_eq H_eq' to from} in H8 H_ins H3 H2.
    rewrite /= in IHrefl_trans_1n_trace1.
    move: H_ins.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    move => H_ins.
    case: d H8 H_ins => /= adjacent0 H_eq H_adj.
    rewrite H_eq in H_adj.
    by apply NSetFacts.remove_1 in H_adj.
  move: H_ins.
  rewrite /update /=.
  case name_eq_dec => H_dec'.
    case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
    case: d H8 => /= adjacent0 H_eq.
    move => H_ins.
    rewrite H_eq {adjacent0 H_eq} in H_ins.
    rewrite -H_dec' {to H_dec'} in H2 H3 H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  move => H_ins.
  exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler; break_exists.
  by io_handler_cases.
- move => n n' H_in_f H_ins.
  rewrite /= in IHrefl_trans_1n_trace1.
  have H_neq: h <> n.
    move => H_eq.
    case: H_in_f.
    by left.
  have H_in_f': ~ In n failed0.
    move => H_in.
    case: H_in_f.
    by right.  
  have IH := IHrefl_trans_1n_trace1 _ _ H_in_f' H_ins.
  case (name_eq_dec h n') => H_dec.
    rewrite H_dec.
    right.
    split; first by left.
    rewrite H_dec in H2.
    have H_adj := Failure_in_adj_adjacent_to H _ H_in_f' H_ins.
    rewrite collate_map2snd_not_in_related //.
    * apply in_or_app.
      by right; left.
    * exact: all_names_nodes.
    * exact: no_dup_nodes.
  case: IH => IH.
    left.
    move => H_or.
    by case: H_or => H_or.
  move: IH => [H_in H_fail].
  right.
  split; first by right.
  by rewrite collate_neq.
Qed.

Lemma Failure_le_one_fail : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st.
move => n n' H_in_f.
pose P_curr (d : Data) (l : list Msg) := 
  count_occ Msg_eq_dec l Fail <= 1.
rewrite -/(P_curr (onet.(onwState) n) _).
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_in_f}.
- by auto with arith.
- move => onet failed tr ms.
  move => H_st H_in_f H_in_f' H_neq H_eq IH.
  rewrite H_eq /= in IH.
  by omega.
- move => onet failed tr H_st H_neq H_in_f H_in_f'.
  move => H_adj IH.
  have H_f := Failure_not_failed_no_fail H_st _ n H_in_f'.
  have H_cnt : ~ count_occ Msg_eq_dec (onwPackets onet n' n) Fail > 0.
    move => H_cnt.
    by apply count_occ_In in H_cnt.
  have H_cnt_eq: count_occ Msg_eq_dec (onwPackets onet n' n) Fail = 0 by omega.
  rewrite count_occ_app /= H_cnt_eq.
  by auto with arith.
Qed.

Lemma Failure_adjacent_to_in_adj :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_f H_f'.
pose P_curr (d d' : Data) (l l' : list Msg) := 
  adjacent_to n' n -> 
  NSet.In n' d.(adjacent).
rewrite -/(P_curr _ (onet.(onwState) n') (onet.(onwPackets) n n')
 (onet.(onwPackets) n' n)).
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_f H_f'}.
- move => H_adj.
  apply adjacent_to_node_adjacency.
  apply related_filter_rel; first exact: all_names_nodes.
  exact: adjacent_to_symmetric.
- move => onet failed tr from ms H_st H_eq H_in_f H_eq' H_neq H_adj H_adj_to.
  rewrite H_eq in H_adj_to.
  contradict H_adj_to.
  exact: adjacent_to_irreflexive.
- move => onet failed tr from ms H_st H_in_f H_in_f' H_eq H_neq H_neq_f H_neq_f' IH H_adj.
  concludes.
  by apply NSetFacts.remove_2.
Qed.

Lemma Failure_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_in_f.
pose P_curr (d : Data) (l : list Msg) := 
  In Fail l ->
  NSet.In n' d.(adjacent).
rewrite -/(P_curr _ _).
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_in_f}.
- move => onet failed tr ms H_st H_in_f H_in_f' H_neq H_eq IH H_in.
  have H_cnt: count_occ Msg_eq_dec ms Fail > 0 by apply count_occ_In.
  have H_cnt': count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail > 1 by rewrite H_eq /=; auto with arith.
  have H_le := Failure_le_one_fail H_st _ n' H_in_f.
  by omega.
- move => onet failed tr from ms H_st H_in_f H_neq H_neq'.
  move => H_eq IH H_in.
  apply NSetFacts.remove_2; first by move => H_eq'; rewrite H_eq' in H_neq'.
  exact: IH.
- move => onet failed tr H_st H_neq H_in_f H_in_f' H_adj IH H_in.
  exact (Failure_adjacent_to_in_adj H_st H_in_f H_in_f' H_adj).
Qed.

Lemma Failure_first_fail_in_adj : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_in_f.
pose P_curr (d : Data) (l : list Msg) := 
  hd_error l = Some Fail ->
  NSet.In n' d.(adjacent).
rewrite -/(P_curr _ _).
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_in_f}.
- move => onet failed tr ms H_st H_in_f H_in_f' H_neq H_eq IH H_hd.
  have H_neq' := hd_error_some_nil H_hd.
  case: ms H_eq H_hd H_neq' => //.
  case => ms H_eq H_hd H_neq'.
  have H_cnt: count_occ Msg_eq_dec (onwPackets onet n' n) Fail > 1 by rewrite H_eq /=; auto with arith.
  have H_le := Failure_le_one_fail H_st _ n' H_in_f.
  by omega.
- move => onet failed tr from ms H_st H_in_f H_neq H_neq' H_eq IH H_hd.
  concludes.
  apply NSetFacts.remove_2 => //.
  move => H_eq'.
  by rewrite H_eq' in H_neq'.
- move => onet failed tr H_st H_neq H_in_f H_in_f' H_adj IH H_hd.
  by have H_a := Failure_adjacent_to_in_adj H_st H_in_f H_in_f' H_adj.
Qed.

Lemma Failure_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Failure_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

Definition head_message_enables_label m src dst l :=
  forall net failed, 
  ~ In dst failed ->
  head (net.(onwPackets) src dst) = Some m ->
  enabled lb_step_ordered_failure l (failed, net).

Lemma Fail_enables_RecvFail :
  forall src dst, head_message_enables_label Fail src dst (RecvFail dst src).
Proof.
move => src dst.
rewrite /head_message_enables_label.
move => net failed H_f H_eq.
case H_eq_p: (onwPackets net src dst) => [|m ms]; first by find_rewrite.
find_rewrite.
simpl in *.
find_injection.
rewrite /enabled.
case H_hnd: (@lb_net_handlers _ FailureRecorder_LabeledMultiParams dst src Fail (onwState net dst)) => [[[lb' out] d'] l].
have H_lb := H_hnd.
rewrite /lb_net_handlers /= in H_hnd.
by net_handler_cases => //;
 exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
Qed.

Lemma Tree_lb_step_ordered_failure_RecvFail_enabled :
  forall net net' net'' failed failed' failed'' tr tr' dst src l,
  l <> RecvFail dst src ->
  lb_step_ordered_failure (failed, net) l (failed', net') tr ->
  lb_step_ordered_failure (failed, net) (RecvFail dst src) (failed'', net'') tr' ->
  enabled lb_step_ordered_failure (RecvFail dst src) (failed', net').
Proof.
move => net net' net'' failed failed' failed'' tr tr' dst src l H_neq H_st H_st'.
destruct l => //.
- invcs H_st => //. 
  * by net_handler_cases.
  * invcs H_st' => //.
    have H_hd: head (onwPackets net' src dst) = Some Fail by net_handler_cases => //; find_injection; find_rewrite.
    have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
    exact: Fail_enables_RecvFail.
- invcs H_st' => //.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    net_handler_cases => //=; rewrite /update2.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
  exact: Fail_enables_RecvFail.
Qed.

Lemma Failure_RecvFail_enabled_weak_until_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvFail dst src) (hd s) ->
                  weak_until (now (l_enabled lb_step_ordered_failure (RecvFail dst src))) 
                             (now (occurred (RecvFail dst src))) 
                             s.
Proof.
cofix c.
case => /=.
case; case => failed net l tr s H_exec src dst.
case (Label_eq_dec l (RecvFail dst src)) => H_eq H_en.
- find_rewrite.
  exact: W0.
- apply: W_tl; first by [].
  apply: c; first by find_apply_lem_hyp lb_step_execution_invar.
  unfold l_enabled in *.
  unfold enabled in H_en.
  break_exists.
  destruct s as [e s].
  inversion H_exec; subst_max.
  inversion H5; subst.  
  destruct e, evt_a.
  destruct e', evt_a.
  destruct x.
  simpl in *.
  by apply: Tree_lb_step_ordered_failure_RecvFail_enabled; eauto.
Qed.

Lemma Failure_RecvFail_eventually_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvFail dst src) (hd s) ->
                  eventually (now (occurred (RecvFail dst src))) s.
Proof.
move => s H_exec H_fair src dst H_en.
have H_wu := Failure_RecvFail_enabled_weak_until_occurred H_exec H_en.
apply weak_until_until_or_always in H_wu.
case: H_wu; first exact: until_eventually.
move => H_al.
apply always_continuously in H_al.
apply H_fair in H_al => //.
destruct s as [x s].
by apply always_now in H_al.
Qed.

Lemma lb_step_ordered_failure_count_occ_Fail_neq_eq : 
  forall net net' failed failed' lb src dst k tr,
  lb <> RecvFail dst src ->
  count_occ msg_eq_dec (net.(onwPackets) src dst) Fail = k ->
  lb_step_ordered_failure (failed, net) lb (failed', net') tr ->
  count_occ msg_eq_dec (net'.(onwPackets) src dst) Fail = k.
Proof.
move => net net' failed failed' lb src dst k tr H_neq H_cnt H_step.
invcs H_step => //=.
net_handler_cases.
rewrite /collate /= /update2.
break_if => //.
break_and; subst.
by case: H_neq.
Qed.

Lemma lb_step_ordered_failure_count_occ_Fail_recv : 
  forall net net' failed failed' src dst k tr,  
  count_occ msg_eq_dec (net.(onwPackets) src dst) Fail = S k ->
  lb_step_ordered_failure (failed, net) (RecvFail dst src) (failed', net') tr ->
  count_occ msg_eq_dec (net'.(onwPackets) src dst) Fail = k.
Proof.
move => net net' failed failed' src dst k tr H_cnt H_step.
invcs H_step => //=.
net_handler_cases.
rewrite /= /update2.
break_if.
  break_and; subst.  
  rewrite H3 /= in H_cnt.
  by auto with arith.
find_injection.
by break_or_hyp.
Qed.

Lemma lb_step_ordered_failure_count_occ_Fail_le_monotonic : 
  forall net net' failed failed' lb src dst k tr,
  count_occ msg_eq_dec (net.(onwPackets) src dst) Fail <= k ->
  lb_step_ordered_failure (failed, net) lb (failed', net') tr ->
  count_occ msg_eq_dec (net'.(onwPackets) src dst) Fail <= k.
Proof.
move => net net' failed failed' lb src dst k tr H_cnt H_step.
invcs H_step => //=.
net_handler_cases.
rewrite /update2 /=.
break_if => //.
break_and.
repeat find_rewrite.
rewrite H3 /= in H_cnt.
by auto with arith.
Qed.

Lemma lb_step_ordered_failure_not_in_failed :
  forall net net' failed failed' lb tr h,
  ~ In h failed ->
  lb_step_ordered_failure (failed, net) lb (failed', net') tr ->
  ~ In h failed'.
Proof.
move => net net' failed failed' lb tr h H_in_f H_step.
by invcs H_step.
Qed.

Lemma Failure_not_in_failed_always : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall h, ~ In h (fst (hd s).(evt_a)) ->
       always (now (fun e => ~ In h (fst e.(evt_a)))) s.
Proof.
cofix c.
move => s H_exec.
inversion H_exec => /=.
move => h H_in_f.
apply: Always; first by [].
rewrite /=.
apply: c; first by [].
rewrite /=.
destruct e, e', evt_a, evt_a0.
simpl in *.
by eapply lb_step_ordered_failure_not_in_failed; eauto.
Qed.

Lemma Failure_lb_step_ordered_failure_fails_occ_monotonic : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall src dst k, 
         count_occ Msg_eq_dec ((snd (hd s).(evt_a)).(onwPackets) src dst) Fail <= k ->
         always (now (fun e => count_occ Msg_eq_dec ((snd e.(evt_a)).(onwPackets) src dst) Fail <= k)) s.
Proof.
cofix c.
move => s H_exec.
inversion H_exec => /=.
move => src dst k H_cnt.
apply: Always; first by [].
apply: c; first by [].
rewrite /=.
destruct e, e', evt_a, evt_a0.
simpl in *.
move: H.
exact: lb_step_ordered_failure_count_occ_Fail_le_monotonic.
Qed.

Lemma count_occ_fail_head :
  forall e src dst k,
  ~ In dst (fst (evt_a e)) ->
  count_occ Msg_eq_dec (onwPackets (snd (evt_a e)) src dst) Fail = S k ->
  l_enabled lb_step_ordered_failure (RecvFail dst src) e.
Proof.
case => /= [[failed net] lb] tr src dst k H_in_f H_cnt.
rewrite /l_enabled /= /enabled.
case H_m: (onwPackets net src dst) => [|m ms]; first by rewrite H_m in H_cnt.
destruct m.
case H_hnd: (@lb_net_handlers _ FailureRecorder_LabeledMultiParams dst src Fail (onwState net dst)) => [[[lb' out] d] l].
have H_lb := H_hnd.
rewrite /lb_net_handlers /= in H_hnd.
net_handler_cases.
exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d |}).
exists [].
by apply: LabeledStepOrderedFailure_deliver; eauto.
Qed.

Lemma Failure_eventually_fewer_Fail :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst k, ~ In dst (fst (hd s).(evt_a)) ->
                    count_occ Msg_eq_dec (onwPackets (snd (hd s).(evt_a)) src dst) Fail = S k ->
                    eventually (now (fun e => count_occ Msg_eq_dec (onwPackets (snd e.(evt_a)) src dst) Fail = k)) s.
Proof.
move => s H_exec H_fair src dst k H_in_f H_cnt.
have H_en := count_occ_fail_head _ _ _ H_in_f H_cnt.
apply Failure_RecvFail_eventually_occurred in H_en => //.
move: H_exec H_fair H_in_f H_cnt.
elim: H_en => {s}.
  case; case => /= [[failed net] lb] tr.
  case; case; case => /= failed' net' lb' tr' s.
  rewrite /occurred /= => H_eq.
  rewrite -H_eq {H_eq}.
  move => H_exec H_fair H_in H_cnt.
  apply: E_next.
  apply: E0.
  rewrite /=.
  inversion H_exec; subst_max.
  simpl in *.
  by eapply lb_step_ordered_failure_count_occ_Fail_recv; eauto.
move => e s H_ev IH H_exec H_fair H_in H_cnt.
inversion H_exec; subst.
destruct e, e'.
destruct evt_a as [failed net].
destruct evt_a0 as [failed' net'].
simpl in *.
case (Label_eq_dec (RecvFail dst src) evt_l) => H_eq.
  subst_max.
  apply: E_next.
  apply: E0.
  rewrite /=.
  by eapply lb_step_ordered_failure_count_occ_Fail_recv; eauto.
apply E_next.
apply IH.
- by [].
- by apply weak_local_fairness_invar in H_fair.
- by eapply lb_step_ordered_failure_not_in_failed; eauto.
- by eapply lb_step_ordered_failure_count_occ_Fail_neq_eq; eauto.
Qed.

Lemma Failure_lb_step_ordered_failure_eventually_le_0_fail :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst,
       ~ In dst (fst (hd s).(evt_a)) ->
       eventually (now (fun e => count_occ Msg_eq_dec ((snd e.(evt_a)).(onwPackets) src dst) Fail = 0)) s.
Proof.
move => s H_exec H_fair src dst H_in_f.
have H_ex: exists k, count_occ Msg_eq_dec (onwPackets (snd (evt_a (hd s))) src dst) Fail = k.
  case count_occ; first by exists 0.
  move => k.
  by exists (S k).
break_exists.
elim/(well_founded_ind lt_wf): x s H_exec H_fair H_in_f H.
case => [|k] IH s H_exec H_fair H_in_f H_cnt.
  apply: E0.
  by destruct s.
have H_k: k < S k by auto.
have IH' := IH _ H_k.
have H_ev := Failure_eventually_fewer_Fail H_exec H_fair src dst H_in_f H_cnt.
elim: H_ev H_exec H_fair H_in_f.
  move => s0 H_now H_exec H_fair H_in_f.
  apply: IH' => //.    
  rewrite /=.
  by destruct s0.
move => e s0 H_ev H_ev' H_exec H_fair H_in_f.
apply: E_next.
apply: H_ev'. 
- by apply lb_step_execution_invar in H_exec.
- by apply weak_local_fairness_invar in H_fair.
- inversion H_exec.
  destruct e, e'.
  destruct evt_a, evt_a0.
  simpl in *.
  by apply: lb_step_ordered_failure_not_in_failed; eauto.
Qed.

Lemma Failure_lb_step_ordered_failure_continuously_no_fail :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst,
       ~ In dst (fst (hd s).(evt_a)) ->
       continuously (now (fun e => ~ In Fail ((snd e.(evt_a)).(onwPackets) src dst))) s.
Proof.
move => s H_exec H_fair src dst H_in_f.
have H_ev := Failure_lb_step_ordered_failure_eventually_le_0_fail H_exec H_fair src dst H_in_f.
move: H_exec H_fair {H_in_f}.
elim: H_ev.
- move => s0 H_n H_exec H_fair.
  apply: E0.
  inversion H_exec.
  rewrite -H2 /now in H_n.
  have H_al := Failure_lb_step_ordered_failure_fails_occ_monotonic H_exec src dst.
  rewrite -H2 /= in H_al.
  have H_le_n: count_occ Msg_eq_dec (onwPackets (snd (evt_a e)) src dst) Fail <= 0 by rewrite H_n.
  have H_al' := H_al _ H_le_n.
  move: H_al' {H_al}.
  rewrite H2.
  generalize s0.
  apply: always_monotonic.
  case => e2 s2.
  rewrite /=.
  move => H_occ.
  apply (count_occ_not_In Msg_eq_dec _ Fail).
  by auto with arith.
- move => e s0 H_ev IH H_exec H_fair.
  apply: E_next.
  apply: IH; first by apply lb_step_execution_invar in H_exec.
  by apply weak_local_fairness_invar in H_fair.
Qed.

Lemma Failure_lb_step_ordered_failure_no_fails_step_star_ex :
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst,
       ~ In dst (fst (hd s).(evt_a)) ->
       continuously (now (fun e => 
         event_step_star step_ordered_failure step_ordered_failure_init e /\ 
         ~ In dst (fst e.(evt_a)) /\ 
         ~ In Fail ((snd e.(evt_a)).(onwPackets) src dst))) s.
Proof.
move => s H_star H_exec H_fair src dst H_in_f.
have H_al := step_ordered_failure_star_lb_step_execution H_star H_exec.
have H_al' := Failure_not_in_failed_always H_exec _ H_in_f.
apply always_continuously in H_al.
apply always_continuously in H_al'.
have H_cny := Failure_lb_step_ordered_failure_continuously_no_fail H_exec H_fair src _ H_in_f.
have H_both := continuously_and_tl H_al H_al'.
have H_both' := continuously_and_tl H_both H_cny.
move: H_both'.
apply continuously_monotonic.
case => /= e s0 H_and.
unfold now, and_tl in H_and.
by break_and.
Qed.

Lemma Failure_lb_step_ordered_failure_continuously_adj_not_failed :
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall n n',
       ~ In n (fst (hd s).(evt_a)) ->
       continuously (now (fun e => 
         NSet.In n' ((snd e.(evt_a)).(onwState) n).(adjacent) -> 
         ~ In n' (fst e.(evt_a)) /\ adjacent_to n' n)) s.
Proof.
move => s H_star H_exec H_fair n n' H_in_f.
have H_cny := Failure_lb_step_ordered_failure_no_fails_step_star_ex H_star H_exec H_fair n' _ H_in_f.
move: H_cny.
apply continuously_monotonic.
case => /= e s0 H_and H_ins.
break_and.
destruct e, evt_a.
unfold event_step_star in *.
simpl in *.
break_exists.
have H_adj := Failure_in_adj_or_incoming_fail H _ H0 H_ins.
break_or_hyp; last by break_and.
split => //.
by eapply Failure_in_adj_adjacent_to; eauto.
Qed.

End FailureRecorderCorrect.
