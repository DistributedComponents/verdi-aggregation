Require Import Verdi.
Require Import HandlerMonad.
Require Import NameOverlay.

Require Import Sumbool.

Require Import TotalMapSimulations.

Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.

Require Import UpdateLemmas.

Require Import OrderedLemmas.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Set Implicit Arguments.

Section OrderedDynamicFailure.

Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {overlay_params : NameOverlayParams multi_params}.
Context {new_msg_params : NewMsgParams multi_params}.
Context {fail_msg_params : FailMsgParams multi_params}.

Lemma ordered_dynamic_uninitialized_state : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, ~ In n (odnwNodes net) ->
 odnwState net n = None.
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update_opt /=.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_not_in: ~ In n (odnwNodes net0) by move => H_not_in; case: H_in; right.
  case eq_dec => H_dec; first by rewrite H_dec in H_neq.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update_opt /=.
  have H_neq: n <> to by move => H_eq; rewrite H_eq in H_in.
  case eq_dec => H_dec //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update_opt.
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  case eq_dec => H_dec //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_initialized_state : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 exists d, odnwState net n = Some d.
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  case: H_in => H_in.
    rewrite -H_in /update_opt.
    break_if => //.
    by exists (init_handlers h).
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  have [d H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  exists d.
  rewrite /update_opt /=.
  by break_if.
- move => n H_in.
  rewrite /update_opt.
  break_if; first by exists d'.
  have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  by exists d0.
- move => n H_in.
  rewrite /update_opt.
  break_if; first by exists d'.
  have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  by exists d0.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_failed_then_initialized : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n failed ->
 In n (odnwNodes net).
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {2}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  right.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  case: H_in => H_in; first by rewrite -H_in.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_state_not_initialized_not_failed : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, ~ In n (odnwNodes net) ->
 ~ In n failed.
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {1}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in.
  have H_not_in: ~ In n (odnwNodes net0) by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  move => H_or.
  case: H_or => H_or; first by repeat find_rewrite.
  contradict H_or.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma ordered_dynamic_no_outgoing_uninitialized :
forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n n' = [].
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_a n'. 
  have H_neq: h <> n by eauto.
  have H_not_in: ~ In n (odnwNodes net0) by eauto.
  rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; exact: not_in_exclude.
  rewrite collate_neq //.
  by eauto.
- move => n H_a n'.
  have H_neq: to <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  rewrite /update2.
  case sumbool_and => H_and; last by eauto.
  break_and; repeat find_rewrite.
  simpl in *.
  have IH := IHrefl_trans_1n_trace1 _ H_a.
  by find_higher_order_rewrite.
- move => n H_a n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  by eauto.
- move => n H_a n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
  rewrite collate_neq //.
  by eauto.
Qed.

Lemma ordered_dynamic_nodes_no_dup :
forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  NoDup (odnwNodes onet).
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /=.
  exact: NoDup_nil.
concludes => {H_init}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite //=.
exact: NoDup_cons.
Qed.

(* if neither input handler nor net handler produces msg_new or msg_fail, we can prove that 
   no msg_new or msg_fail will go to or from inactive nodes *)

End OrderedDynamicFailure.

Module FailureRecorder (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (Import ANT : AdjacentNameType NT).

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Inductive Msg : Set := 
| Fail : Msg
| New : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Input : Set := .

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Output : Set := .

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
Defined.

Definition NS := NSet.t.

Record Data := mkData { adjacent : NS }.

Definition InitData (n : name) := mkData NSet.empty.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| New =>
  put {| adjacent := NSet.add src st.(adjacent) |}
| Fail => 
  put {| adjacent := NSet.remove src st.(adjacent) |}
end.

Definition IOHandler (me : name) (i : Input) : Handler Data := nop.

Instance FailureRecorder_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance FailureRecorder_MultiParams : MultiParams FailureRecorder_BaseParams :=
  {
    name := name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := name_eq_dec ;
    nodes := nodes ;
    all_names_nodes := all_names_nodes ;
    no_dup_nodes := no_dup_nodes ;
    init_handlers := InitData ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Instance FailureRecorder_NameOverlayParams : NameOverlayParams FailureRecorder_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance FailureRecorder_FailMsgParams : FailMsgParams FailureRecorder_MultiParams :=
  {
    msg_fail := Fail
  }.

Instance FailureRecorder_NewMsgParams : NewMsgParams FailureRecorder_MultiParams :=
  {
    msg_new := New
  }.

Lemma net_handlers_NetHandler :
  forall dst src m st os st' ms,
    net_handlers dst src m st = (os, st', ms) ->
    NetHandler dst src m st = (tt, os, st', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    IOHandler h i d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma IOHandler_cases :
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) -> False.
Proof. by move => h; case. Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (msg = Fail /\ out = [] /\ ms = [] /\
    st'.(adjacent) = NSet.remove src st.(adjacent)) \/
    (msg = New /\ out = [] /\ ms = [] /\
     st'.(adjacent) = NSet.add src st.(adjacent)).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg; monad_unfold => /= H_eq.
- by left; find_inversion.
- by right; find_inversion.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases.

Lemma Failure_self_channel_empty : 
forall onet failed tr, 
 step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
 forall n, onet.(odnwPackets) n n = [].
Proof.
move => onet failed tr H.
remember step_o_d_f_init as y in *.
have ->: onet = snd (failed, onet) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl.
- move => n.
  case (name_eq_dec h n) => H_dec; last by rewrite collate_ls_neq_to // collate_neq.
  rewrite H_dec collate_ls_not_related; last exact: adjacent_to_irreflexive.
  by rewrite collate_map_pair_not_related; last exact: adjacent_to_irreflexive.
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
  rewrite collate_map_pair_not_related //; last exact: adjacent_to_irreflexive.
Qed.

Lemma Failure_node_not_adjacent_self : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 ~ In n failed ->
 forall d, odnwState net n = Some d ->
 ~ NSet.In n d.(adjacent).
Proof.
move => net failed tr H.
remember step_o_d_f_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {1 3}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes.
move {H1}.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in H_f d.
  rewrite /update_opt /=.
  case name_eq_dec => H_dec.
    rewrite /InitData.
    case => H_eq.
    rewrite -H_eq.
    by auto with set.
  case: H_in => H_in; first by rewrite H_in in H_dec.
  by auto.
- find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update_opt /= => n.
  case name_eq_dec => H_dec; last by find_apply_hyp_goal.
  find_rewrite.
  net_handler_cases.
    find_injection.
    find_rewrite.
    find_apply_lem_hyp NSet.remove_spec.
    break_and.
    by eauto.
  find_injection.
  find_rewrite.
  have H_neq: from <> to by move => H_eq; repeat find_rewrite; find_erewrite_lem Failure_self_channel_empty.
  find_apply_lem_hyp NSet.add_spec.
  break_or_hyp; first by unfold NSet.E.eq in *; find_rewrite.
  by eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- by eauto.
Qed.

Lemma Failure_not_failed_no_fail :
forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  forall n, In n (odnwNodes onet) -> ~ In n failed ->
  forall n', ~ In Fail (onet.(odnwPackets) n n').
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3}H_eq_o {H_eq_o}.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl.
- move => n H_a H_f n'.
  simpl in *.
  break_or_hyp.
    case (name_eq_dec n n') => H_dec.
      rewrite -H_dec {H_dec n'}.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; exact: not_in_exclude.
      rewrite collate_map_pair_notin; last exact: not_in_exclude.
      by rewrite (Failure_self_channel_empty H).      
    rewrite collate_ls_neq_to //.
    case (adjacent_to_dec n n') => H_dec'.
      case (In_dec name_eq_dec n' failed) => H_in_f.
        rewrite collate_map_pair_in_failed //.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H).
      case (In_dec name_eq_dec n' (odnwNodes net)) => H_in.
        rewrite collate_map_pair_live_related //; last exact: (ordered_dynamic_nodes_no_dup H).
        move => H_in'.
        find_apply_lem_hyp in_app_or.
        simpl in *.
        break_or_hyp; last by break_or_hyp.
        contradict H0.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
      rewrite collate_map_pair_notin; last exact: not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
    rewrite collate_map_pair_not_related //. 
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H).
  have H_neq: h <> n by move => H_eq; repeat find_rewrite.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec {n' H_dec}.
    case (adjacent_to_dec h n) => H_dec.
      rewrite collate_ls_nodup_in.
      * rewrite collate_neq //.
        move => H_in.
        find_apply_lem_hyp in_app_or.
        simpl in *.
        break_or_hyp; last by break_or_hyp.
        contradict H3.
        by eauto.
      * apply: nodup_filter_rel.
        apply: nodup_exclude.
        by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
      * apply: related_filter_rel => //.
        exact: In_n_exclude.
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n' n = [].
Proof.
move => onet failed tr H.
have ->: onet = snd (failed, onet) by [].
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in n'.
  have H_neq: h <> n by eauto.
  have H_not_in: ~ In n (odnwNodes net) by eauto.
  rewrite collate_ls_neq_to //.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
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
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
    by auto.
  rewrite collate_neq //.
  by auto.
Qed.

Section SingleNodeInv.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_d_f_star step_o_d_f_init (failed, onet) tr.

Variable n : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_fail : 
  forall onet failed tr n',
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    forall d, onet.(odnwState) n = Some d ->
    P d ->
    P (mkData (NSet.remove n' d.(adjacent))).

Hypothesis recv_new : 
  forall onet failed tr n',
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
remember step_o_d_f_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_o_d_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_a H_f d.
  rewrite /update_opt /=.
  case name_eq_dec => H_dec H_eq; first by find_inversion.
  by break_or_hyp; eauto.
- simpl in *.
  rewrite /update_opt.
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
  rewrite /update_opt.
  find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- move => H_a H_f.
  by eauto.
Qed.

End SingleNodeInv.

Section SingleNodeInvOut.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_d_f_star step_o_d_f_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init_empty : P (InitData n) [].

Hypothesis after_init_adjacent : P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n' onet.(odnwNodes) ->
  ~ In n failed ->
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
remember step_o_d_f_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_o_d_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => H_a H_f d.
  rewrite /update_opt /=.
  case name_eq_dec => H_dec H_eq.
    repeat find_rewrite.
    find_injection.
    case (name_eq_dec h n') => H_dec.
      repeat find_reverse_rewrite.
      rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
      rewrite collate_map_pair_not_related; last exact: adjacent_to_irreflexive.
      by rewrite (Failure_self_channel_empty s1).
    rewrite collate_ls_neq_to //.
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_map_pair_notin; last exact: not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_map_pair_notin //; last exact: in_not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (adjacent_to_dec h n') => H_dec'.
      rewrite collate_map_pair_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    rewrite collate_map_pair_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
  break_or_hyp => //.
  set f := collate _ _ _.
  have H_eq_f: f n n' = odnwPackets net n n' by rewrite /f collate_neq //; auto.
  rewrite (collate_ls_f_eq _ _ _ _ _ _ _ H_eq_f) {H_eq_f f}.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_ls_neq_to //; eauto.  
  repeat find_reverse_rewrite.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_ls_not_related //; eauto.
  rewrite collate_ls_nodup_in.
  * have H_p: P d (odnwPackets net n h) by eauto.
    move: H_p.
    rewrite (Failure_inactive_no_incoming s1) //=.
    by eauto.
  * apply: nodup_filter_rel.
    apply: nodup_exclude.
    by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
  * apply: related_filter_rel => //.
    exact: In_n_exclude.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => /=.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) in H3.
    case (in_dec name_eq_dec from failed0) => H_from_failed; last first.
      have H_f := Failure_not_failed_no_fail s1 _ H_from_nodes H_from_failed to.
      rewrite H3 in H_f.
      by case: H_f; left.
    have H_neq: from <> to by move => H_eq; rewrite H_eq in H_from_failed.      
    move: H6.
    rewrite /update_opt.
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
    rewrite /update_opt.
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

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_d_f_star step_o_d_f_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis after_init_new : P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  ~ In n' onet.(odnwNodes) ->  
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
remember step_o_d_f_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_o_d_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => H_a H_f d.
  rewrite /update_opt /=.
  case name_eq_dec => H_dec H_eq.
    repeat find_rewrite.
    find_injection.
    case (name_eq_dec h n') => H_dec.
      repeat find_reverse_rewrite.
      rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
      rewrite collate_map_pair_not_related; last exact: adjacent_to_irreflexive.
      by rewrite (Failure_self_channel_empty s1).
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_ls_not_in_related; last exact: not_in_exclude.
      rewrite collate_neq //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_ls_in_excluded //.
      rewrite collate_neq //.
      by rewrite (Failure_inactive_no_incoming s1).
    case (adjacent_to_dec h n') => H_dec'; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Failure_inactive_no_incoming s1).
    rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite collate_neq //.
    by rewrite (Failure_inactive_no_incoming s1).
  have H_neq: h <> n by auto.
  rewrite collate_ls_neq_to //.
  break_or_hyp => //.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_neq //; exact: IHs1.
  rewrite -H_dec'.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_map_pair_not_related //; rewrite H_dec'; exact: IHs1.
  rewrite collate_map_pair_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
  have IH := IHs1 H H_f _ H_eq.
  move: IH.
  rewrite -H_dec'.
  rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1) //=.
  rewrite H_dec' in H0.
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
    rewrite /update_opt.
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
    rewrite /update_opt.
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
    case (adjacent_to_dec n' n) => H_dec'; last by rewrite collate_map_pair_not_related //; exact: IHs1.
    rewrite collate_map_pair_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite H_dec in H_neq H0 H1.
    apply (send_fail s1) => //.
    exact: IHs1.
  rewrite collate_neq //.
  exact: IHs1.
Qed.
      
End SingleNodeInvIn.

Lemma Failure_in_after_all_fail_new : 
forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), In_all_before New Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
  In_all_before New Fail l.
rewrite -/(P_curr d _ ).
move: H_d; generalize d => {d}.
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f} => /=.
- by auto.
- by auto.
- move => onet failed tr ms H_st H_in H_f H_in' H_f' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq in H_bef.
  apply head_before_all_not_in in H_bef => //.
  exact: not_in_all_before.
- move => onet failed tr ms H_st H_in H_f H_in' H_neq H_eq d H_eq' H_bef.
  rewrite H_eq in H_bef.
  rewrite /= in H_bef.
  break_or_hyp; last by break_and.
  exact: not_in_all_before.
- move => onet failed tr H_st H_in H_f H_in' H_f' H_adj H_neq d H_eq H_bef.
  exact: append_neq_before_all.
Qed.

Lemma Failure_le_one_new : 
forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
  rewrite count_occ_app_split /=.
  by ring_simplify.
Qed.

Lemma Failure_le_one_fail : 
forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
  rewrite count_occ_app_split /=.
  have H_not_in := Failure_not_failed_no_fail H_st _ H_in' H_f' n.
  have H_cnt := @count_occ_not_In _ Msg_eq_dec.
  apply H_cnt in H_not_in.
  rewrite H_not_in.
  by auto with arith.
Qed.

(*
Lemma Failure_in_adj_or_incoming_fail :
forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
       forall d, onet.(odnwState) n = Some d ->
            NSet.In n' d.(adjacent) ->
            (In n' (odnwNodes onet) /\ ~ In n' failed) \/ (In n (odnwNodes onet) /\ In n' failed /\ In Fail (onet.(odnwPackets) n' n)).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 5}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /= {H_init}.
  move => n n' H_ins.
  by left.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => n n' H_in_f H_ins.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.  
  rewrite /= /update2 {H1}.
  case (sumbool_and _ _ _ _) => H_dec.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' {H_eq H_eq' to from} in H7 H_ins H3 H2.
    rewrite /= in IHrefl_trans_1n_trace1.
    move: H_ins.
    rewrite /update' /=.
    case name_eq_dec => H_dec //.
    move => H_ins.
    case: d H7 H_ins => /= adjacent0 H_eq H_adj.
    rewrite H_eq in H_adj.
    by apply NSetFacts.remove_1 in H_adj.
  move: H_ins.
  rewrite /update' /=.
  case name_eq_dec => H_dec'.
    case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
    case: d H7 => /= adjacent0 H_eq.
    move => H_ins.
    rewrite H_eq {adjacent0 H_eq} in H_ins.
    rewrite -H_dec' {to H_dec'} in H2 H3 H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  move => H_ins.
  exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
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
    rewrite collate_map_pair_live_related //.
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


Lemma Failure_new_incoming_not_in_adj :
forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
- move => H_or.
  exact: NSetFacts.empty_1.
- move => onet failed tr H_st H_in H_f H_in' d H_eq H_bef H_or.
  
  apply: H_bef.


Lemma in_queue_not_in_adj_churn : forall (S5 : S), churn_net_ok S5 -> 
  forall (s5 : s), In s5 S5 -> 
  forall (j : i), 
  In_queue (msg_new j) (churn_mbox s5) -> 
  ~ ISet.In j (churn_adj s5).
*)

End FailureRecorder.
