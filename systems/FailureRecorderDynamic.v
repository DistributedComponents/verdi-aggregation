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
  case name_eq_dec => H_dec; first by rewrite H_dec in H_neq.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update_opt /=.
  have H_neq: n <> to by move => H_eq; rewrite H_eq in H_in.
  case name_eq_dec => H_dec //.
  exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite /= in IHrefl_trans_1n_trace1.
  rewrite /update_opt.
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  case name_eq_dec => H_dec //.
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
    case name_eq_dec => H_dec //.
    by exists (init_handlers h).
  have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
  have [d H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  exists d.
  rewrite /update_opt /=.
  by case name_eq_dec.
- move => n H_in.
  rewrite /update_opt.
  case name_eq_dec => H_dec; first by exists d'.
  have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
  by exists d0.
- move => n H_in.
  rewrite /update_opt.
  case name_eq_dec => H_dec; first by exists d'.
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
  rewrite collate_ls_not_in; last by apply: not_in_not_in_adjacent_to_node; exact: not_in_exclude.
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

Module A := Adjacency NT NOT NSet ANT.
Import A.

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
  rewrite H_dec collate_ls_not_adjacent; last exact: adjacent_to_irreflexive.
  by rewrite collate_msg_for_not_adjacent; last exact: adjacent_to_irreflexive.
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
  rewrite collate_msg_for_not_adjacent //; last exact: adjacent_to_irreflexive.
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
      rewrite collate_ls_not_in; last by apply: not_in_not_in_adjacent_to_node; exact: not_in_exclude.
      rewrite collate_msg_for_notin; last exact: not_in_exclude.
      by rewrite (Failure_self_channel_empty H).      
    rewrite collate_ls_neq_to //.
    case (adjacent_to_dec n n') => H_dec'.
      case (In_dec name_eq_dec n' failed) => H_in_f.
        rewrite collate_msg_for_in_failed //.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H).
      case (In_dec name_eq_dec n' (odnwNodes net)) => H_in.
        rewrite collate_msg_for_live_adjacent //; last exact: (ordered_dynamic_nodes_no_dup H).
        move => H_in'.
        find_apply_lem_hyp in_app_or.
        simpl in *.
        break_or_hyp; last by break_or_hyp.
        contradict H0.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
      rewrite collate_msg_for_notin; last exact: not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ H). 
    rewrite collate_msg_for_not_adjacent //. 
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
      * apply: nodup_adjacent_to_node.
        apply: nodup_exclude.
        by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
      * apply: adjacent_to_adjacent_to_node => //.
        exact: In_n_exclude.
    rewrite collate_ls_not_in; last by move => H_in; find_apply_lem_hyp adjacent_to_node_adjacent_to; break_and.
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
    rewrite collate_msg_for_notin; last exact: not_in_exclude.
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
    rewrite collate_msg_for_notin; last exact: not_in_exclude.
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
  adjacent_to n n' ->
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

Hypothesis recv_new_eq_from :
  forall onet failed tr ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n' <> n ->
  adjacent_to n n' ->
  onet.(odnwPackets) n' n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.add n' d.(adjacent))) (onet.(odnwPackets) n n').

Hypothesis recv_new_neq_from :
  forall onet failed tr from ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  In from failed ->  
  from <> n ->
  from <> n' ->
  onet.(odnwPackets) from n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n n') ->
  P (mkData (NSet.remove from d.(adjacent))) (onet.(odnwPackets) n n').

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
      rewrite collate_ls_not_adjacent; last exact: adjacent_to_irreflexive.
      rewrite collate_msg_for_not_adjacent; last exact: adjacent_to_irreflexive.
      by rewrite (Failure_self_channel_empty s1).
    rewrite collate_ls_neq_to //.
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_msg_for_notin; last exact: not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_msg_for_notin //; last exact: in_not_in_exclude.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    case (adjacent_to_dec h n') => H_dec'.
      rewrite collate_msg_for_live_adjacent //; last exact: (ordered_dynamic_nodes_no_dup s1).
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
    rewrite collate_msg_for_not_adjacent //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ FailureRecorder_FailMsgParams _ _ _ s1).
  break_or_hyp => //.
  set f := collate _ _ _.
  have H_eq_f: f n n' = odnwPackets net n n' by rewrite /f collate_neq //; auto.
  rewrite (collate_ls_f_eq _ _ _ _ _ _ _ H_eq_f) {H_eq_f f}.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_ls_neq_to //; eauto.  
  repeat find_reverse_rewrite.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_ls_not_adjacent //; eauto.
  rewrite collate_ls_nodup_in.
  * have H_p: P d (odnwPackets net n h) by eauto.
    move: H_p.
    rewrite (Failure_inactive_no_incoming s1) //=.
    by eauto.
  * apply: nodup_adjacent_to_node.
    apply: nodup_exclude.
    by find_apply_lem_hyp ordered_dynamic_nodes_no_dup.
  * apply: adjacent_to_adjacent_to_node => //.
    exact: In_n_exclude.
Admitted.

End SingleNodeInvOut.

(*
Lemma Failure_in_after_all_fail_new : 
forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), In_all_before New Fail (net.(odnwPackets) n' n).
Proof.

Qed.
*)

End FailureRecorder.
x
