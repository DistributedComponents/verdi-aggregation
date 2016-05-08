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
