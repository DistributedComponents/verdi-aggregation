Require Import Verdi.
Require Import HandlerMonad.
Require Import StructTact.Fin.
Require Import NameOverlay.

Require Import Sumbool.

Require Import TotalMapSimulations.

Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.

Require Import UpdateLemmas.
Local Arguments update {_} {_} _ _ _ _ : simpl never.

Set Implicit Arguments.

Lemma count_occ_app_split : 
  forall (A : Type) eq_dec  l l' (a : A),
    count_occ eq_dec (l ++ l') a = count_occ eq_dec l a + count_occ eq_dec l' a.
Proof.
move => A eq_dec.
elim => //.
move => a' l IH l' a.
rewrite /=.
case (eq_dec _ _) => H_dec; first by rewrite IH.
by rewrite IH.
Qed.

(* holds when there are no a' in the list until after all a *)
Fixpoint In_all_before (A : Type) (a a' : A) l : Prop :=
match l with
| [] => True
| a0 :: l' => ~ In a l' \/ (a' <> a0 /\ In_all_before a a' l')
end.

Lemma head_before_all_not_in : 
  forall (A : Type) l (a a' : A),
  a <> a' ->
  In_all_before a a' (a' :: l) ->
  ~ In a l.
Proof.
move => A l a a' H_neq H_bef.
case: H_bef => H_bef //.
by move: H_bef => [H_neq' H_bef].
Qed.

Lemma append_neq_before_all : 
  forall (A : Type) l (a a' a0 : A),
    a0 <> a ->
    In_all_before a a' l ->
    In_all_before a a' (l ++ [a0]).
Proof.
move => A.
elim => [|a l IH] a' a0 a1 H_neq H_bef; first by left.
rewrite /=.
case: H_bef => H_bef.
  left.
  move => H_in.
  apply in_app_or in H_in.
  case: H_in => H_in //.
  by case: H_in => H_in.
move: H_bef => [H_neq' H_bef].
right.
split => //.
exact: IH.
Qed.

Lemma append_before_all_not_in : 
  forall (A : Type) l (a a' a0 : A),
    ~ In a' l ->
    In_all_before a a' (l ++ [a0]).
Proof.
move => A.
elim => [|a l IH] a0 a' a1 H_in; first by left.
have H_neq': a' <> a.
  move => H_neq.
  rewrite H_neq in H_in.
  case: H_in.
  by left.
have H_in': ~ In a' l.
  move => H_in'.
  by case: H_in; right.
rewrite /=.
right.
split => //.
exact: IH.
Qed.

Lemma not_in_all_before :
  forall (A : Type) l (a a' : A),
    ~ In a l ->
    In_all_before a a' l.
Proof.
move => A.
case => //.
move => a l a0 a' H_in.
have H_in': ~ In a0 l.
  move => H_in'.
  by case: H_in; right.
by left.
Qed.

Module FailureRecorder (N : NatValue).

Module AN := Adjacency N.
Import AN.

Module FinNSetFacts := Facts FinNSet.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.

Section Adjacent.

Context {fin_nop : NameOverlayParams Fin_n_NameParams}.

Inductive Msg := 
| Fail : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
by case; case; left.
Defined.

Inductive Input : Set := .

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Output : Set := .

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
Defined.

Record Data :=  mkData { adjacent : FinNS }.

Definition InitData (n : name) := mkData (adjacency n nodes).

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Fail => 
  put {| adjacent := FinNSet.remove src st.(adjacent) |}
end.

Definition IOHandler (me : name) (i : Input) : Handler Data := nop.

Instance FailureRecorder_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance FailureRecorder_MultiParams : MultiParams _ _ :=
  {
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    init_handlers := InitData ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Instance FailureRecorder_FailMsgParams : FailMsgParams FailureRecorder_MultiParams :=
  {
    msg_fail := Fail
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
    msg = Fail /\ out = [] /\ ms = [] /\
    st'.(adjacent) = FinNSet.remove src st.(adjacent).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg; monad_unfold.
rewrite /=.
move => H_eq.
by inversion H_eq.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases.

Lemma Failure_node_not_adjacent_self : 
forall net failed tr n, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 ~ In n failed ->
 ~ FinNSet.In n (onwState net n).(adjacent).
Proof.
move => net failed tr n H.
remember step_o_f_init as y in *.
have ->: failed = fst (failed, net) by [].
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_o_f_init /=.
  move => H_f.
  exact: not_adjacent_self.
move => H_f.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec /=; last exact: IHrefl_trans_1n_trace1.
  rewrite -H_dec in H3.
  net_handler_cases.
  apply FinNSet.remove_spec in H0.
  by move: H0 => [H0 H_neq].
- by find_apply_lem_hyp input_handlers_IOHandler.
- exact: IHrefl_trans_1n_trace1.
Qed.

Definition self_channel_empty (n : name) (onet : ordered_network) : Prop :=
onet.(onwPackets) n n = [].

Lemma Failure_self_channel_empty : 
forall onet failed tr, 
 step_o_f_star step_o_f_init (failed, onet) tr -> 
 forall n, ~ In n failed ->
   self_channel_empty n onet.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
rewrite /self_channel_empty in IHrefl_trans_1n_trace1.
rewrite /self_channel_empty.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
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
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
concludes.
move => n n' H_in.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  rewrite /= in H0, H_in.
  contradict H0.
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

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variable n : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_fail : 
  forall onet failed tr n',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) ->
    P (mkData (FinNSet.remove n' (onet.(onwState) n).(adjacent))).

Theorem P_inv_n : P (onwState onet n).
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec //.
  rewrite -H_dec {H_dec H'_step2 to} in H0 H1 H5.
  case: d H5 => /=.
  move => adjacent0 H_eq.
  rewrite H_eq {H_eq adjacent0}.
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

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_fail_neq_from :
  forall onet failed tr from ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  from <> n ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n n').

Hypothesis recv_fail_neq :
  forall onet failed tr from ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  n <> n' ->
  from <> n ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n n').

Theorem P_inv_n_out : P (onet.(onwState) n) (onet.(onwPackets) n n').
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_f_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec.
    rewrite -H_dec in H1 H5 H0.
    rewrite -H_dec /update2 /= {H_dec to H'_step2}.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq {H_eq from} in H5 H0. 
      by rewrite (Failure_self_channel_empty H'_step1) in H0.
    case: d H5 => /=.
    move => adjacent0 H_eq.
    rewrite H_eq {adjacent0 H_eq}.
    case: H_dec => H_dec.
      case (In_dec (fin_eq_dec N.n) from failed) => H_in; first exact: (recv_fail_neq_from H'_step1 H_in_f H_in H_dec H0).
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    case (fin_eq_dec N.n from n) => H_neq; first by rewrite H_neq (Failure_self_channel_empty H'_step1) in H0.
    case (In_dec (fin_eq_dec N.n) from failed) => H_in; first exact: recv_fail_neq H'_step1 _ _ H_dec _ H0 H4.
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

Lemma collate_msg_for_not_adjacent :
  forall m n h ns f,
    ~ adjacent_to h n ->
    collate h f (msg_for m (adjacent_to_node h ns)) h n = f h n.
Proof.
move => m n h ns f H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_msg_for_notin :
  forall m n h ns f failed,
    ~ In n ns ->
    collate h f (msg_for m (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m n h ns f failed.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (in_dec _ _) => H_dec.
  rewrite IH //.
  move => H_in'.
  by case: H_in; right.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH.
    rewrite /update2.
    case (sumbool_and _ _) => H_and //.
    move: H_and => [H_and H_and'].
    rewrite H_and' in H_in.
    by case: H_in; left.
  move => H_in'.
  case: H_in.
  by right.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_msg_for_live_adjacent :
  forall m n h ns f failed,
    ~ In n failed ->
    adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (msg_for m (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [m].
Proof.
move => m n h ns f failed H_in H_adj.
move: f.
elim: ns => //.
move => n' ns IH f H_in' H_nd.
inversion H_nd; subst.
rewrite /=.
case (in_dec _ _) => H_dec.
  case: H_in' => H_in'; first by rewrite H_in' in H_dec.
  by rewrite IH.
case: H_in' => H_in'.
  rewrite H_in'.
  rewrite H_in' in H1.
  rewrite /=.
  case (adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_msg_for_notin //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by move: H_sumb => [H_eq H_eq'].
by rewrite IH.
Qed.

Section SingleNodeInvIn.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_fail_neq :
  forall onet failed tr ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In n' failed ->
  n <> n' ->
  onet.(onwPackets) n' n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (FinNSet.remove n' (onet.(onwState) n).(adjacent))) ms.

Hypothesis recv_fail_other_neq :
  forall onet failed tr from ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> from ->
  n' <> from ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwPackets) n' n).

Hypothesis fail_adjacent :
  forall onet failed tr,
    step_o_f_star step_o_f_init (failed, onet) tr ->
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
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_f_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec.
    rewrite -H_dec in H1 H5 H0.
    have H_neq: n <> from.
      move => H_eq.
      rewrite -H_eq in H0.
      by rewrite (Failure_self_channel_empty H'_step1) in H0.
    rewrite -H_dec /update2 /= {H_dec to H'_step2}.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq {H_eq from} in H0 H5 H_neq.
      case: d H5 => /= adjacent0 H_eq.
      rewrite H_eq {H_eq adjacent0}.
      case (In_dec (fin_eq_dec N.n) n' failed) => H_in; first exact: (recv_fail_neq H'_step1).
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    case: H_dec => H_dec //.
    case: d H5 => /= adjacent0 H_eq.
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
  case (fin_eq_dec N.n h n') => H_dec.
    rewrite H_dec in H0 H_neq H_f.
    rewrite H_dec {H_dec h H'_step2 H_in}.
    case (adjacent_to_dec n' n) => H_dec.
      rewrite collate_msg_for_live_adjacent //.      
      * apply (fail_adjacent H'_step1) => //.
        exact: IHH'_step1.
      * exact: all_names_nodes.
      * exact: no_dup_nodes.
    rewrite collate_msg_for_not_adjacent //.
    exact: IHH'_step1.
  rewrite collate_neq //.
  exact: IHH'_step1.
Qed.

End SingleNodeInvIn.

Section DualNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

Hypothesis after_init : P (InitData n) (InitData n') [] [].

Hypothesis recv_fail_self :
  forall onet failed tr from ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    n' = n ->
    ~ In n failed ->
    onet.(onwPackets) from n = Fail :: ms ->
    n <> from ->
    P (onet.(onwState) n) (onet.(onwState) n) (onet.(onwPackets) n n) (onet.(onwPackets) n n) ->
    P (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent)))
      (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent)))
      (onet.(onwPackets) n n) (onet.(onwPackets) n n).

Hypothesis recv_fail_other :
  forall onet failed tr from ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    ~ In n' failed ->
    onet.(onwPackets) from n = Fail :: ms ->
    n <> n' ->
    from <> n ->
    from <> n' ->
    P (onet.(onwState) n) (onet.(onwState) n') (onet.(onwPackets) n n') (onet.(onwPackets) n' n) ->
    P (mkData (FinNSet.remove from (onet.(onwState) n).(adjacent))) (onet.(onwState) n')
      (onet.(onwPackets) n n') (onet.(onwPackets) n' n).

Hypothesis recv_other_fail :
  forall onet failed tr from ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    ~ In n' failed ->
    onet.(onwPackets) from n' = Fail :: ms ->
    n <> n' ->
    from <> n ->
    from <> n' ->
    P (onet.(onwState) n) (onet.(onwState) n') (onet.(onwPackets) n n') (onet.(onwPackets) n' n) ->
    P (onet.(onwState) n) (mkData (FinNSet.remove from (onet.(onwState) n').(adjacent))) 
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
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_f_init /= => H_in_f H_in_f'.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- rewrite /= in IHH'_step1.
  move {H'_step2}.
  move => H_in_f H_in_f'.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec_n.
    rewrite -H_dec_n.
    rewrite -H_dec_n {H_dec_n to} in H5 H6 H1 H0.
    case (fin_eq_dec _ _) => H_dec_n'.
      rewrite H_dec_n'.
      rewrite H_dec_n' in H_in_f' H6.
      rewrite /update2.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq in H0.
        by rewrite (Failure_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec //.
      case: d H5 => /= adjacent0 H_eq.
      rewrite H_eq {H_eq adjacent0}.
      apply (recv_fail_self H'_step1 H_dec_n' H1 H0) => //.
      move => H_neq.
      by rewrite H_neq in H_dec.
    case: d H5 => /= adjacent0 H_eq.
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
    case (fin_eq_dec _ _) => H_dec_n'.
      rewrite -H_dec_n'.
      rewrite -H_dec_n' {to H_dec_n'} in H0 H_dec_n H1 H5.
      case: d H5 => /= adjacent0 H_eq.
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
      * exact: H6.
- rewrite /= in IHH'_step1.
  move {H'_step2}.
  move => H_in_f H_in_f'.
  find_apply_lem_hyp input_handlers_IOHandler.
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
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall (n n' : name),
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st.
move => n n' H_f.
pose P_curr (d : Data) := FinNSet.In n' d.(adjacent) -> @adjacent_to _ fin_nop n' n.
rewrite -/(P_curr _).
apply: (P_inv_n H_st); rewrite /P_curr //= {P_curr net tr H_st failed H_f}.
- move => H_ins.
  apply adjacent_to_node_adjacency in H_ins.
  apply adjacent_to_node_adjacent_to in H_ins.
  move: H_ins => [H_in H_adj].
  by apply adjacent_to_symmetric in H_adj.
- move => net failed tr n0 H_st H_in_f IH H_adj.
  apply: IH.
  by apply FinNSetFacts.remove_3 in H_adj.
Qed.

Lemma Failure_in_adj_or_incoming_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
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
    rewrite /update /=.
    case (fin_eq_dec _ _) => H_dec //.
    move => H_ins.
    case: d H7 H_ins => /= adjacent0 H_eq H_adj.
    rewrite H_eq in H_adj.
    by apply FinNSetFacts.remove_1 in H_adj.
  move: H_ins.
  rewrite /update /=.
  case (fin_eq_dec _ _) => H_dec'.
    case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
    case: d H7 => /= adjacent0 H_eq.
    move => H_ins.
    rewrite H_eq {adjacent0 H_eq} in H_ins.
    rewrite -H_dec' {to H_dec'} in H2 H3 H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
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
  case (fin_eq_dec N.n h n') => H_dec.
    rewrite H_dec.
    right.
    split; first by left.
    rewrite H_dec in H2.
    have H_adj := Failure_in_adj_adjacent_to H _ H_in_f' H_ins.
    rewrite collate_msg_for_live_adjacent //.
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
  step_o_f_star step_o_f_init (failed, onet) tr -> 
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
  rewrite count_occ_app_split /= H_cnt_eq.
  by auto with arith.
Qed.

Lemma Failure_adjacent_to_in_adj :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_f H_f'.
pose P_curr (d d' : Data) (l l' : list Msg) := 
  @adjacent_to _ fin_nop n' n -> 
  FinNSet.In n' d.(adjacent).
rewrite -/(P_curr _ (onet.(onwState) n') (onet.(onwPackets) n n')
 (onet.(onwPackets) n' n)).
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_f H_f'}.
- move => H_adj.
  apply adjacent_to_node_adjacency.
  apply adjacent_to_adjacent_to_node; first exact: all_names_nodes.
  exact: adjacent_to_symmetric.
- move => onet failed tr from ms H_st H_eq H_in_f H_eq' H_neq H_adj H_adj_to.
  rewrite H_eq in H_adj_to.
  contradict H_adj_to.
  exact: adjacent_to_irreflexive.
- move => onet failed tr from ms H_st H_in_f H_in_f' H_eq H_neq H_neq_f H_neq_f' IH H_adj.
  concludes.
  by apply FinNSetFacts.remove_2.
Qed.

Lemma Failure_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_in_f.
pose P_curr (d : Data) (l : list Msg) := 
  In Fail l ->
  FinNSet.In n' d.(adjacent).
rewrite -/(P_curr _ _).
apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_in_f}.
- move => onet failed tr ms H_st H_in_f H_in_f' H_neq H_eq IH H_in.
  have H_cnt: count_occ Msg_eq_dec ms Fail > 0 by apply count_occ_In.
  have H_cnt': count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail > 1 by rewrite H_eq /=; auto with arith.
  have H_le := Failure_le_one_fail H_st _ n' H_in_f.
  by omega.
- move => onet failed tr from ms H_st H_in_f H_neq H_neq'.
  move => H_eq IH H_in.
  apply FinNSetFacts.remove_2; first by move => H_eq'; rewrite H_eq' in H_neq'.
  exact: IH.
- move => onet failed tr H_st H_neq H_in_f H_in_f' H_adj IH H_in.
  exact (Failure_adjacent_to_in_adj H_st _ _ H_in_f H_in_f' H_adj).
Qed.

Lemma Failure_first_fail_in_adj : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_in_f.
pose P_curr (d : Data) (l : list Msg) := 
  hd_error l = Some Fail ->
  FinNSet.In n' d.(adjacent).
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
  apply FinNSetFacts.remove_2 => //.
  move => H_eq'.
  by rewrite H_eq' in H_neq'.
- move => onet failed tr H_st H_neq H_in_f H_in_f' H_adj IH H_hd.
  by have H_a := Failure_adjacent_to_in_adj H_st _ _ H_in_f H_in_f' H_adj.
Qed.

Lemma Failure_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Failure_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

End Adjacent.

End FailureRecorder.
