Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.
Require Import Simul.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Sumbool.

Require Import ssreflect.
Require Import ssrbool.
Require Import eqtype.
Require Import fintype.
Require Import finset.
Require Import fingroup.

Require Import AAC.

Require Import Orders.
Require Import MSetList.
Require Import MSetFacts.
Require Import MSetProperties.

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

(* holds when there are no a' until, possibly, after the first a *)
(*
Fixpoint In_after_first (A : Type) (a a' : A) l : Prop :=
match l with
| [] => True
| a0 :: l' => a = a0 \/ (a' <> a0 /\ In_after_first a a' l')
end.
*)

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


(*
In_all_before (Aggregate m') Fail l ->
In_all_before (Aggregate m') Fail (l ++ [Fail]).

~ In Fail l ->
In_all_before (Aggregate m') Fail (l ++ (Aggregate m'))
*)

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

(* -------------------------------------- *)

Module Type NetOverlay.

Parameter n : nat.

Module N <: NatValue.
Definition n := n.
End N.

Definition num_sources := n.

Definition Name := (fin num_sources).

Definition list_sources := (all_fin num_sources).

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
exact: fin_eq_dec.
Defined.

Parameter Adjacent_to : relation Name.

Parameter Adjacent_to_symmetric : Symmetric Adjacent_to.

Parameter Adjacent_to_irreflexive : Irreflexive Adjacent_to.

Parameter Adjacent_to_dec : forall n n', { Adjacent_to n n' } + { ~ Adjacent_to n n' }.

Definition Adjacent_to_node (n : Name) := 
filter (Adjacent_to_dec n).

Lemma Adjacent_to_node_Adjacent_to : 
  forall n n' ns,
  In n' (Adjacent_to_node n ns) -> In n' ns /\ Adjacent_to n n'.
Proof.
move => n n' ns H_in.
rewrite /Adjacent_to_node in H_in.
apply filter_In in H_in.
move: H_in => [H_in H_eq].
split => //.
move: H_eq.
by case (Adjacent_to_dec _ _) => H_dec H.
Qed.

Lemma Adjacent_to_Adjacent_to_node : 
  forall n n' ns,
  In n' ns -> 
  Adjacent_to n n' ->
  In n' (Adjacent_to_node n ns).
Proof.
move => n n' ns H_in H_adj.
apply filter_In.
split => //.
by case (Adjacent_to_dec _ _) => H_dec.
Qed.

Definition Nodes := list_sources.

Theorem In_n_Nodes : forall n : Name, In n Nodes.
Proof. exact: all_fin_all. Qed.

Theorem nodup : NoDup Nodes.
Proof. exact: all_fin_NoDup. Qed.

Module fin_n_OT := fin_OT N.

Module FinNSet <: MSetInterface.S := MSetList.Make fin_n_OT.

Definition FinNS := FinNSet.t.

Definition adjacency (n : Name) (ns : list Name) : FinNS :=
fold_right (fun n' fs => FinNSet.add n' fs) FinNSet.empty (Adjacent_to_node n ns).

Lemma Adjacent_to_node_adjacency : forall n n' ns, In n' (Adjacent_to_node n ns) <-> FinNSet.In n' (adjacency n ns).
Proof.
move => n n' ns.
split.
  elim: ns => //=.
  move => n0 ns IH.
  rewrite /adjacency /= /is_left.
  case (Adjacent_to_dec _ _) => H_dec /= H_in; last exact: IH.
  case: H_in => H_in.
    rewrite H_in.
    apply FinNSet.add_spec.
    by left.
  apply FinNSet.add_spec.
  right.
  exact: IH.
elim: ns => //=; first by rewrite /adjacency /=; exact: FinNSet.empty_spec.
move => n0 ns IH.
rewrite /adjacency /=.
rewrite /is_left.
case (Adjacent_to_dec _ _) => H_dec /= H_ins; last exact: IH.
apply FinNSet.add_spec in H_ins.
case: H_ins => H_ins; first by left.
right.
exact: IH.
Qed.

Lemma not_adjacent_self : forall n ns, ~ FinNSet.In n (adjacency n ns).
Proof.
move => n ns H_ins.
apply Adjacent_to_node_adjacency in H_ins.
apply Adjacent_to_node_Adjacent_to in H_ins.
move: H_ins => [H_in H_adj].
contradict H_adj.
exact: Adjacent_to_irreflexive.
Qed.

Lemma adjacency_mutual_in : 
  forall n n' ns,
  In n' ns ->
  FinNSet.In n (adjacency n' ns) -> 
  FinNSet.In n' (adjacency n ns).
Proof.
move => n n' ns H_in H_ins.
apply Adjacent_to_node_adjacency.
apply Adjacent_to_node_adjacency in H_ins.
apply Adjacent_to_node_Adjacent_to in H_ins.
move: H_ins => [H_in' H_adj].
apply Adjacent_to_symmetric in H_adj.
exact: Adjacent_to_Adjacent_to_node.
Qed.

Lemma adjacency_mutual : forall (n n' : Name), FinNSet.In n (adjacency n' Nodes) -> FinNSet.In n' (adjacency n Nodes).
Proof.
move => n n' H_ins.
have H_in: In n' Nodes by exact: In_n_Nodes.
exact: adjacency_mutual_in.
Qed.

End NetOverlay.

(* -------------------------------------- *)

Module Failure (NO : NetOverlay).

Import NO.

Module FinNSetFacts := Facts FinNSet.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.

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

Definition init_Data (n : Name) := mkData (adjacency n Nodes).

Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Fail => 
  let new_adjacent := FinNSet.remove src st.(adjacent) in
  put (mkData new_adjacent)
end.

Definition IOHandler (me : Name) (i : Input) : Handler Data := nop.

Instance Failure_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Failure_MultiParams : MultiParams Failure_BaseParams :=
  {
    name := Name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := Name_eq_dec ;
    nodes := Nodes ;
    all_names_nodes := In_n_Nodes ;
    no_dup_nodes := nodup ;
    init_handlers := init_Data ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Instance Failure_OverlayParams : OverlayParams Failure_MultiParams :=
  {
    adjacent_to := Adjacent_to ;
    adjacent_to_dec := Adjacent_to_dec ;
    adjacent_to_irreflexive := Adjacent_to_irreflexive ;
    adjacent_to_symmetric := Adjacent_to_symmetric
  }.

Instance Failure_FailMsgParams : FailMsgParams Failure_MultiParams :=
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
  case (Name_eq_dec _ _) => H_dec /=; last exact: IHrefl_trans_1n_trace1.
  rewrite -H_dec in H3.
  net_handler_cases.
  apply FinNSet.remove_spec in H0.
  by move: H0 => [H0 H_neq].
- by find_apply_lem_hyp input_handlers_IOHandler.
- exact: IHrefl_trans_1n_trace1.
Qed.

Definition self_channel_empty (n : Name) (onet : ordered_network) : Prop :=
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

Variable n : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (init_Data n).

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
  case (Name_eq_dec _ _) => H_dec //.
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

Variables n n' : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

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
  case (Name_eq_dec _ _) => H_dec.
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
      case (In_dec Name_eq_dec from failed) => H_in; first exact: (recv_fail_neq_from H'_step1 H_in_f H_in H_dec H0).
      have H_inl := Failure_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    case (Name_eq_dec from n) => H_neq; first by rewrite H_neq (Failure_self_channel_empty H'_step1) in H0.
    case (In_dec Name_eq_dec from failed) => H_in; first exact: recv_fail_neq H'_step1 _ _ H_dec _ H0 H4.
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

Lemma collate_fail_for_not_adjacent :
  forall n h ns f failed,
    ~ Adjacent_to h n ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => n h ns f failed H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (in_dec _ _) => H_dec //.
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_fail_for_notin :
  forall n h ns f failed,
    ~ In n ns ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => n h ns f failed.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (in_dec _ _) => H_dec.
  rewrite IH //.
  move => H_in'.
  by case: H_in; right.
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec'.
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

Lemma collate_fail_for_live_adjacent :
  forall n h ns f failed,
    ~ In n failed ->
    Adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [Fail].
Proof.
move => n h ns f failed H_in H_adj.
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
  case (Adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_fail_for_notin //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec'.
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

Variables n n' : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

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
    Adjacent_to n' n ->
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
  case (Name_eq_dec _ _) => H_dec.
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
      case (In_dec Name_eq_dec n' failed) => H_in; first exact: (recv_fail_neq H'_step1).
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
  case (Name_eq_dec h n') => H_dec.
    rewrite H_dec in H0 H_neq H_f.
    rewrite H_dec {H_dec h H'_step2 H_in}.
    case (Adjacent_to_dec n' n) => H_dec.
      rewrite collate_fail_for_live_adjacent //.      
      * apply (fail_adjacent H'_step1) => //.
        exact: IHH'_step1.
      * exact: In_n_Nodes.
      * exact: nodup.
    rewrite collate_fail_for_not_adjacent //.
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

Variables n n' : Name.

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) (init_Data n') [] [].

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
  case (Name_eq_dec _ _) => H_dec_n.
    rewrite -H_dec_n.
    rewrite -H_dec_n {H_dec_n to} in H5 H6 H1 H0.
    case (Name_eq_dec _ _) => H_dec_n'.
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
    case (Name_eq_dec _ _) => H_dec_n'.
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
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    Adjacent_to n' n.
Proof.
move => net failed tr H_st.
move => n n' H_f.
pose P_curr (d : Data) := FinNSet.In n' d.(adjacent) -> Adjacent_to n' n.
rewrite -/(P_curr _).
apply: (P_inv_n H_st); rewrite /P_curr //= {P_curr net tr H_st failed H_f}.
- move => H_ins.
  apply Adjacent_to_node_adjacency in H_ins.
  apply Adjacent_to_node_Adjacent_to in H_ins.
  move: H_ins => [H_in H_adj].
  by apply Adjacent_to_symmetric in H_adj.
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
    case (Name_eq_dec _ _) => H_dec //.
    move => H_ins.
    case: d H7 H_ins => /= adjacent0 H_eq H_adj.
    rewrite H_eq in H_adj.
    by apply FinNSetFacts.remove_1 in H_adj.
  move: H_ins.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec'.
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
  case (Name_eq_dec h n') => H_dec.
    rewrite H_dec.
    right.
    split; first by left.
    rewrite H_dec in H2.
    have H_adj := Failure_in_adj_adjacent_to H _ H_in_f' H_ins.
    rewrite collate_fail_for_live_adjacent //.
    * apply in_or_app.
      by right; left.
    * exact: In_n_Nodes.
    * exact: nodup.
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
    Adjacent_to n' n ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st.
move => n n' H_f H_f'.
pose P_curr (d d' : Data) (l l' : list Msg) := 
  Adjacent_to n' n -> 
  FinNSet.In n' d.(adjacent).
rewrite -/(P_curr _ (onet.(onwState) n') (onet.(onwPackets) n n')
 (onet.(onwPackets) n' n)).
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr onet tr H_st failed H_f H_f'}.
- move => H_adj.
  apply Adjacent_to_node_adjacency.
  apply Adjacent_to_Adjacent_to_node; first exact: In_n_Nodes.
  exact: Adjacent_to_symmetric.
- move => onet failed tr from ms H_st H_eq H_in_f H_eq' H_neq H_adj H_adj_to.
  rewrite H_eq in H_adj_to.
  contradict H_adj_to.
  exact: Adjacent_to_irreflexive.
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
  exact (Failure_adjacent_to_in_adj H_st H_in_f H_in_f' H_adj).
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
  by have H_a := Failure_adjacent_to_in_adj H_st H_in_f H_in_f' H_adj.
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

End Failure.

(* -------------------------------------- *)

Module Type CommutativeMassGroup.
Parameter gT : finGroupType.
Parameter commutes : forall x y : gT, commute x y.
End CommutativeMassGroup.

Module Aggregation (NO : NetOverlay) (CMG : CommutativeMassGroup) <:
       CommutativeMassGroup
       with Definition gT := CMG.gT
       with Definition commutes := CMG.commutes.

Module FNO := Failure NO.

Definition gT := CMG.gT.
Definition commutes := CMG.commutes.

Import GroupScope.

Import NO.

Instance aac_mulg_Assoc : Associative eq (mulg (T:=gT)) := mulgA (T:=gT).

Instance aac_mulg_Comm : Commutative eq (mulg (T:=gT)).
move => x y.
rewrite commute_sym //.
exact: commutes.
Defined.

Instance aac_mulg_unit : Unit eq (mulg (T:=gT)) 1.
apply: (Build_Unit eq (mulg (T:=gT)) 1 _ _) => x; first by rewrite mul1g.
by rewrite mulg1.
Defined.

Require Import OrderedTypeEx.
Require Import FMapList.
Module fin_n_compat_OT := fin_OT_compat N.
Module FinNMap <: FMapInterface.S := FMapList.Make fin_n_compat_OT.

Module FinNSetFacts := Facts FinNSet.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.

Require Import FMapFacts.
Module FinNMapFacts := Facts FinNMap.

Definition m := gT.

Definition FinNM := FinNMap.t m.

Definition m_eq_dec : forall (a b : m), { a = b }+{ a <> b }.
move => a b.
case H_dec: (a == b); move: H_dec; first by case/eqP; left.
move => H_eq; right.
case/eqP => H_neq.
by rewrite H_eq in H_neq.
Defined.

Inductive Msg := 
| Aggregate : m -> Msg
| Fail : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Input :=
| Local : m -> Input
| SendAggregate : Name -> Input
| AggregateRequest : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: Name_eq_dec.
Defined.

Inductive Output :=
| AggregateResponse : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data :=  mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : FinNS ; 
  sent : FinNM ; 
  received : FinNM 
}.

Definition fins_lt (fins fins' : FinNS) : Prop :=
FinNSet.cardinal fins < FinNSet.cardinal fins'.

Lemma fins_lt_well_founded : well_founded fins_lt.
Proof.
apply (well_founded_lt_compat _ (fun fins => FinNSet.cardinal fins)).
by move => x y; rewrite /fins_lt => H.
Qed.

Definition init_map_t (fins : FinNS) : Type := 
{ map : FinNM | forall (n : Name), FinNSet.In n fins <-> FinNMap.find n map = Some 1 }.

Definition init_map_F : forall fins : FinNS, 
  (forall fins' : FinNS, fins_lt fins' fins -> init_map_t fins') ->
  init_map_t fins.
rewrite /init_map_t.
refine
  (fun (fins : FinNS) init_map_rec =>
   match FinNSet.choose fins as finsopt return (_ = finsopt -> _) with
   | None => fun (H_eq : _) => exist _ (FinNMap.empty m) _
   | Some n => fun (H_eq : _) => 
     match init_map_rec (FinNSet.remove n fins) _ with 
     | exist fins' H_fins' => exist _ (FinNMap.add n 1 fins') _
     end
   end (refl_equal _)).
- rewrite /fins_lt /=.
  apply FinNSet.choose_spec1 in H_eq.
  set fn := FinNSet.remove _ _.
  have H_notin: ~ FinNSet.In n fn by move => H_in; apply FinNSetFacts.remove_1 in H_in.
  have H_add: FinNSetProps.Add n fn fins.
    rewrite /FinNSetProps.Add.
    move => k.
    split => H_in.
      case (Name_eq_dec n k) => H_eq'; first by left.
      by right; apply FinNSetFacts.remove_2.
    case: H_in => H_in; first by rewrite -H_in.
    by apply FinNSetFacts.remove_3 in H_in.
  have H_card := FinNSetProps.cardinal_2 H_notin H_add.
  rewrite H_card {H_notin H_add H_card}.
  by auto with arith.
- move => n'.
  apply FinNSet.choose_spec1 in H_eq.
  case (Name_eq_dec n n') => H_eq_n.
    rewrite -H_eq_n.
    split => //.
    move => H_ins.
    apply FinNMapFacts.find_mapsto_iff.
    exact: FinNMap.add_1.
  split => H_fins.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.add_neq_mapsto_iff => //.
    apply FinNMapFacts.find_mapsto_iff.    
    apply H_fins'.
    exact: FinNSetFacts.remove_2.
  apply FinNMapFacts.find_mapsto_iff in H_fins.
  apply FinNMapFacts.add_neq_mapsto_iff in H_fins => //.
  apply FinNMapFacts.find_mapsto_iff in H_fins.
  apply H_fins' in H_fins.
  by apply FinNSetFacts.remove_3 in H_fins.    
- move => n.
  apply FinNSet.choose_spec2 in H_eq.
  split => H_fin; first by contradict H_fin; auto with set.
  apply FinNMap.find_2 in H_fin.
  contradict H_fin.
  exact: FinNMap.empty_1.
Defined.

Definition init_map_str : forall (fins : FinNS), init_map_t fins :=
  @well_founded_induction_type
  FinNSet.t
  fins_lt
  fins_lt_well_founded
  init_map_t
  init_map_F.

Definition init_map (fins : FinNS) : FinNM := 
match init_map_str fins with
| exist map _ => map
end.
    
Definition init_Data (n : Name) := mkData 1 1 (adjacency n Nodes) (init_map (adjacency n Nodes)) (init_map (adjacency n Nodes)).

Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match FinNMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    let new_aggregate := st.(aggregate) * m_msg in
    let new_received := FinNMap.add src (m_src * m_msg) st.(received) in
    put (mkData st.(local) new_aggregate st.(adjacent) st.(sent) new_received)
  end
| Fail => 
  let new_adjacent := FinNSet.remove src st.(adjacent) in  
  match FinNMap.find src st.(sent), FinNMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>    
    let new_aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 in    
    let new_sent := FinNMap.remove src st.(sent) in
    let new_received := FinNMap.remove src st.(received) in
    put (mkData st.(local) new_aggregate new_adjacent new_sent new_received)
  | _, _ => 
    put (mkData st.(local) st.(aggregate) new_adjacent st.(sent) st.(received))
  end
end.

Definition IOHandler (me : Name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  let new_local := m_msg in
  let new_aggregate := st.(aggregate) * m_msg * st.(local)^-1 in
  put (mkData new_local new_aggregate st.(adjacent) st.(sent) st.(received))
| SendAggregate dst => 
  when (FinNSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match FinNMap.find dst st.(sent) with
   | None => nop
   | Some m_dst =>        
     let new_aggregate := 1 in
     let new_sent := FinNMap.add dst (m_dst * st.(aggregate)) st.(sent) in
     put (mkData st.(local) new_aggregate st.(adjacent) new_sent st.(received)) >> (send (dst, (Aggregate st.(aggregate))))
   end)
| Query =>
  write_output (AggregateResponse st.(aggregate))
end.

Instance Aggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Aggregation_MultiParams : MultiParams Aggregation_BaseParams :=
  {
    name := Name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := Name_eq_dec ;
    nodes := Nodes ;
    all_names_nodes := In_n_Nodes ;
    no_dup_nodes := nodup ;
    init_handlers := init_Data ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Instance Aggregation_OverlayParams : OverlayParams Aggregation_MultiParams :=
  {
    adjacent_to := Adjacent_to ;
    adjacent_to_dec := Adjacent_to_dec ;
    adjacent_to_irreflexive := Adjacent_to_irreflexive ;
    adjacent_to_symmetric := Adjacent_to_symmetric
  }.

Instance Aggregation_FailMsgParams : FailMsgParams Aggregation_MultiParams :=
  {
    msg_fail := Fail
  }.

Definition sum_fold (fm : FinNM) (n : Name) (partial : m) : m :=
match FinNMap.find n fm with
| Some m' => partial * m'
| None => partial
end.

Definition sumM (fs : FinNS) (fm : FinNM) : m := 
FinNSet.fold (sum_fold fm) fs 1.

Lemma fold_left_right : forall (fm : FinNM) (l : list Name),
  fold_left (fun partial n => (sum_fold fm) n partial) l 1 = fold_right (sum_fold fm) 1 l.
Proof.
move => fm; elim => [|a l IH] //.
rewrite /= -IH /sum_fold {IH}.
case (FinNMap.find _ _) => [m6|] // {a}; gsimpl.
move: m6; elim: l => [m6|a l IH m6] => /=; first by gsimpl.
case (FinNMap.find _ _) => [m7|] //.
rewrite commutes IH; gsimpl.
by rewrite -IH.
Qed.

Corollary sumM_fold_right : forall (fs : FinNS) (fm : FinNM), 
  FinNSet.fold (sum_fold fm) fs 1 = fold_right (sum_fold fm) 1 (FinNSet.elements fs).
Proof. by move => fs fm; rewrite FinNSet.fold_spec fold_left_right. Qed.

Lemma not_in_add_eq : forall (l : list Name) (n : name) (fm : FinNM) (m5 : m),
  ~ InA eq n l -> 
  fold_right (sum_fold (FinNMap.add n m5 fm)) 1 l = fold_right (sum_fold fm) 1 l.
move => l n fm m5; elim: l => //.
move => a l IH H_in.
have H_in': ~ InA eq n l by move => H_neg; apply: H_in; apply InA_cons; right.
apply IH in H_in'.
rewrite /= H_in' /= /sum_fold.
have H_neq: n <> a by move => H_eq; apply: H_in; apply InA_cons; left.
case H_find: (FinNMap.find _ _) => [m6|].
  apply FinNMapFacts.find_mapsto_iff in H_find.  
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  case H_find': (FinNMap.find _ _) => [m7|]; last by rewrite H_find' in H_find.
  rewrite H_find in H_find'.
  injection H_find' => H_eq.
  by rewrite H_eq.
case H_find': (FinNMap.find _ _) => [m6|] => //.
apply FinNMapFacts.find_mapsto_iff in H_find'.
apply (FinNMapFacts.add_neq_mapsto_iff _ m5 _ H_neq) in H_find'.
apply FinNMapFacts.find_mapsto_iff in H_find'.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_add_map : forall (n : Name) (fs : FinNS) (fm : FinNM) (m5 m' : m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM fs (FinNMap.add n (m5 * m') fm) = sumM fs fm * m'.
Proof.
move => n fs fm m5 m' H_in H_find.
have H_in_el: InA eq n (FinNSet.elements fs) by apply FinNSetFacts.elements_2.
have H_nodup := FinNSet.elements_spec2w fs.
move: H_in_el H_nodup {H_in}.
rewrite 2!/sumM 2!sumM_fold_right.
elim (FinNSet.elements fs) => [|a l IH] H_in H_nodup; first by apply InA_nil in H_in.
case (Name_eq_dec n a) => H_dec.
  rewrite H_dec in H_find.
  rewrite H_dec /sum_fold /=.
  have H_find_eq := @FinNMapFacts.add_eq_o m fm a a (m5 * m') (refl_equal a).
  case H_find': (FinNMap.find _ _) => [m6|]; last by rewrite H_find_eq in H_find'.
  rewrite H_find_eq in H_find'.
  injection H_find' => H_eq.
  rewrite -H_eq.
  case H_find'': (FinNMap.find _ _) => [m7|]; last by rewrite H_find in H_find''.
  rewrite H_find'' in H_find.
  injection H_find => H_eq'.
  rewrite H_eq'; gsimpl.
  inversion H_nodup; subst.
  by rewrite not_in_add_eq.
apply InA_cons in H_in.
case: H_in => H_in //.
have H_nodup': NoDupA eq l by inversion H_nodup.
rewrite /= (IH H_in H_nodup') /sum_fold.
case H_find': (FinNMap.find _ _) => [m6|].
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  case H_find'': (FinNMap.find _ _) => [m7|]; last by rewrite H_find'' in H_find'.
  rewrite H_find' in H_find''.
  injection H_find'' => H_eq.
  rewrite H_eq.
  by aac_reflexivity.
case H_find'': (FinNMap.find _ _) => [m7|] //.
apply FinNMapFacts.find_mapsto_iff in H_find''.
apply (FinNMapFacts.add_neq_mapsto_iff _ (m5 * m') _ H_dec) in H_find''.
apply FinNMapFacts.find_mapsto_iff in H_find''.
by rewrite H_find' in H_find''.
Qed.

Lemma eqlistA_eq : forall (l l' : list Name), eqlistA eq l l' -> l = l'.
Proof.
elim; first by move => l' H_eql; inversion H_eql.
move => a l IH.
case => [|a' l'] H; first by inversion H.
inversion H; subst.
by rewrite (IH l').
Qed.

Lemma sumM_remove : forall (fs : FinNS) (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) fm = sumM fs fm * m5^-1.
Proof.
move => I_ind.
pose P_ind (fs : FinNS) := forall (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) fm = sumM fs fm * m5^-1.
rewrite -/(P_ind I_ind).
apply (FinNSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty n fm m5 H_in.
  have H_empty' := FinNSet.empty_spec.
  by contradict H_in; apply H_empty.
rewrite /sumM.
move => fs I' IH a H_below H_add n fm m5 H_in H_map.
have H_eql := FinNSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite 2!sumM_fold_right.
case (Name_eq_dec a n) => H_eq.
  move: H_in H_map; rewrite -H_eq H_eql {H_eq} => H_in H_map.
  rewrite /FinNSetOrdProps.P.Add in H_add.
  have H_rem := FinNSet.remove_spec I' a.
  have H_below': FinNSetOrdProps.Below a (FinNSet.remove a I').
    rewrite /FinNSetOrdProps.Below => a' H_in'.
    apply FinNSet.remove_spec in H_in'.
    case: H_in' => H_in' H_neq.
    apply H_below.
    apply H_add in H_in'.
    by case: H_in' => H_in'; first by case H_neq.
  have H_add' := FinNSetProps.Add_remove H_in.
  have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
  apply eqlistA_eq in H_eql'.
  rewrite H_eql {H_eql} in H_eql'.
  set el_rm := FinNSet.elements _.
  have {H_eql'} ->: el_rm = FinNSet.elements fs by injection H_eql'.
  rewrite {2}/fold_right {2}/sum_fold {el_rm}.
  case H_find: (FinNMap.find _ _) => [m6|]; last by rewrite H_map in H_find.
  rewrite H_map in H_find.
  have ->: m6 = m5 by injection H_find.
  by gsimpl.
rewrite H_eql.
have H_in': FinNSet.In n fs.
  apply H_add in H_in.
  by case: H_in.
have H_below': FinNSetOrdProps.Below a (FinNSet.remove n fs).
  rewrite /FinNSetOrdProps.Below => a' H_inr.
  apply H_below.
  have H_rm := FinNSet.remove_spec fs n a'.
  apply H_rm in H_inr.
  by case: H_inr.
have H_add': FinNSetOrdProps.P.Add a (FinNSet.remove n fs) (FinNSet.remove n I').
  rewrite /FinNSetOrdProps.P.Add => a'.
  have H_add_a' := H_add a'.
  case (Name_eq_dec a a') => H_eq'.
    split => H_imp; first by left.
    have H_or: a = a' \/ FinNSet.In a' fs by left.
    apply H_add_a' in H_or.
    apply FinNSet.remove_spec; split => //.
    by rewrite -H_eq'.
  split => H_imp.    
    right.
    apply FinNSet.remove_spec in H_imp.
    case: H_imp => H_imp H_neq.
    apply FinNSet.remove_spec; split => //.
    apply H_add_a' in H_imp.
    by case: H_imp.
  case: H_imp => H_imp //.
  apply FinNSet.remove_spec in H_imp.
  case: H_imp => H_imp H_neq.
  have H_or: a = a' \/ FinNSet.In a' fs by right.
  apply H_add_a' in H_or.
  by apply FinNSet.remove_spec; split.
have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /fold_right /sum_fold.      
case H_find: (FinNMap.find a fm) => [m6|].
  have H_eq' := IH n fm m5 H_in' H_map.
  rewrite 2!sumM_fold_right /fold_right in H_eq'.
  rewrite H_eq' /sum_fold.
  by aac_reflexivity.
have H_eq' := IH n fm m5 H_in' H_map.
rewrite 2!sumM_fold_right in H_eq'.
rewrite /fold_right in H_eq'.
by rewrite H_eq' /sum_fold.
Qed.

Lemma sumM_notins_remove_map : forall (fs : FinNS) (n : Name) (fm : FinNM),
  ~ FinNSet.In n fs ->
  sumM fs (FinNMap.remove n fm) = sumM fs fm.
Proof.
move => fs n fm H_ins.
have H_notin: ~ InA eq n (FinNSet.elements fs).
  move => H_ina.
  by apply FinNSetFacts.elements_2 in H_ina.
rewrite 2!/sumM 2!sumM_fold_right.
move: H_notin.
elim (FinNSet.elements fs) => [|a l IH] H_in //.
have H_in': ~ InA eq n l.
  move => H_in'.
  contradict H_in.
  by right.
have H_neq: n <> a.
  move => H_eq.
  contradict H_in.
  by left.
have IH' := IH H_in'.
move: IH'.
rewrite /fold_right /sum_fold => IH'.
case H_find: (FinNMap.find _ _) => [m5|].
  case H_find': (FinNMap.find _ _) => [m6|]; rewrite FinNMapFacts.remove_neq_o in H_find => //.
    rewrite H_find in H_find'.
    injection H_find' => H_eq.
    rewrite H_eq.
    by rewrite IH'.
  by rewrite H_find in H_find'.
rewrite FinNMapFacts.remove_neq_o in H_find => //.
case H_find': (FinNMap.find _ _) => [m5|] //.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_remove_remove : forall (fs : FinNS) (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) (FinNMap.remove n fm) = sumM fs fm * m5^-1.
Proof.
move => fs n fm m5 H_ins H_find.
have H_ins': ~ FinNSet.In n (FinNSet.remove n fs) by move => H_ins'; apply FinNSetFacts.remove_1 in H_ins'.
rewrite sumM_notins_remove_map => //.
exact: sumM_remove.
Qed.

Lemma sumM_empty : forall (fs : FinNS) (fm : FinNM), FinNSet.Empty fs -> sumM fs fm = 1.
Proof.
move => fs fm.
rewrite /FinNSet.Empty => H_empty.
have H_elts: forall (n : Name), ~ InA eq n (FinNSet.elements fs).
  move => n H_notin.
  apply FinNSetFacts.elements_2 in H_notin.
  by apply (H_empty n).
rewrite /sumM sumM_fold_right.
case H_elt: (FinNSet.elements fs) => [|a l] //.
have H_in: InA eq a (FinNSet.elements fs) by rewrite H_elt; apply InA_cons; left.
by contradict H_in; apply (H_elts a).
Qed.

Lemma sumM_eq : forall (fs : FinNS) (fm' : FinNS) (fm : FinNM),
   FinNSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
Proof.
move => I_ind.
pose P_ind (fs : FinNS) := forall (fm' : FinNS) (fm : FinNM),
   FinNSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
rewrite -/(P_ind I_ind).
apply (FinNSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty fm' fm H_eq.
  have H_empty': FinNSet.Empty fm'.
    rewrite /FinNSet.Empty => a H_in.
    apply H_eq in H_in.
    by apply H_empty in H_in.    
  rewrite sumM_empty //.
  by rewrite sumM_empty.
move => fs fm' IH a H_below H_add fm'' fm H_eq.
have H_eql := FinNSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite /sumM 2!sumM_fold_right H_eql.
have H_below': FinNSetOrdProps.Below a (FinNSet.remove a fm'').
  rewrite /FinNSetOrdProps.Below => a' H_in.
  apply H_below.
  apply (FinNSet.remove_spec) in H_in.
  case: H_in => H_in H_neq.    
  apply H_eq in H_in.
  apply H_add in H_in.
  by case: H_in => H_in; first by case H_neq.
have H_add': FinNSetOrdProps.P.Add a (FinNSet.remove a fm'') fm''.
  rewrite /FinNSetOrdProps.P.Add => a'.
  case (Name_eq_dec a a') => H_eq_a.
    split => H_imp; first by left.
    apply H_eq.
    rewrite -H_eq_a.
    by apply H_add; left.
  split => H_imp; first by right; apply FinNSet.remove_spec; split; last by contradict H_eq_a.
  case: H_imp => H_imp; first by case H_eq_a.
  by apply FinNSet.remove_spec in H_imp; case: H_imp.
have H_eq': FinNSet.Equal fs (FinNSet.remove a fm'').
   rewrite /FinNSet.Equal => a'.
   case (Name_eq_dec a a') => H_eq_a.
     have H_or: a = a' \/ FinNSet.In a' fs by left.
     apply H_add in H_or.
     split => H_imp.
       apply FinNSet.remove_spec.
       rewrite -H_eq_a in H_or H_imp.
       apply H_below in H_imp.
       by contradict H_imp.
     rewrite H_eq_a in H_imp.
     apply FinNSet.remove_spec in H_imp.
     by case: H_imp.
   split => H_imp.
     apply FinNSet.remove_spec; split; last by contradict H_eq_a.
     apply H_eq.
     by apply H_add; right.
   apply FinNSet.remove_spec in H_imp.
   case: H_imp => H_imp H_neq.
   apply H_eq in H_imp.
   apply H_add in H_imp.
   by case: H_imp.
have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /sum_fold /fold_right.
have IH' := IH (FinNSet.remove a fm'') fm.
rewrite /sumM 2!sumM_fold_right /fold_right in IH'.
by case H_find: (FinNMap.find _ _) => [m5|]; rewrite IH'.
Qed.

Corollary sumM_add : forall (fs : FinNS) (fm : FinNM) (m5 : m) (n : Name),
  ~ FinNSet.In n fs -> 
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.add n fs) fm = sumM fs fm * m5.
Proof.
move => fs fm m5 n H_notin H_map.
have H_in: FinNSet.In n (FinNSet.add n fs) by apply FinNSet.add_spec; left.
have H_rm := @sumM_remove (FinNSet.add n fs) _ _ _ H_in H_map.
set srm := sumM _ _ in H_rm.
set sadd := sumM _ _ in H_rm *.
have <-: srm * m5 = sadd by rewrite H_rm; gsimpl.
suff H_eq: srm = sumM fs fm by rewrite H_eq; aac_reflexivity.
apply sumM_eq.
exact: (FinNSetProps.remove_add H_notin).
Qed.

Lemma sumM_add_add : forall (fs : FinNS) (M5 : FinNM) (m5 : m) (n : Name),
  ~ FinNSet.In n fs -> 
  sumM (FinNSet.add n fs) (FinNMap.add n m5 M5) = sumM fs M5 * m5.
Proof.
move => fs M5 m5 n H_in.
have H_find := @FinNMapFacts.add_eq_o _ M5 _ _ m5 (refl_equal n).
rewrite (@sumM_add _ _ _ _ H_in H_find) {H_find}.
set sadd := sumM _ _.
suff H_suff: sadd = sumM fs M5 by rewrite H_suff.
rewrite /sadd /sumM 2!sumM_fold_right {sadd}.
have H_in_el: ~ InA eq n (FinNSet.elements fs) by move => H_neg; apply FinNSetFacts.elements_2 in H_neg.
by move: H_in_el; apply not_in_add_eq.
Qed.

Lemma sumM_init_map_1 : forall fm, sumM fm (init_map fm) = 1.
Proof.
move => fm.
rewrite /sumM sumM_fold_right.
rewrite /init_map /=.
case (init_map_str _).
move => fm' H_init.
have H_el := FinNSet.elements_spec1 fm.
have H_in: forall n, In n (FinNSet.elements fm) -> FinNMap.find n fm' = Some 1.
  move => n H_in.
  apply H_init.
  have [H_el' H_el''] := H_el n.
  apply: H_el'.
  apply InA_alt.
  by exists n; split.
move {H_init H_el}.
elim: (FinNSet.elements fm) H_in => //.
move => n l IH H_in.
rewrite /= {1}/sum_fold.
have H_in': In n (n :: l) by left.
have H_find' := H_in n H_in'.
rewrite IH.
  case H_find: (FinNMap.find _ _) => [n'|] //.
  rewrite H_find in H_find'.
  injection H_find' => H_eq'.
  rewrite H_eq'.
  by gsimpl.
move => n' H_in''.
apply H_in.
by right.
Qed.

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
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = []) \/
      (exists dst m', i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = FinNMap.add dst (m' * st.(aggregate)) st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = None /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) = 1 /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ ~ FinNSet.In dst st.(adjacent) /\ 
         st' = st /\ 
         out = [] /\ ms = []) \/
      (i = AggregateRequest /\ st' = st /\ out = [AggregateResponse (aggregate st)] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler.
case: i => [m_msg|dst|]; monad_unfold.
- rewrite /= => H_eq.
  injection H_eq => H_ms H_st H_out H_tt.
  rewrite -H_st /=.
  by left; exists m_msg.
- case H_mem: (FinNSet.mem _ _); case (m_eq_dec _ _) => H_dec; rewrite /sumbool_not //=.
  * apply FinNSetFacts.mem_2 in H_mem.
    move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left; exists dst.
  * apply FinNSetFacts.mem_2 in H_mem.
    case H_find: (FinNMap.find _ _) => [m'|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    + by right; left; exists dst; exists m'.
    + by right; right; left; exists dst.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply FinNSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply FinNSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
- move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
  by right; right; right; right; right.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ FinNMap.find src st.(received) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\     
     st'.(received) = FinNMap.add src (m_src * m_msg) st.(received) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ FinNMap.find src st.(received) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_snt m_rcd, msg = Fail /\ FinNMap.find src st.(sent) = Some m_snt /\ FinNMap.find src st.(received) = Some m_rcd /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = FinNMap.remove src st.(sent) /\
     st'.(received) = FinNMap.remove src st.(received) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (FinNMap.find src st.(sent) = None \/ FinNMap.find src st.(received) = None) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg|]; monad_unfold.
  case H_find: (FinNMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=; first by left; exists m_msg; exists  m_src.
  by right; left; exists m_msg.
case H_find: (FinNMap.find _ _) => [m_snt|]; case H_find': (FinNMap.find _ _) => [m_rcd|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
- right; right; left.
  by exists m_snt; exists m_rcd.
- right; right; right.
  split => //.
  split => //.
  by right.
- right; right; right.
  split => //.
  split => //.
  by left.
- right; right; right.
  split => //.
  split => //.
  by left.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Instance Aggregation_Failure_base_params_pt_map : BaseParamsPtMap Aggregation_BaseParams FNO.Failure_BaseParams :=
  {
    pt_map_data := fun d => FNO.mkData d.(adjacent) ;
    pt_map_input := fun _ => None ;
    pt_map_output := fun _ => None
  }.

Instance Aggregation_Failure_multi_params_pt_map : MultiParamsPtMap Aggregation_Failure_base_params_pt_map Aggregation_MultiParams FNO.Failure_MultiParams :=
  {
    pt_map_msg := fun m => match m with Fail => Some FNO.Fail | _ => None end ;
    pt_map_name := id ;
    pt_map_name_inv := id
  }.

Lemma pt_map_name_inv_inverse : forall n, pt_map_name_inv (pt_map_name n) = n.
Proof. by []. Qed.

Lemma pt_map_name_inverse_inv : forall n, pt_map_name (pt_map_name_inv n) = n.
Proof. by []. Qed.

Lemma pt_init_handlers_eq : forall n,
  pt_map_data (init_handlers n) = init_handlers (pt_map_name n).
Proof. by []. Qed.

Lemma pt_net_handlers_some : forall me src m st m',
  pt_map_msg m = Some m' ->
  pt_mapped_net_handlers me src m st = net_handlers (pt_map_name me) (pt_map_name src) m' (pt_map_data st).
Proof.
move => me src.
case => // d.
case => H_eq.
rewrite /pt_mapped_net_handlers.
repeat break_let.
apply net_handlers_NetHandler in Heqp.
net_handler_cases => //.
- by rewrite /= /runGenHandler_ignore /= H4.
- by rewrite /= /runGenHandler_ignore /id /= H3.
- by rewrite /= /runGenHandler_ignore /id /= H3.
Qed.

Lemma pt_net_handlers_none : forall me src m st out st' ps,
  pt_map_msg m = None ->
  net_handlers me src m st = (out, st', ps) ->
  pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = [].
Proof.
move => me src.
case => //.
move => m' d out d' ps H_eq H_eq'.
apply net_handlers_NetHandler in H_eq'.
net_handler_cases => //.
by rewrite /= H3.
Qed.

Lemma pt_input_handlers_some : forall me inp st inp',
  pt_map_input inp = Some inp' ->
  pt_mapped_input_handlers me inp st = input_handlers (pt_map_name me) inp' (pt_map_data st).
Proof. by []. Qed.

Lemma pt_input_handlers_none : forall me inp st out st' ps,
  pt_map_input inp = None ->
  input_handlers me inp st = (out, st', ps) ->
  pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = [].
Proof.
move => me.
case.
- move => m' d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  io_handler_cases => //.
  by rewrite /= H2.
- move => src d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  io_handler_cases => //.
  by rewrite /= H5.
- move => d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  by io_handler_cases.
Qed.

Lemma fail_msg_fst_snd : pt_map_msg msg_fail = Some (msg_fail).
Proof. by []. Qed.

Lemma adjacent_to_fst_snd : 
  forall n n', adjacent_to n n' <-> adjacent_to (pt_map_name n) (pt_map_name n').
Proof. by []. Qed.

Theorem Aggregation_Failed_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_o_f_star _ _ Aggregation_OverlayParams Aggregation_FailMsgParams step_o_f_init (failed, net) tr ->
    exists tr', @step_o_f_star _ _ FNO.Failure_OverlayParams FNO.Failure_FailMsgParams step_o_f_init (failed, pt_map_onet net) tr' /\
    pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
have H_sim := step_o_f_pt_mapped_simulation_star_1 pt_map_name_inv_inverse pt_map_name_inverse_inv pt_init_handlers_eq pt_net_handlers_some pt_net_handlers_none pt_input_handlers_some pt_input_handlers_none fail_msg_fst_snd adjacent_to_fst_snd.
rewrite /pt_map_name /= /id in H_sim.
move => onet failed tr H_st.
apply H_sim in H_st.
move: H_st => [tr' [H_st H_eq]].
rewrite map_id in H_st.
by exists tr'.
Qed.

Lemma in_msg_pt_map_msgs :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m0 l ->
    In m' (pt_map_msgs l).
Proof.
elim => //.
move => m1 l IH.
case.
case => //.
case: m1 => [m5|] H_eq H_in; last by left.
case: H_in => H_in //.
rewrite /=.
move: H_in.
exact: IH.
Qed.

Lemma in_pt_map_msgs_in_msg :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m' (pt_map_msgs l) ->
    In m0 l.
Proof.
elim => //.
move => m1 l IH.
case.
case => //.
case: m1 => [m5|] /= H_eq H_in; last by left.
right.
move: H_in.
exact: IH.
Qed.

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr n, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 ~ In n failed ->
 ~ FinNSet.In n (onwState net n).(adjacent).
Proof.
move => onet failed tr n H_st H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: FNO.Failure_node_not_adjacent_self H_st' H_in_f.
Qed.

Lemma Aggregation_not_failed_no_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H_st n n' H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FNO.Failure_not_failed_no_fail H_st' n n' H_in_f.
move => H_in.
case: H_inv'.
rewrite /= /id /=.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_in_adj_adjacent_to :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    Adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact (FNO.Failure_in_adj_adjacent_to H_st' n H_in_f H_ins).
Qed.

Lemma Aggregation_in_adj_or_incoming_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FNO.Failure_in_adj_or_incoming_fail H_st' _ H_in_f H_ins.
case: H_inv' => H_inv'; first by left.
right.
move: H_inv' => [H_in_f' H_inv'].
split => //.
move: H_inv'.
exact: in_pt_map_msgs_in_msg.
Qed.

Lemma count_occ_pt_map_msgs_eq :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  count_occ FNO.Msg_eq_dec (pt_map_msgs l) m' = count_occ Msg_eq_dec l m0.
Proof.
elim => //.
case => [m5|] l IH.
  case.
  case => //= H_eq.
  by rewrite (IH _ Fail).
case.
case => //= H_eq.
by rewrite (IH _ Fail).
Qed.

Lemma Aggregation_le_one_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st n n' H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FNO.Failure_le_one_fail H_st' _ n' H_in_f.
rewrite /= /id /= in H_inv'.
by rewrite (count_occ_pt_map_msgs_eq _ Fail) in H_inv'.
Qed.

Lemma Aggregation_adjacent_to_in_adj :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    Adjacent_to n' n ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_in_f' H_adj.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: (FNO.Failure_adjacent_to_in_adj H_st' H_in_f H_in_f' H_adj).
Qed.

Lemma Aggregation_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FNO.Failure_in_queue_fail_then_adjacent H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_ins.
exact: in_msg_pt_map_msgs.
Qed.

Lemma hd_error_pt_map_msgs :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  hd_error l = Some m0 ->
  hd_error (pt_map_msgs l) = Some m'.
Proof.
elim => //.
by case => [m5|] l IH; case; case.
Qed.

Lemma Aggregation_first_fail_in_adj : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_eq.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FNO.Failure_first_fail_in_adj H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Aggregation_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    FinNSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Aggregation_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

Lemma Aggregation_in_set_exists_find_sent : 
forall net failed tr, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 forall n, ~ In n failed ->
 forall n', FinNSet.In n' (net.(onwState) n).(adjacent) -> 
       exists m5 : m, FinNMap.find n' (net.(onwState) n).(sent) = Some m5.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}.
  rewrite H_init /=.
  move => n H_in_f n' H_ins.
  rewrite /init_map.
  case (init_map_str _) => mp H.
  have H' := H n'.
  apply H' in H_ins.
  by exists 1.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * move: H5 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H10 H11.
    rewrite H10 H9.
    exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H11.
    move => H_ins.
    have H_neq': n' <> from.
      move => H_eq.
      rewrite H_eq in H_ins.
      by apply FinNSetFacts.remove_1 in H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    rewrite /= in IHrefl_trans_1n_trace1.
    have [m5 IH'] := IHrefl_trans_1n_trace1 _ H3 _ H_ins.
    exists m5.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq'.
    by apply FinNMapFacts.find_mapsto_iff.
  * move: H13 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H8.
    move => H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  * move: H13 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H8.
    move => H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * move: H4 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H6 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H6.
    rewrite H7 H8 /=.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H11.
    move => H_ins.
    case (Name_eq_dec n' x) => H_dec'.
      rewrite H_dec'.
      exists (x0 * aggregate (onwState net h)).
      exact: FinNMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply FinNMapFacts.find_mapsto_iff.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H7 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
- move => n H_in n' H_ins.
  have H_neq: ~ In n failed by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma Aggregation_in_set_exists_find_received : 
forall net failed tr, 
 step_o_f_star step_o_f_init (failed, net) tr -> 
 forall n, ~ In n failed ->
 forall n', FinNSet.In n' (net.(onwState) n).(adjacent) -> 
    exists m5 : m, FinNMap.find n' (net.(onwState) n).(received) = Some m5.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}.
  rewrite H_init /=.
  move => n H_in_f n' H_ins.
  rewrite /init_map.
  case (init_map_str _) => mp H.
  have H' := H n'.
  apply H' in H_ins.
  by exists 1.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * move: H5 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H10 H11.
    rewrite H11 H9.
    move => H_ins.
    case (Name_eq_dec n' from) => H_dec'.
      rewrite H_dec'.
      exists (x0 * x).
      exact: FinNMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H4 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply FinNMapFacts.find_mapsto_iff.
  * move: H5 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H12 H10.
    move => H_ins.
    have H_neq': n' <> from.
      move => H_eq.
      rewrite H_eq in H_ins.
      by apply FinNSetFacts.remove_1 in H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    rewrite /= in IHrefl_trans_1n_trace1.
    have [m5 IH'] := IHrefl_trans_1n_trace1 _ H3 _ H_ins.
    exists m5.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq'.
    by apply FinNMapFacts.find_mapsto_iff.
  * move: H13 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H9.
    move => H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  * move: H13 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H9.
    move => H_ins.
    apply FinNSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * move: H4 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H6 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H6.
    rewrite H7 H9 /=.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H12.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H7 {H1}.
    rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; exact: IHrefl_trans_1n_trace1.
- move => n H_in n' H_ins.
  have H_neq: ~ In n failed by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Section SingleNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variable n : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (init_Data n).

Hypothesis recv_aggregate : 
  forall onet failed tr n' m' m0,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNMap.find n' (onet.(onwState) n).(received) = Some m0 ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add n' (m0 * m') (onet.(onwState) n).(received))).

Hypothesis recv_fail : 
  forall onet failed tr n' m_snt m_rcd,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNMap.find n' (onet.(onwState) n).(sent) = Some m_snt ->
    FinNMap.find n' (onet.(onwState) n).(received) = Some m_rcd ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m_snt * (m_rcd)^-1) (FinNSet.remove n' (onet.(onwState) n).(adjacent)) (FinNMap.remove n' (onet.(onwState) n).(sent)) (FinNMap.remove n' (onet.(onwState) n).(received))).

Hypothesis recv_local_weight : 
  forall onet failed tr m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  P (onet.(onwState) n) ->
  P (mkData m' ((onwState onet n).(aggregate) * m' * ((onwState onet n).(local))^-1) (onwState onet n).(adjacent) (onwState onet n).(sent) (onwState onet n).(received)).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n' m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNSet.In n' (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    FinNMap.find n' (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add n' (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)).

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
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2 to} in H0, H1, H2.
  net_handler_cases => //.
  * case: d H4 H5 H6 H7 H8 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H4 H5 H6 H7 H8.
    rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
    exact: (recv_aggregate _ _ H'_step1).
  * case: d H5 H6 H7 H8 H9 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
    exact: (recv_fail _ H'_step1).    
  * case (In_dec Name_eq_dec from failed) => H_in; first last.
      have H_fail := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      case: H_fail.
      rewrite H0.
      by left.
    have H_in': In Fail (onwPackets net from n) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ from H1 H_in'.    
    have [m5 H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * case (In_dec Name_eq_dec from failed) => H_in; first last.
      have H_fail := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      case: H_fail.
      rewrite H0.
      by left.
    have H_in': In Fail (onwPackets net from n) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ from H1 H_in'.    
    have [m5 H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
- move => H_in_f.
  find_apply_lem_hyp input_handlers_IOHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2} in H0 H1.
  io_handler_cases => //.
  * case: d H3 H4 H5 H6 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local_weight _ H'_step1).
  * case: d H5 H6 H7 H8 H9 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
    exact: (recv_send_aggregate H'_step1).
- move => H_in_f.
  apply: IHH'_step1.
  move => H'_in_f.
  case: H_in_f.
  by right.
Qed.

End SingleNodeInv.

Lemma collate_fail_for_notin :
  forall n h ns f failed,
    ~ In n ns ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => n h ns f failed.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (in_dec _ _) => H_dec.
  rewrite IH //.
  move => H_in'.
  by case: H_in; right.
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec'.
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

Lemma collate_fail_for_in_failed :
  forall n h ns f failed,
    In n failed ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => n h ns f failed.
move: f.
elim: ns => //.
  move => n' ns IH f H_in.
  rewrite /=.
  case (in_dec _ _) => H_dec; first by rewrite IH.
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec'; last by rewrite IH.
rewrite /= IH //.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_in.
Qed.  

Lemma collate_fail_for_not_adjacent :
  forall n h ns f failed,
    ~ Adjacent_to h n ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => n h ns f failed H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (in_dec _ _) => H_dec //.
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_neq :
  forall h n n' ns f,
    h <> n ->
    collate h f ns n n' = f n n'.
Proof.
move => h n n' ns f H_neq.
move: f.
elim: ns => //.
case.
move => n0 mg ms IH f.
rewrite /=.
rewrite IH.
rewrite /update2 /=.
case (sumbool_and _ _) => H_and //.
by move: H_and => [H_and H_and'].
Qed.

Lemma collate_fail_for_live_adjacent :
  forall n h ns f failed,
    ~ In n failed ->
    Adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (fail_for (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [Fail].
Proof.
move => n h ns f failed H_in H_adj.
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
  case (Adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_fail_for_notin //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
rewrite /=.
case (Adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by move: H_sumb => [H_eq H_eq'].
by rewrite IH.
Qed.

Definition self_channel_empty (n : Name) (onet : ordered_network) : Prop :=
onet.(onwPackets) n n = [].

Lemma Aggregation_self_channel_empty : 
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
  net_handler_cases => //=.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases; rewrite /collate /= //.
  * exact: IHrefl_trans_1n_trace1.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec' H_dec in H3.
    by have H_not := Aggregation_node_not_adjacent_self H H0 H3.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite collate_neq.
    apply: IHrefl_trans_1n_trace1.
    move => H_in'.
    case: H_in.
    by right.
  move => H_eq.
  by case: H_in; left.
Qed.

Lemma Aggregation_in_after_all_fail_aggregate : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall n, ~ In n failed ->
 forall n' m', In_all_before (Aggregate m') Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H1}.
  net_handler_cases => //=.
  * rewrite /update2.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H1 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; last by move: IH' => [H_neq H_bef].
    exact: not_in_all_before.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H1 H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; last by move: IH' => [H_neq H_bef].
    exact: not_in_all_before.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H1 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
- move {H1}. 
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * exact: IHrefl_trans_1n_trace1.
  * rewrite /= /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq'.
    rewrite H_eq in H2.
    apply: append_before_all_not_in.
    exact: Aggregation_not_failed_no_fail H _ _ H2.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
- move {H1} => n0 H_in_f n' m'.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  move {H_in_f}.
  case (Name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec in H_neq H2.
  rewrite H_dec {H_dec h}.
  case (Adjacent_to_dec n' n0) => H_dec; last first.
    rewrite collate_fail_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  rewrite collate_fail_for_live_adjacent //.
  * apply: append_neq_before_all => //.
    exact: IHrefl_trans_1n_trace1.
  * exact: In_n_Nodes.
  * exact: nodup.
Qed.

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
forall onet failed tr, 
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall n, ~ In n failed ->
  forall n' m5, In (Aggregate m5) (onet.(onwPackets) n' n) ->
 FinNSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H1}.
  net_handler_cases => //=.
  * rewrite /= in IHrefl_trans_1n_trace1.
    move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n0) by rewrite H2; right.
      case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H6 H7 H8 H9 H10.
      rewrite H8 -H_dec'.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n0) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H6 H7 H8 H9 H10.
      rewrite H8 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * rewrite /= in IHrefl_trans_1n_trace1.
    move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      rewrite H_eq'.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n0) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n0) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + rewrite -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H1 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H7 H8 H9 H10 H11.
      rewrite H9.
      move => H_ins.
      apply FinNSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H12.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H0 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H4 H5 H6 H7 H8 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H4 H5 H6 H7 H8.
      rewrite H6.
      move => H_ins.
      apply FinNSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H12.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      move => H_in.
      rewrite -H_dec' H_eq in H2.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H0 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H4 H5 H6 H7 H8 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H4 H5 H6 H7 H8.
      rewrite H6.
      move => H_ins.
      apply FinNSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
- move {H1}. 
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * move: H3.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move => H_in.
    case: d H6 H7 H8 H5 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H6 H7 H8 H5.
    rewrite H6 -H_dec.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update2 /update.
    case (sumbool_and _ _ _ _) => H_dec; case (Name_eq_dec _ _) => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq' H_dec' in H1.
      rewrite H_dec' in H0.
      by have H_self := Aggregation_node_not_adjacent_self H H0.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq' in H1.
      rewrite H_eq in H1.
      rewrite H_eq H_eq'.
      rewrite H_eq in H2.
      move => H_in.
      have H_adj := Aggregation_in_adj_adjacent_to H _ H2 H1.
      apply Adjacent_to_symmetric in H_adj.
      by have H_adj' := Aggregation_adjacent_to_in_adj H H0 H2 H_adj.
    + case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H7 H8 H9 H10 H11.
      rewrite H9 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H6.
    rewrite /= /update.
    case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
- move => n0 H_in_f n' m5 H_in {H1}.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  case (Name_eq_dec h n') => H_dec; last first.
    move: H_in.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec {h H_dec H_in_f} in H_in H_neq H2.
  case (Adjacent_to_dec n' n0) => H_dec; last first.
    move: H_in.
    rewrite collate_fail_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  move: H_in.
  rewrite collate_fail_for_live_adjacent //.
  * move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in; last by case: H_in => H_in.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * exact: In_n_Nodes.
  * exact: nodup.
Qed.

Section SingleNodeInvOut.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

Hypothesis recv_aggregate_neq_from :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  from <> n ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq_other_some :
  forall onet failed tr m' m0 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    FinNMap.find n (received (onet.(onwState) n')) = Some m0 ->
    onet.(onwPackets) n n' = Aggregate m' :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (onet.(onwState) n) ms.

Hypothesis recv_fail_neq_from :
  forall onet failed tr from m0 m1 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  from <> n ->
  FinNMap.find from (onwState onet n).(sent) = Some m0 ->
  FinNMap.find from (onwState onet n).(received) = Some m1 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (FinNSet.remove from (onet.(onwState) n).(adjacent)) (FinNMap.remove from (onet.(onwState) n).(sent)) (FinNMap.remove from (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_fail_neq :
  forall onet failed tr from m0 m1 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  n <> n' ->
  from <> n ->
  FinNMap.find from (onwState onet n).(sent) = Some m0 ->
  FinNMap.find from (onwState onet n).(received) = Some m1 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (FinNSet.remove from (onet.(onwState) n).(adjacent)) (FinNMap.remove from (onet.(onwState) n).(sent)) (FinNMap.remove from (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

Hypothesis recv_local_eq_some :
  forall onet failed tr m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      n <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      FinNSet.In n' (onet.(onwState) n).(adjacent) ->
      FinNMap.find n' (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (FinNMap.add n' (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n' ++ [Aggregate (onet.(onwState) n).(aggregate)]).

Hypothesis recv_local_neq_some :
  forall onet failed tr to m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      to <> n ->
      to <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      FinNSet.In to (onet.(onwState) n).(adjacent) ->
      FinNMap.find to (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (FinNMap.add to (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

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
  net_handler_cases => //.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H2 H4 H5 H6 H7 H8 H0 H1.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H6 H8 H0. 
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec.
        case: d H4 H5 H6 H7 H8 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8.
        rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
        exact: (recv_aggregate_neq_from H'_step1 _ H_dec H H0).
      case: d H4 H5 H6 H7 H8 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8.
      rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
      case (Name_eq_dec from n) => H_dec'.
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1 _ H1) in H0.
      exact: (recv_aggregate_neq H'_step1 H1 H_dec H_dec' H H0).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' in H_dec.
    rewrite H_dec' {from H_dec' H'_step2} in H H8 H0.
    rewrite H_dec'' {H_dec'' to} in H H1 H2 H4 H5 H6 H7 H8 H0.
    exact: (recv_aggregate_neq_other_some H'_step1 _ H_dec H H0).
  * rewrite /update.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H0.
      rewrite -H_dec.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec' //.
      move: H_dec' => [H_dec' H_dec''].
      rewrite -H_dec'' in H.
      rewrite H_dec' in H H0.
      by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' {H'_step2 to H_dec''} in H_dec H H1 H2 H0.
    rewrite H_dec' {H_dec' from} in H H2 H0.
    have H_in: In (Aggregate x) (onwPackets net n n') by rewrite H0; left.    
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 _ H1 _ _ H_in.
    have [m5 H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H2.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H4 H5 H6 H7 H8 H9.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      move {H'_step2 H_dec H1}.
      case: d H5 H6 H7 H8 H9 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.      
      case: H_dec' => H_dec'.
        case (In_dec Name_eq_dec from failed) => H_in; first exact: (recv_fail_neq_from H'_step1 H_in_f H_in H_dec' H H4 H0).
        have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
        rewrite H0 in H_inl.
        by case: H_inl; left.
      case (Name_eq_dec from n) => H_neq; first by rewrite H_neq (Aggregation_self_channel_empty H'_step1) in H0.
      case (In_dec Name_eq_dec from failed) => H_in; first exact: (recv_fail_neq H'_step1 _ _ H_dec' _ _ H4 H0).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H H4 H5 H6 H7 H8 H9 H0.
    rewrite H_eq' in H_dec.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H5.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      rewrite -H_dec in H9.
      have H_in: In Fail (onwPackets net from n) by rewrite H0; left.
      have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H_in_f H_in.
      have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H_in_f H_ins.
      by rewrite H_snt in H9.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H_dec H1 H0.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H0.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_eq H_eq'].
        rewrite H_eq in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      rewrite -H_dec in H9.
      have H_in: In Fail (onwPackets net from n) by rewrite H0; left.
      have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H_in_f H_in.
      have [m' H_rcd] := Aggregation_in_set_exists_find_received H'_step1 _ H_in_f H_ins.
      by rewrite H_rcd in H9.
   rewrite /update2 /=.
   case (sumbool_and _ _ _ _) => H_and.
     move: H_and => [H_eq H_eq'].
     rewrite H_eq' in H1.
     rewrite H_eq H_eq' in H0.
     have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
     rewrite H0 in H_f.
     by case: H_f; left.
   exact: H.               
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {h H_dec H'_step2} in H3 H4 H5 H6 H0.
    case: d H3 H4 H5 H6 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local _ H'_step1).
  * rewrite /update /= /update2.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec.
      rewrite -H_dec {h H_dec H'_step2} in H0 H1 H3 H4 H5 H6 H7 H8 H9.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec''.
        rewrite H_dec'' {x H_dec'' H_dec'} in H1 H3 H4 H8.
        case: d H4 H5 H6 H7 H8 H9 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8 H9.
        rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
        case (Name_eq_dec n n') => H_dec.
          have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
          by rewrite {1}H_dec in H_self.
        exact: (recv_local_eq_some H'_step1 H0 H_dec H3 H1).
      case: H_dec' => H_dec' //.
      case: d H4 H5 H6 H7 H8 H9 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
      case (Name_eq_dec x n) => H_dec.
        have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
        by rewrite -{1}H_dec in H_self.
      exact: (recv_local_neq_some H'_step1 H0 H_dec H_dec' H3 H1).
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec' in H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
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

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

Hypothesis recv_aggregate : 
  forall onet failed tr m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  FinNMap.find n' (onet.(onwState) n).(received) = Some m0 ->
  onet.(onwPackets) n' n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add n' (m0 * m') (onet.(onwState) n).(received))) ms.

Hypothesis recv_aggregate_other : 
  forall onet failed tr m' from m0,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n' ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n' n).

Hypothesis recv_fail : 
  forall onet failed tr m0 m1 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In n' failed ->
    n <> n' ->
    FinNMap.find n' (onwState onet n).(sent) = Some m0 ->
    FinNMap.find n' (onwState onet n).(received) = Some m1 ->
    onet.(onwPackets) n' n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (FinNSet.remove n' (onet.(onwState) n).(adjacent)) (FinNMap.remove n' (onet.(onwState) n).(sent)) (FinNMap.remove n' (onet.(onwState) n).(received))) ms.

Hypothesis recv_fail_other : 
  forall onet failed tr from m0 m1 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In from failed ->
    from <> n' ->
    FinNMap.find from (onwState onet n).(sent) = Some m0 ->
    FinNMap.find from (onwState onet n).(received) = Some m1 ->
    onet.(onwPackets) from n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (FinNSet.remove from (onet.(onwState) n).(adjacent)) (FinNMap.remove from (onet.(onwState) n).(sent)) (FinNMap.remove from (onet.(onwState) n).(received))) (onwPackets onet n' n).

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n0 m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    FinNSet.In n0 (onet.(onwState) n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    FinNMap.find n0 (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add n0 (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet failed tr to m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    to <> n ->
    FinNSet.In to (onet.(onwState) n).(adjacent) ->
    (onet.(onwState) n).(aggregate) <> 1 ->
    FinNMap.find to (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add to (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_neq :
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  (onet.(onwState) n').(aggregate) <> 1 ->
  FinNSet.In n (onet.(onwState) n').(adjacent) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n ++ [Aggregate (onet.(onwState) n').(aggregate)]).

Hypothesis recv_fail_neq :
  forall onet failed tr ms m m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  FinNMap.find n' (onet.(onwState) n).(sent) = Some m ->
  FinNMap.find n' (onet.(onwState) n).(received) = Some m' ->
  onwPackets onet n' n = Fail :: ms ->
  P (onwState onet n) (onwPackets onet n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m * m'^-1) (FinNSet.remove n' ((onet.(onwState) n).(adjacent))) (FinNMap.remove n' (onet.(onwState) n).(sent)) (FinNMap.remove n' (onet.(onwState) n).(received))) ms.

Hypothesis fail_adjacent :
  forall onet failed tr,
step_o_f_star step_o_f_init (failed, onet) tr ->
~ In n failed ->
~ In n' failed ->
n' <> n ->
Adjacent_to n' n ->
P (onwState onet n) (onwPackets onet n' n) ->
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
  net_handler_cases => //.   
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H1 H4 H5 H6 H7 H8 H0.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H8 H0.
        case: d H4 H5 H6 H7 H8 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8.
        rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
        case (Name_eq_dec n n') => H_dec'.
          rewrite -H_dec' in H0.
          by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
        exact: (recv_aggregate H'_step1 H1 H_dec' H H0).
      case: H_dec => H_dec //.
      case: d H4 H5 H6 H7 H8 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8.
      rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
      exact: (recv_aggregate_other _ H'_step1).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec'' in H_dec.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.    
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_rcd in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H0 H H4 H5 H6 H7 H8.
      case (In_dec Name_eq_dec n' failed) => H_in.
        rewrite /update /=.
        case (Name_eq_dec _ _) => H_dec; last by rewrite H_eq' in H_dec.
        rewrite -H_dec H_eq in H9.
        have H_neq: n <> n' by move => H_eq_n; rewrite -H_eq_n in H_in.
        move {H'_step2}.
        case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
        move => H5 H6 H7 H8 H9.
        rewrite H5 H6 H7 H8 H9.
        exact: (recv_fail H'_step1).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec'; last exact: H2.
    rewrite -H_dec' in H_dec.
    case: H_dec => H_dec //.
    rewrite -H_dec' {H_dec'} in H H0 H4 H5 H6 H7 H8 H9.
    case (In_dec Name_eq_dec from failed) => H_in.
      move {H'_step2}.
      case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {H5 H6 H7 H8 H9 local0 aggregate0 adjacent0 sent0 received0}.
      exact: (recv_fail_other H'_step1 _ _ _ _ _ H0).          
    have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
    rewrite H0 in H_inl.
    by case: H_inl; left.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H1 H_in.
    have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H1 H_in.
    have [m' H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
- move {H'_step2}.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {h H_dec} in H0 H3 H4 H1 H5 H6.
    case: d H3 H4 H5 H6 => /= local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local _ H'_step1).
  - rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_eq].
        rewrite H_eq -H_dec in H1.
        contradict H1.
        exact: (Aggregation_node_not_adjacent_self H'_step1).
      case: H_dec' => H_dec'.
        rewrite -H_dec in H_dec'.
        rewrite -H_dec {H_dec h} in H1 H3 H4 H5 H0 H7 H8 H9.
        case: d H6 H5 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 receive0.
        move => H6 H5 H7 H8 H9.
        rewrite H6 H5 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H6 H5 H7 H8 H9}.
        exact: (recv_send_aggregate H'_step1).
      rewrite -H_dec {H_dec h} in H1 H0 H3 H4 H5 H7 H8 H9.
      case: d H6 H5 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 receive0.
      move => H6 H5 H7 H8 H9.
      rewrite H6 H5 H7 H8 H9 {H6 H5 H7 H8 H9 local0 aggregate0 adjacent0 sent0 receive0}.
      exact: (recv_send_aggregate_other H'_step1).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec' in H_dec H H1 H4 H3 H5 H6 H7 H0 H8 H9.
    rewrite H_dec' {H_dec' h}.
    rewrite H_dec'' in H4 H8 H1.
    rewrite H_dec'' {H_dec'' x}.
    exact: (recv_send_aggregate_neq H'_step1).
  * have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H0 H.
    by rewrite H_snt in H4.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- move => H_in_f {H'_step2}.
  have H_neq: h <> n by move => H_neq'; case: H_in_f; left.
  have H_in_f': ~ In n failed by move => H_in; case: H_in_f; right.
  have IH := IHH'_step1 H_in_f'.
  rewrite /= in IH.
  case (Name_eq_dec h n') => H_dec; last by rewrite collate_neq.
  rewrite H_dec.
  rewrite H_dec {H_dec h H_in_f} in H0 H_neq.
  case (Adjacent_to_dec n' n) => H_dec; last by rewrite collate_fail_for_not_adjacent.
  rewrite collate_fail_for_live_adjacent //.
  * exact: (fail_adjacent H'_step1).
  * exact: In_n_Nodes.
  * exact: nodup.
Qed.

End SingleNodeInvIn.

Definition conserves_node_mass (d : Data) : Prop := 
d.(local) = d.(aggregate) * sumM d.(adjacent) d.(sent) * (sumM d.(adjacent) d.(received))^-1.

Lemma Aggregation_conserves_node_mass : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall n, ~ In n failed -> conserves_node_mass (onet.(onwState) n).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  move => n.
  rewrite H_init /conserves_node_mass /init_Data /= => H_in.
  by rewrite sumM_init_map_1; gsimpl.
move => n.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move {H1}.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {H_dec to H3} in H1 H5 H6 H7 H8 H9 H2.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {H5 H6 H7 H8 H9 local0 aggregate0 adjacent0 sent0 received0}.
    rewrite /conserves_node_mass /=.
    have H_ins: FinNSet.In from (net.(onwState) n).(adjacent).
      have H_in: In (Aggregate x) (net.(onwPackets) from n) by rewrite H2; left.
      exact: Aggregation_aggregate_msg_dst_adjacent_src H _ H0 _ _ H_in.
    rewrite IH sumM_add_map //; gsimpl.
    suff H_eq: (net.(onwState) n).(aggregate) * x * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * x^-1 * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
     (net.(onwState) n).(aggregate) * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 * (x * x^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H2; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H _ H3 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H _ H3 H_ins.
    by rewrite H_rcd in H1.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {H_dec to H3} in H1 H5 H6 H7 H8 H9 H10 H2.
    case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H6 H7 H8 H9 H10.
    rewrite H6 H7 H8 H9 H10 {H6 H7 H8 H9 H10 local0 aggregate0 adjacent0 sent0 received0}.
    rewrite /conserves_node_mass /= IH.
    have H_in: In Fail (net.(onwPackets) from n) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H0 H_in.
    rewrite (sumM_remove_remove _ H_ins H1) (sumM_remove_remove _ H_ins H5); gsimpl.
    suff H_eq: 
      (net.(onwState) n).(aggregate) * x * x0^-1 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * x^-1 * x0 * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
      (net.(onwState) n).(aggregate) * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 * (x * x^-1) * (x0 * x0^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have H_in: In Fail (net.(onwPackets) from to) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H3 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_sent H _ H3 H_ins.
    by rewrite H_rcd in H11.
  * have H_in: In Fail (net.(onwPackets) from to) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H3 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H _ H3 H_ins.
    by rewrite H_rcd in H11.
- move {H1}.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {h H_dec} in H5 H2 H6 H7 H4.
    case: d H5 H6 H7 H4 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H4.
    rewrite /conserves_node_mass /= H5 H6 H7 H4 {H5 H6 H7 H4 aggregate0 adjacent0 sent0 received0}.
    rewrite IH; gsimpl.
    suff H_eq: 
        (net.(onwState) n).(aggregate) * local0 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent))^-1 * (net.(onwState) n).(aggregate)^-1 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
        local0 * ((net.(onwState) n).(aggregate) * (net.(onwState) n).(aggregate)^-1) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent))^-1) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    rewrite -H_dec {h H_dec} in H1 H2 H4 H5 H6 H8 H9 H10.
    case: d H7 H6 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H6 H8 H9 H10.
    rewrite /conserves_node_mass /= H7 H6 H8 H9 H10 {H7 H6 H8 H9 H10 aggregate0 adjacent0 sent0 received0}.
    rewrite IH sumM_add_map; gsimpl.
    by aac_reflexivity.
  * have [m5 H_rcd] := Aggregation_in_set_exists_find_sent H _ H2 H1.
    by rewrite H_rcd in H5.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /= in IH.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    by rewrite -H_dec.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    by rewrite -H_dec.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec //.
    by rewrite -H_dec.
- move => H_in_f.
  have H_in_f': ~ In n failed0 by move => H_in; case: H_in_f; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Definition sum_local (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * d.(local)) 1 l.

Definition sum_aggregate (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * d.(aggregate)) 1 l.

Definition sum_sent (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * sumM d.(adjacent) d.(sent)) 1 l.

Definition sum_received (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * sumM d.(adjacent) d.(received)) 1 l.

Definition conserves_mass_globally (l : list Data) : Prop :=
sum_local l = sum_aggregate l * sum_sent l * (sum_received l)^-1.

Definition conserves_node_mass_all (l : list Data) : Prop :=
forall d, In d l -> conserves_node_mass d.

Lemma global_conservation : 
  forall (l : list Data), 
    conserves_node_mass_all l ->
    conserves_mass_globally l.
Proof.
rewrite /conserves_mass_globally /=.
elim => [|d l IH]; first by gsimpl.
move => H_cn.
rewrite /=.
rewrite /conserves_node_mass_all in H_cn.
have H_cn' := H_cn d.
rewrite H_cn'; last by left.
rewrite IH; first by gsimpl; aac_reflexivity.
move => d' H_in.
apply: H_cn.
by right.
Qed.

Definition Nodes_data (ns : list Name) (onet : ordered_network) : list Data :=
fold_right (fun (n : Name) (l' : list Data) => (onet.(onwState) n) :: l') [] ns.

Lemma Aggregation_conserves_node_mass_all : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_node_mass_all (Nodes_data Nodes onet).
Proof.
fail.
move => onet failed tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data.
elim: Nodes => //.
move => n l IH.
move => d.
rewrite /=.
move => H_or.
case: H_or => H_or.
  rewrite -H_or.
  apply: (Aggregation_conserves_node_mass H_st).
exact: IH.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet tr,
 step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
 conserves_mass_globally (Nodes_data Nodes onet).
Proof.
move => onet tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

Definition aggregate_sum_fold (msg : Msg) (partial : m) : m :=
match msg with
| Aggregate m' => partial * m'
end.

Definition sum_aggregate_msg := fold_right aggregate_sum_fold 1.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall onet tr,
   step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
   forall n, sum_aggregate_msg (onet.(onwPackets) n n) = 1.
Proof.
move => onet tr H_step n.
by rewrite (Aggregation_self_channel_empty H_step).
Qed.

(* given n, sum aggregate messages for all its incoming channels *)
Definition sum_aggregate_msg_incoming (ns : list Name) (onet : ordered_network) (n : Name) : m := 
fold_right (fun (n' : Name) (partial : m) => partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.

(* given list of active names and all names, sum all incoming channels for all active *)
Definition sum_aggregate_msg_incoming_active (allns : list Name) (actns : list Name)  (onet : ordered_network) : m :=
fold_right (fun (n : Name) (partial : m) => partial * sum_aggregate_msg_incoming allns onet n) 1 actns.

Definition conserves_network_mass (actns : list Name) (allns : list Name) (onet : ordered_network) : Prop :=
sum_local (Nodes_data actns onet) = sum_aggregate (Nodes_data actns onet) * sum_aggregate_msg_incoming_active allns actns onet.

Lemma sum_aggregate_msg_incoming_step_o_init :
  forall ns n, sum_aggregate_msg_incoming ns step_o_init n = 1.
Proof.
move => ns n.
rewrite /sum_aggregate_msg_incoming /= {n}.
elim: ns => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_all_step_o_init :
  forall actns allns, sum_aggregate_msg_incoming_active allns actns step_o_init = 1.
Proof.
rewrite /sum_aggregate_msg_incoming_active /=.
elim => [|a l IH] l' //=.
rewrite IH sum_aggregate_msg_incoming_step_o_init.
by gsimpl.
Qed.

Lemma sum_local_step_o_init :
  forall ns, sum_local (Nodes_data ns step_o_init) = 1.
Proof.
rewrite /Nodes_data /step_o_init /=.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_step_o_init :
  forall ns, sum_aggregate (Nodes_data ns step_o_init) = 1.
Proof.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_local_split :
  forall ns0 ns1 onet n,
    sum_local (Nodes_data (ns0 ++ n :: ns1) onet) =
    (onet.(onwState) n).(local) * sum_local (Nodes_data (ns0 ++ ns1) onet).
Proof.
elim => /=; first by move => ns1 onet n; aac_reflexivity.
move => n ns IH ns1 onet n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma sum_aggregate_split :
  forall ns0 ns1 onet n,
    sum_aggregate (Nodes_data (ns0 ++ n :: ns1) onet) =
    (onet.(onwState) n).(aggregate) * sum_aggregate (Nodes_data (ns0 ++ ns1) onet).
Proof.
elim => /=; first by move => ns1 onet n; aac_reflexivity.
move => n ns IH ns1 onet n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma nodup_notin : 
  forall (A : Type) (a : A) (l l' : list A),
    NoDup (l ++ a :: l') ->
    ~ In a (l ++ l').
Proof.
move => A a.
elim => /=; first by move => l' H_nd; inversion H_nd; subst.
move => a' l IH l' H_nd.
inversion H_nd; subst.
move => H_in.
case: H_in => H_in.
  case: H1.
  apply in_or_app.
  by right; left.
contradict H_in.
exact: IH.
Qed.

Lemma Nodes_data_not_in : 
forall n' d onet ns,
~ In n' ns ->
fold_right
  (fun (n : Name) (l : list Data) =>
     (match Name_eq_dec n n' with
      | left _ => d 
      | right _ => (onet.(onwState) n) 
      end) :: l) [] ns = Nodes_data ns onet.
Proof.
move => n' d onet.
elim => //.
move => a l IH H_in.
rewrite /=.
case (Name_eq_dec _ _) => H_dec; first by case: H_in; left.
rewrite IH => //.
move => H_in'.
by case: H_in; right.
Qed.

(* with failed nodes - don't add their incoming messages, but add their outgoing channels to non-failed nodes *)

Lemma sum_aggregate_msg_neq_from :
forall from to n onet ms ns,
~ In from ns ->
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns =
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.
Proof.
move => from to n onet ms.
elim => //.
move => n0 ns IH H_in.
rewrite /= IH /=; last by move => H_in'; case: H_in; right.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_dec H_dec'].
case: H_in.
by left.
Qed.

Lemma sum_aggregate_msg_n_neq_from :
forall from to n onet ms ns,
to <> n ->
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns =
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.
Proof.
move => from to n onet ms ns H_neq.
elim: ns => //.
move => n' l IH.
rewrite /= IH /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
by move: H_dec => [H_dec H_dec'].
Qed.

Lemma sum_aggregate_msg_neq_to :
forall from to onet ms ns1 ns0,
~ In to ns1 ->
fold_right
  (fun (n : Name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : Name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (update2 onet.(onwPackets) from to ms n' n)) 1 ns0) 1 ns1 = 
fold_right
  (fun (n : Name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : Name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns0) 1 ns1.
Proof.
move => from to onet ms.
elim => //=.
move => n l IH ns H_in.
rewrite IH /=; last by move => H_in'; case: H_in; right.
have H_neq: to <> n by move => H_eq; case: H_in; left.
by rewrite sum_aggregate_msg_n_neq_from.
Qed.

Lemma sum_aggregate_msg_fold_split :
forall ns0 ns1 ns2 from to ms onet,
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 (ns1 ++ ns2) = 
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 ns1 * 
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 ns2.
Proof.
move => ns0 ns1 ns2 from to ms onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split_folded :
forall ns0 ns1 from to n onet ms,
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 (ns0 ++ ns1) = 
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0 *
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns1.
Proof.
move => ns0 ns1 from to n onet ms.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH /=.
by aac_reflexivity.
Qed.


Lemma sum_aggregate_msg_incoming_active_split :
forall ns0 ns1 ns2 onet,
sum_aggregate_msg_incoming_active ns0 (ns1 ++ ns2) onet = 
sum_aggregate_msg_incoming_active ns0 ns1 onet *
sum_aggregate_msg_incoming_active ns0 ns2 onet.
Proof.
move => ns0 ns1 ns2 onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_split :
forall ns0 ns1 onet n,
sum_aggregate_msg_incoming (ns0 ++ ns1) onet n = 
sum_aggregate_msg_incoming ns0 onet n *
sum_aggregate_msg_incoming ns1 onet n.
Proof.
move => ns0 ns1 onet n.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split : 
forall l1 l2,
sum_aggregate_msg (l1 ++ l2) = sum_aggregate_msg l1 * sum_aggregate_msg l2.
Proof.
elim => //= [|msg l' IH] l2; first by gsimpl.
rewrite IH.
rewrite /aggregate_sum_fold /=.
case: msg => m'.
by aac_reflexivity.
Qed.

Lemma fold_right_update_id :
forall ns h x',
fold_right 
  (fun (n : Name) (l' : list Data) =>
     update (onwState x') h (onwState x' h) n :: l') [] ns =
fold_right 
  (fun (n : Name) (l' : list Data) =>
     (onwState x' n) :: l') [] ns.
Proof.
elim => //.
move => n l IH h onet.
rewrite /= IH.
rewrite /update /=.
case (Name_eq_dec _ _) => H_dec //.
by rewrite H_dec.
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall onet tr,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  conserves_network_mass Nodes Nodes onet.
Proof.
move => onet tr H_step.
remember step_o_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /conserves_network_mass /= {H_init}.
  rewrite sum_aggregate_msg_incoming_all_step_o_init.
  rewrite sum_local_step_o_init sum_aggregate_step_o_init.
  by gsimpl.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
  - rewrite /= /conserves_network_mass /=.
    have H_inn := In_n_Nodes to.     
    apply in_split in H_inn.
    move: H_inn => [ns0 [ns1 H_inn]].
    rewrite H_inn sum_local_split. 
    rewrite sum_aggregate_split /=.
    rewrite /Nodes_data.
    rewrite {2}/update /=.
    have H_nd := nodup.
    rewrite H_inn in H_nd.
    have H_nin := nodup_notin _ _ _ H_nd.
    rewrite (Nodes_data_not_in _ d x' _ H_nin).
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec // {H_dec}.
    rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
    rewrite H2 H3 {H_nd H_nin}.
    rewrite /conserves_network_mass in IHH_step1.
    rewrite H_inn in IHH_step1.
    rewrite sum_local_split in IHH_step1.
    rewrite sum_aggregate_split in IHH_step1.
    rewrite sum_aggregate_msg_fold_split.   
    have H_inn': In from Nodes by exact: In_n_Nodes.
    apply in_split in H_inn'.
    move: H_inn' => [ns2 [ns3 H_in']].
    rewrite -{1}H_inn.
    have H_nin: ~ In to ns0.
      have H_nd := nodup.
      rewrite H_inn in H_nd.
      have H_nin := nodup_notin _ _ _ H_nd.
      move => H_nin'.
      case: H_nin.
      apply in_or_app.
      by left.    
    rewrite {1}sum_aggregate_msg_neq_to //.
    rewrite -/(sum_aggregate_msg_incoming_active Nodes ns0 x').
    rewrite /=.
    have H_nin': ~ In to ns1.
      have H_nd := nodup.
      rewrite H_inn in H_nd.
      have H_nin' := nodup_notin _ _ _ H_nd.
      move => H_nin''.
      case: H_nin'.
      apply in_or_app.
      by right.
    rewrite {1}sum_aggregate_msg_neq_to //.
    rewrite -{1}H_inn.
    rewrite -/(sum_aggregate_msg_incoming_active Nodes ns1 x').
    rewrite -H_inn {3}H_in'.
    rewrite sum_aggregate_msg_split_folded /=.
    have H_nin_f: ~ In from ns2.
      have H_nd := nodup.
      rewrite H_in' in H_nd.
      have H_nin_f := nodup_notin _ _ _ H_nd.
      move => H_nin_f'.
      case: H_nin_f.
      apply in_or_app.
      by left.
    have H_nin_f': ~ In from ns3.
      have H_nd := nodup.
      rewrite H_in' in H_nd.
      have H_nin_f' := nodup_notin _ _ _ H_nd.
      move => H_nin_f''.
      case: H_nin_f'.
      apply in_or_app.
      by right.
    rewrite sum_aggregate_msg_neq_from //.    
    rewrite -/(sum_aggregate_msg_incoming ns2 x' to).
    rewrite sum_aggregate_msg_neq_from //.    
    rewrite -/(sum_aggregate_msg_incoming ns3 x' to).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec => H_dec.
    rewrite -{1}H_inn in IHH_step1.
    rewrite H_in' in IHH_step1.
    rewrite sum_aggregate_msg_incoming_active_split /= in IHH_step1.
    rewrite -{1 2}H_in' in IHH_step1.
    rewrite sum_aggregate_msg_incoming_split /= in IHH_step1.
    rewrite H0 /= in IHH_step1.
    rewrite IHH_step1.
    gsimpl.
    set mm := sum_aggregate _.
    by aac_reflexivity.    
  - have H_in_ag: In (Aggregate x) (x'.(onwPackets) from to) by rewrite H0; left.
    have H_adj := Aggregation_aggregate_msg_src_adjacent_dst H_step1 _ _ _ H_in_ag.
    have [m' H_recv] := Aggregation_in_set_exists_find_received H_step1 _ H_adj.
    by rewrite H in H_recv.
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases => // {H_step2}.
- (* Local *)
  rewrite /=.
  rewrite /conserves_network_mass /=.
  have H_inn := In_n_Nodes h.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  rewrite H_inn sum_local_split. 
  rewrite sum_aggregate_split /=.
  rewrite /Nodes_data.
  rewrite {2}/update /=.
  have H_nd := nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  rewrite (Nodes_data_not_in _ d x' _ H_nin).
  rewrite {1 2}/update /=.
  case (Name_eq_dec _ _) => H_dec // {H_dec}.
  rewrite -H_inn.
  rewrite /sum_aggregate_msg_incoming_active /=.
  rewrite /sum_aggregate_msg_incoming /=.
  rewrite /conserves_network_mass in IHH_step1.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  rewrite {1 2}H_inn in IHH_step1.
  rewrite sum_local_split sum_aggregate_split in IHH_step1.
  rewrite H1.
  suff H_suff: sum_local (Nodes_data (ns0 ++ ns1) x') = aggregate (onwState x' h) * (local (onwState x' h))^-1 * sum_aggregate (Nodes_data (ns0 ++ ns1) x') * sum_aggregate_msg_incoming_active Nodes Nodes x'.
    rewrite H_suff.
    gsimpl.
    set mm := sum_aggregate _.
    by aac_reflexivity.
  have ->: sum_local (Nodes_data (ns0 ++ ns1) x') = sum_local (Nodes_data (ns0 ++ ns1) x') * local (onwState x' h) * (local (onwState x' h))^-1 by gsimpl.
  aac_rewrite IHH_step1.
  by aac_reflexivity.  
- (* send Aggregate *)
  rewrite /conserves_network_mass /=.
  have H_inn := In_n_Nodes h.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  rewrite H_inn sum_local_split /=.
  rewrite sum_aggregate_split /=.
  rewrite /Nodes_data.
  rewrite {2}/update /=.
  have H_nd := nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  rewrite (Nodes_data_not_in _ d x' _ H_nin).
  rewrite {1 2}/update /=.
  case (Name_eq_dec _ _) => H_dec // {H_dec}.
  rewrite H3 H4.
  gsimpl.
  rewrite -H_inn.
  rewrite /sum_aggregate_msg_incoming_active /=.
  rewrite /sum_aggregate_msg_incoming /=.
  have H_inn': In x Nodes by exact: In_n_Nodes.
  apply in_split in H_inn'.
  move: H_inn' => [ns2 [ns3 H_in']].
  rewrite {2}H_in'.
  have H_nin': ~ In x ns2.
    have H_nd' := nodup.
    rewrite H_in' in H_nd'.
    have H_nin' := nodup_notin _ _ _ H_nd'.
    move => H_nin''.
    case: H_nin'.
    apply in_or_app.
    by left.  
  rewrite sum_aggregate_msg_fold_split.
  rewrite sum_aggregate_msg_neq_to //.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes ns2 x').
  rewrite /=.
  have H_nin'': ~ In x ns3.
    have H_nd' := nodup.
    rewrite H_in' in H_nd'.
    have H_nin'' := nodup_notin _ _ _ H_nd'.
    move => H_nin'''.
    case: H_nin''.
    apply in_or_app.
    by right.
  rewrite sum_aggregate_msg_neq_to //.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes ns3 x').
  rewrite {3}H_inn.
  rewrite sum_aggregate_msg_split_folded.
  have H_nin_h: ~ In h ns0.
    move => H_in_h.
    case: H_nin.
    apply in_or_app.
    by left.
  have H_nin'_h: ~ In h ns1.
    move => H_in_h.
    case: H_nin.
    apply in_or_app.
    by right.
  rewrite sum_aggregate_msg_neq_from //.
  rewrite /=.
  rewrite sum_aggregate_msg_neq_from //.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  gsimpl.
  rewrite -/(sum_aggregate_msg_incoming ns0 x' x).
  rewrite -/(sum_aggregate_msg_incoming ns1 x' x).
  rewrite sum_aggregate_msg_split /=.
  gsimpl.
  rewrite /conserves_network_mass in IHH_step1.
  rewrite {1 2}H_inn in IHH_step1.
  rewrite sum_local_split in IHH_step1.
  rewrite sum_aggregate_split in IHH_step1.
  rewrite {2}H_in' in IHH_step1.
  rewrite sum_aggregate_msg_incoming_active_split /= in IHH_step1.
  rewrite {3}H_inn in IHH_step1.
  rewrite sum_aggregate_msg_incoming_split /= in IHH_step1.
  move: IHH_step1.
  gsimpl.
  move => IH.
  rewrite IH.
  set mm := sum_aggregate _.
  by aac_reflexivity.  
- have [m' H_recv] := Aggregation_in_set_exists_find_sent H_step1 _ H.
  by find_rewrite.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
Qed.

(*
Inductive step_o_f : step_relation (list name * ordered_network) (name * (input + list output)) :=
| SOF_deliver : forall net net' failed m ms out d l from to,
                   onwPackets net from to = m :: ms ->
                   ~ In to failed ->
                   net_handlers to from m (onwState net to) = (out, d, l) ->
                   net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l) (update (onwState net) to d) ->
                   step_o_f (failed, net) (failed, net') [(to, inr out)]
| SOF_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                 input_handlers h inp (onwState net h) = (out, d, l) ->
                 net' = mkONetwork (collate h (onwPackets net) l) (update (onwState net) h d) ->
                 step_o_f (failed, net) (failed, net') [(h, inl inp); (h, inr out)]
| SOF_fail :  forall h net net' failed l,
               ~ In h failed ->
               l =  ->
               net' = mkONetwork (collate h (onwPackets net) l) (onwState net) ->
               step_o_f (failed, net) (h :: failed, net') [].

Definition step_o_f_star := refl_trans_1n_trace step_o_f.

Definition step_o_f_init : list name * ordered_network := ([], step_o_init).
*)


(* hook up tree-building protocol to SendAggregate input for aggregation protocol *)

(* merge sent and received into "balance" map? *)

(* use boolean function, name-to-list function, or decision procedure for adjacency *)
(* at recovery time, send new to all existing neighbors *)
(* handle problem with unprocessed fail messages for recovery *)

(* higher-level language like ott/lem for protocols that exports to handlers? *)

(* 
path to liveness properties:

- handler monad must be able to output labels, e.g., return broadcast_level

- all labels must be decorated with the involved node names by the semantics

- labels must be removed at extraction time

- is strong local liveness warranted in practice? how can extraction guarantee it?

*)

(*Parameter adjacentP : Name -> Name -> Prop.*)

(*
firstin q5 (msg_new j) ->
dequeued q5 q' ->
sum_aggregate_queue_ident q' i5 = sum_aggregate_queue_ident q5 i5.
*)

(*
firstin q5 (msg_aggregate j m5) ->
  dequeued q5 q' ->
  sum_aggregate_queue_ident q' j = sum_aggregate_queue_ident q5 j * m5^-1.
*)

(* 
sum_aggregate_queue (queue_enqueue q5 (msg_aggregate j m5)) = sum_aggregate_queue q5 * m5.
*)

(* 
~ ISet.in j ->
snd (sum_aggregate_queue_aux (I5, m') (queue_enqueue q5 (msg_aggregate j m5))) = 
snd (sum_aggregate_queue_aux (I5, m') q5) * m5.
*)

(* 
  ~ In_queue (msg_fail j) q5 ->
  sum_aggregate_queue (queue_enqueue q5 (msg_fail j)) = sum_aggregate_queue q5 * (sum_aggregate_queue_ident q5 j)^-1.
*)

(* ---------------------------------- *)

(*
Section StepFailureMsg.

  (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_fm : step_relation (list name * network) (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SFM_deliver : forall net net' failed p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) failed ->
                net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                 (update (nwState net) (pDst p) d) ->
                step_fm (failed, net) (failed, net') [(pDst p, inr out)]
  | SFM_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                  input_handlers h inp (nwState net h) = (out, d, l) ->
                  net' = mkNetwork (send_packets h l ++ nwPackets net)
                                   (update (nwState net) h d) ->
                  step_fm (failed, net) (failed, net') [(h, inl inp) ;  (h, inr out)]
  (* a host fails and a Fail message is delivered to all adjacent hosts *)
  (* add same node to failed several times? *)
  (* use adjacency function *)
  | SFM_fail :  forall h net failed,
                 step_fm (failed, net) (h :: failed, net) [].

  Definition step_fm_star : step_relation (list name * network) (name * (input + list output)) :=
    refl_trans_1n_trace step_fm.

  Definition step_fm_init : list name * network := ([], step_m_init).
End StepFailureMsg.
*)

End Aggregation.

(* 

Module NatValue10 <: NatValue.
 Definition n := 10.
End NatValue10.

Module fin_10_compat_OT := fin_OT_compat NatValue10.

Require Import FMapList.
Module Map <: FMapInterface.S := FMapList.Make fin_10_compat_OT.

Definition b : fin 10 := Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))).

Eval compute in Map.find b (Map.add b 3 (Map.empty nat)).

Module fin_10_OT := fin_OT NatValue10.

Require Import MSetList.
Module FinSet <: MSetInterface.S := MSetList.Make fin_10_OT.
Eval compute in FinSet.choose (FinSet.singleton b).

*)

(*
Definition exclude (excluded : list Name) := filter (fun n => sumbool_not _ _ (in_dec Name_eq_dec n excluded)).

Definition fail_for := map (fun (n : Name) => (n, Fail)).

Inductive step_o_f : step_relation (list Name * ordered_network) (Name * (input + list output)) :=
| SOF_deliver : forall net net' failed m ms out d l from to,
                   onwPackets net from to = m :: ms ->
                   ~ In to failed ->
                   net_handlers to from m (onwState net to) = (out, d, l) ->
                   net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l) (update (onwState net) to d) ->
                   step_o_f (failed, net) (failed, net') [(to, inr out)]
| SOF_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                 input_handlers h inp (onwState net h) = (out, d, l) ->
                 net' = mkONetwork (collate h (onwPackets net) l) (update (onwState net) h d) ->
                 step_o_f (failed, net) (failed, net') [(h, inl inp); (h, inr out)]
| SOF_fail :  forall h net net' failed l,
               ~ In h failed ->
               l = fail_for (adjacent_to_node h (exclude failed nodes)) ->
               net' = mkONetwork (collate h (onwPackets net) l) (onwState net) ->
               step_o_f (failed, net) (h :: failed, net') [].

Definition step_o_f_star := refl_trans_1n_trace step_o_f.

Definition step_o_f_init : list Name * ordered_network := ([], step_o_init).
*)
