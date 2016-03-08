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

Lemma collate_msg_for_not_adjacent :
  forall m n h ns f failed,
    ~ Adjacent_to h n ->
    collate h f (msg_for m (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m n h ns f failed H_adj.
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

Lemma collate_msg_for_live_adjacent :
  forall m n h ns f failed,
    ~ In n failed ->
    Adjacent_to h n ->
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
  case (Adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_msg_for_notin //.
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
      rewrite collate_msg_for_live_adjacent //.      
      * apply (fail_adjacent H'_step1) => //.
        exact: IHH'_step1.
      * exact: In_n_Nodes.
      * exact: nodup.
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
    rewrite collate_msg_for_live_adjacent //.
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
     put (mkData st.(local) new_aggregate st.(adjacent) new_sent st.(received)) ;; 
     send (dst, (Aggregate st.(aggregate)))
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
have H_sim := step_o_f_pt_mapped_simulation_star_1 pt_map_name_inv_inverse pt_map_name_inverse_inv pt_init_handlers_eq pt_net_handlers_some pt_net_handlers_none pt_input_handlers_some pt_input_handlers_none adjacent_to_fst_snd fail_msg_fst_snd.
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

Lemma collate_msg_for_notin :
  forall m' n h ns f failed,
    ~ In n ns ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m' n h ns f failed.
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

Lemma collate_msg_for_in_failed :
  forall m' n h ns f failed,
    In n failed ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m' n h ns f failed.
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

Lemma collate_msg_for_not_adjacent :
  forall m' n h ns f failed,
    ~ Adjacent_to h n ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m' n h ns f failed H_adj.
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

Lemma collate_msg_for_live_adjacent :
  forall m' n h ns f failed,
    ~ In n failed ->
    Adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [m'].
Proof.
move => m' n h ns f failed H_in H_adj.
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
  rewrite collate_msg_for_notin //.
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
    rewrite collate_msg_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  rewrite collate_msg_for_live_adjacent //.
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
    rewrite collate_msg_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  move: H_in.
  rewrite collate_msg_for_live_adjacent //.
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
  case (Adjacent_to_dec n' n) => H_dec; last by rewrite collate_msg_for_not_adjacent.
  rewrite collate_msg_for_live_adjacent //.
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
 conserves_node_mass_all (Nodes_data (exclude failed Nodes) onet).
Proof.
move => onet failed tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data.
elim: Nodes => //=.
move => n l IH.
move => d.
case (in_dec _ _ _) => H_dec; first exact: IH.
move => H_or.
case: H_or => H_or.
  rewrite -H_or.
  exact: (Aggregation_conserves_node_mass H_st).
exact: IH.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_mass_globally (Nodes_data (exclude failed Nodes) onet).
Proof.
move => onet failed tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

(* ------ *)

Definition aggregate_sum_fold (msg : Msg) (partial : m) : m :=
match msg with
| Aggregate m' => partial * m'
| _ => partial
end.

Definition sum_aggregate_msg := fold_right aggregate_sum_fold 1.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed -> sum_aggregate_msg (onet.(onwPackets) n n) = 1.
Proof.
move => onet failed tr H_step n H_in_f.
by rewrite (Aggregation_self_channel_empty H_step).
Qed.

(* given n, sum aggregate messages for all its incoming channels *)
Definition sum_aggregate_msg_incoming (ns : list Name) (f : Name -> Name -> list Msg) (n : Name) : m := 
fold_right (fun (n' : Name) (partial : m) => 
  partial * if In_dec Msg_eq_dec Fail (f n' n) then 1 else sum_aggregate_msg (f n' n)) 1 ns.

(* given list of active names and all names, sum all incoming channels for all active *)
Definition sum_aggregate_msg_incoming_active (allns : list Name) (actns : list Name)  (onet : ordered_network) : m :=
fold_right (fun (n : Name) (partial : m) => partial * sum_aggregate_msg_incoming allns onet.(onwPackets) n) 1 actns.

Definition sum_fail_map (l : list Msg) (from : Name) (adj : FinNS) (map : FinNM) : m :=
if In_dec Msg_eq_dec Fail l && FinNSet.mem from adj then sum_fold map from 1 else 1.

Definition sum_fail_map_incoming (ns : list Name) (f : Name -> Name -> list Msg) (n : Name) (adj : FinNS) (map : FinNM) : m :=
  fold_right (fun (n' : Name) (partial : m) => partial * sum_fail_map (f n' n) n' adj map) 1 ns.

Definition sum_fail_sent_incoming_active (allns : list Name) (actns : list Name) (onet : ordered_network) : m :=
fold_right (fun (n : Name) (partial : m) => 
  partial * sum_fail_map_incoming allns onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent)) 1 actns.

Definition sum_fail_received_incoming_active (allns : list Name) (actns : list Name) (onet : ordered_network) : m :=
fold_right (fun (n : Name) (partial : m) => 
  partial * sum_fail_map_incoming allns onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received)) 1 actns.

Definition conserves_network_mass (actns : list Name) (allns : list Name) (onet : ordered_network) : Prop :=
sum_local (Nodes_data actns onet) = 
  sum_aggregate (Nodes_data actns onet) * sum_aggregate_msg_incoming_active allns actns onet * 
  sum_fail_sent_incoming_active allns actns onet * (sum_fail_received_incoming_active allns actns onet)^-1.

Lemma sum_aggregate_msg_incoming_step_o_init :
  forall ns n, sum_aggregate_msg_incoming ns step_o_init.(onwPackets) n = 1.
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

Lemma sum_aggregate_msg_incoming_neq_eq :
  forall ns n f from to ms,
  n <> to ->
  sum_aggregate_msg_incoming ns (update2 f from to ms) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //.
move => n ns IH n' f from to ms H_neq.
rewrite /= IH //.
rewrite /update2 /=.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_aggregate_msg_incoming_active_not_in_eq :
  forall ns ns' from to h ms d f g,
    ~ In to ns ->
    sum_aggregate_msg_incoming_active ns' ns
     {| onwPackets := update2 f from to ms;
        onwState := update g h d |} = 
    sum_aggregate_msg_incoming_active ns' ns {| onwPackets := f; onwState := g |}.
Proof.
elim => //=.
move => n ns IH ns' from to h ms d f g H_in.
have H_not_in: ~ In to ns by move => H_in'; case: H_in; right.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_active_not_in_eq_alt :
  forall ns ns' h d net,
    sum_aggregate_msg_incoming_active ns' ns
     {| onwPackets := onwPackets net;
        onwState := update (onwState net) h d |} = 
    sum_aggregate_msg_incoming_active ns' ns net.
Proof. by []. Qed.

Lemma sum_aggregate_msg_incoming_not_in_eq :
forall ns ns0 f from to ms,
~ In to ns0 ->
fold_right
     (fun (n0 : Name) (partial : m) =>
      partial * sum_aggregate_msg_incoming ns (update2 f from to ms) n0) 1 ns0 =
fold_right
     (fun (n0 : Name) (partial : m) =>
      partial * sum_aggregate_msg_incoming ns f n0) 1 ns0.
Proof.
move => ns ns0 f from to ms.
elim: ns0 => //.
move => n ns' IH.
rewrite /=.
move => H_in.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_in': ~ In to ns' by move => H_in'; case: H_in; right.
rewrite IH //.
set m1 := sum_aggregate_msg_incoming _ _ _.
set m2 := sum_aggregate_msg_incoming _ _ _.
suff H_suff: m1 = m2 by rewrite H_suff.
move {IH ns' H_in' H_in}.
rewrite /m1 /m2 {m1 m2}.
elim: ns => //.
move => n' ns IH.
rewrite /= IH.
suff H_suff: update2 f from to ms n' n = f n' n by rewrite H_suff.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
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

Lemma sum_fail_sent_incoming_active_split :
  forall ns0 ns1 ns2 onet,
    sum_fail_sent_incoming_active ns0 (ns1 ++ ns2) onet = 
    sum_fail_sent_incoming_active ns0 ns1 onet *
    sum_fail_sent_incoming_active ns0 ns2 onet.
Proof.
move => ns0 ns1 ns2 onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_fail_received_incoming_active_split :
  forall ns0 ns1 ns2 onet,
    sum_fail_received_incoming_active ns0 (ns1 ++ ns2) onet = 
    sum_fail_received_incoming_active ns0 ns1 onet *
    sum_fail_received_incoming_active ns0 ns2 onet.
Proof.
move => ns0 ns1 ns2 onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split : 
  forall l1 l2,
    sum_aggregate_msg (l1 ++ l2) = sum_aggregate_msg l1 * sum_aggregate_msg l2.
Proof.
elim => //= [|msg l' IH] l2; first by gsimpl.
rewrite IH.
rewrite /aggregate_sum_fold /=.
by case: msg => [m'|]; aac_reflexivity.
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

(* take Fail messages into account when summing up Aggregate messages *)

Lemma In_n_exclude : 
  forall n ns ns',
    ~ In n ns' ->
    In n ns ->
    In n (exclude ns' ns).
Proof.
move => n.
elim => //=.
move => n' ns IH ns' H_in H_in'.
case: H_in' => H_in'.
  rewrite H_in'.
  case (in_dec _ _) => H_dec //.
  by left.
case (in_dec _ _) => H_dec; first exact: IH.
right.
exact: IH.
Qed.

Lemma exclude_in : 
  forall n ns ns',
    In n (exclude ns' ns) ->
    In n ns.
Proof.
move => n.
elim => //=.
move => n' ns IH ns'.
case (in_dec _ _) => H_dec.
  move => H_in.
  right.
  move: H_in.
  exact: IH.
move => H_in.
case: H_in => H_in; first by left.
right.
move: H_in.
exact: IH.
Qed.

Lemma nodup_exclude : 
  forall ns ns', 
    NoDup ns ->
    NoDup (exclude ns' ns).
Proof.
elim => //.
move => n ns IH ns' H_nd.
rewrite /=.
inversion H_nd.
case (in_dec _ _) => H_dec; first exact: IH.
apply NoDup_cons.
  move => H_in.
  case: H1.
  move: H_in.
  exact: exclude_in.
exact: IH.
Qed.

Lemma sum_aggregate_msg_incoming_update2_eq :
  forall ns f from to ms n,
  ~ In from ns ->
  sum_aggregate_msg_incoming ns (update2 f from to ms) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n l IH f from to ms n' H_in.
have H_in' : ~ In from l by move => H_in'; case: H_in; right.
rewrite IH //.
have H_neq: n <> from by move => H_eq; case: H_in; left.
rewrite /update2 /=.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq in H_neq.
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    ~ In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to * (m')^-1.
Proof.
elim => //.
move => n ns IH f from to ms m' H_in H_nd H_f H_eq.
case: H_in => H_in.  
  rewrite H_in /=.
  case (in_dec _ _) => H_dec; case (in_dec _ _) => H_dec' //=.
    rewrite H_eq in H_dec'.
    case: H_dec'.
    right.    
    move: H_dec.
    rewrite /update2.
    by case (sumbool_and _ _ _ _) => H_dec.
  rewrite H_eq /=.
  gsimpl.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec''; last by case: H_dec''.
  rewrite H_in in H_nd.
  inversion H_nd.
  by rewrite sum_aggregate_msg_incoming_update2_eq.
rewrite /=.
inversion H_nd.
rewrite (IH f from to ms m') //.
have H_neq: n <> from by move => H_eq'; rewrite H_eq' in H1.
case (in_dec _ _) => H_dec; case (in_dec _ _) => H_dec' //=.
- by gsimpl.
- case: H_dec'.
  move: H_dec.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
- case: H_dec.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
- rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec0; first by move: H_dec0 => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
  by aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_sent_neq_eq :
  forall ns net from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 (onwPackets net) from to ms) n
    (adjacent (match Name_eq_dec n to with left _ => d | right_ => onwState net n end))
    (sent (match Name_eq_dec n to with left _ => d |right _ => onwState net n end)) =
  sum_fail_map_incoming ns (onwPackets net) n (adjacent (onwState net n)) (sent (onwState net n)).
Proof.
elim => //=.
move => n ns IH net from to ms n0 d H_neq.
rewrite IH //.
case (Name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_map_incoming_received_neq_eq :
  forall ns net from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 (onwPackets net) from to ms) n
    (adjacent (match Name_eq_dec n to with left _ => d | right_ => onwState net n end))
    (received (match Name_eq_dec n to with left _ => d |right _ => onwState net n end)) =
  sum_fail_map_incoming ns (onwPackets net) n (adjacent (onwState net n)) (received (onwState net n)).
Proof.
elim => //=.
move => n ns IH net from to ms n0 d H_neq.
rewrite IH //.
case (Name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq :
  forall ns0 ns1 net from to ms d,
    ~ In to ns0 ->
    sum_fail_sent_incoming_active ns1 ns0
      {| onwPackets := update2 (onwPackets net) from to ms; 
         onwState := fun nm : Name => match Name_eq_dec nm to with left _ => d | right _ => onwState net nm end |} =
    sum_fail_sent_incoming_active ns1 ns0 net.
Proof.
elim => //.
move => n ns IH ns1 net from to ms d H_in.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_sent_neq_eq //.
rewrite -/(sum_fail_sent_incoming_active _ _ _).
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 net from to ms d H_in'.
by rewrite -IH'.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt :
forall ns net h d,
  ~ In h ns ->
  sum_fail_sent_incoming_active Nodes ns
     {| onwPackets := onwPackets net;
        onwState := update (onwState net) h d |} =
  sum_fail_sent_incoming_active Nodes ns net.
Proof.
elim => //=.
move => n ns IH net h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (Name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq :
  forall ns0 ns1 net from to ms d,
    ~ In to ns0 ->
    sum_fail_received_incoming_active ns1 ns0
      {| onwPackets := update2 (onwPackets net) from to ms; 
         onwState := fun nm : Name => match Name_eq_dec nm to with left _ => d | right _ => onwState net nm end |} =
    sum_fail_received_incoming_active ns1 ns0 net.
Proof.
elim => //.
move => n ns IH ns1 net from to ms d H_in.
rewrite /sum_fail_received_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_received_neq_eq //.
rewrite -/(sum_fail_received_incoming_active _ _ _).
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 net from to ms d H_in'.
by rewrite -IH'.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt :
forall ns net h d,
  ~ In h ns ->
  sum_fail_received_incoming_active Nodes ns
     {| onwPackets := onwPackets net;
        onwState := update (onwState net) h d |} =
  sum_fail_received_incoming_active Nodes ns net.
Proof.
elim => //=.
move => n ns IH net h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (Name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_map_incoming_not_in_eq :
  forall ns f from to ms adj map,
    ~ In from ns ->
    sum_fail_map_incoming ns (update2 f from to ms) to adj map =
    sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms adj map H_in.
have H_neq: n <> from by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq H_eq'].
by rewrite H_eq in H_neq.
Qed.

Lemma no_fail_sum_fail_map_incoming_eq :
  forall ns mg f from to ms adj map,  
  In from ns ->
  NoDup ns ->
  f from to = mg :: ms ->
  ~ In Fail (f from to) ->
  sum_fail_map_incoming ns (update2 f from to ms) to adj map =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH mg f from to ms adj map.
case => H_in H_eq H_in'.
  rewrite H_in.
  rewrite H_in in H_eq.
  rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  inversion H_eq.
  move => H_not_in.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite {2}/sum_fail_map.
  case (in_dec _ _) => /= H_dec' //.
  rewrite H_in' in H_not_in.
  have H_not_in': ~ In Fail ms by move => H_inn; case: H_not_in; right.
  rewrite {1}/sum_fail_map.
  by case (in_dec _ _) => /= H_dec''.
inversion H_eq.
move => H_inn.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
rewrite {2}/update2 /=.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1].
by rewrite (IH mg f from to ms adj map H_in).
Qed.

Lemma sum_fail_map_incoming_add_not_in_eq :
  forall ns f m' from to adj map,
  ~ In from ns ->
  sum_fail_map_incoming ns f to adj (FinNMap.add from m' map) =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f m' from to adj map H_in.
have H_neq: from <> n by move => H_eq; case: H_in; left.
have H_not_in: ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /sum_fail_map /sum_fold.
case H_find: (FinNMap.find _ _) => [m0|]; case H_find': (FinNMap.find _ _) => [m1|] //.
- apply FinNMapFacts.find_mapsto_iff in H_find.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  rewrite H_find in H_find'.
  by inversion H_find'.
- apply FinNMapFacts.find_mapsto_iff in H_find.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  by rewrite H_find in H_find'.
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply (FinNMapFacts.add_neq_mapsto_iff _ m' _ H_neq) in H_find'.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find in H_find'.
Qed.

Lemma no_fail_sum_fail_map_incoming_add_eq :
  forall ns mg m' f from to ms adj map,  
  In from ns ->
  NoDup ns ->
  f from to = mg :: ms ->
  ~ In Fail (f from to) ->
  sum_fail_map_incoming ns (update2 f from to ms) to adj (FinNMap.add from m' map) =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH mg m' f from to ms adj map.
case => H_in H_eq H_in'.
  rewrite H_in.
  rewrite H_in in H_eq.
  rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  inversion H_eq.
  move => H_not_in.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite {2}/sum_fail_map.
  case (in_dec _ _) => /= H_dec' //.
  rewrite H_in' in H_not_in.
  have H_not_in': ~ In Fail ms by move => H_inn; case: H_not_in; right.
  rewrite {1}/sum_fail_map /=.
  case (in_dec _ _) => /= H_dec'' //.
  by rewrite sum_fail_map_incoming_add_not_in_eq.
move => H_inn.
inversion H_eq.
rewrite (IH _ _ _ _ _ _ _ _ H_in H2 H_in' H_inn).
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1].
rewrite /sum_fail_map.
case (in_dec _ _) => /= H_dec' //.
case (FinNSet.mem _ _) => //.
rewrite /sum_fold.
case H_find: (FinNMap.find _ _) => [m0|]; case H_find': (FinNMap.find _ _) => [m1|] //.
- apply FinNMapFacts.find_mapsto_iff in H_find.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  rewrite H_find in H_find'.
  by inversion H_find'.
- apply FinNMapFacts.find_mapsto_iff in H_find.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  by rewrite H_find in H_find'.
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply (FinNMapFacts.add_neq_mapsto_iff _ m' _ H_neq) in H_find'.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find in H_find'.
Qed.

Lemma sum_aggregate_msg_incoming_update2_fail_eq : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
elim => //=.
move => n ns IH f from to ms m' H_in H_nd H_in' H_eq.
case: H_in => H_in.
  inversion H_nd.
  rewrite H_in.
  rewrite H_in {H_in l x H H0 n H_nd} in H1.
  have H_in'' := H_in'.
  rewrite H_eq in H_in''.
  case: H_in'' => H_in'' //.
  case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
  - by rewrite sum_aggregate_msg_incoming_update2_eq.
  - case: H_dec.
    rewrite /update2.
    by case (sumbool_and _ _ _ _) => H_dec_s.
inversion H_nd => {x l H H0}.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec'.
- by rewrite (IH _ _ _ _ m').
- case: H_dec'.
  move: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- case: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec_s; first by move: H_dec_s => [H_eq' H_eq''].
  by rewrite (IH _ _ _ _ m').
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate_in_fail_add :
  forall ns f from to ms m' x x0 adj map,
    FinNSet.In from adj ->
    In from ns ->
    NoDup ns ->
    In Fail (f from to) -> 
    f from to = Aggregate m' :: ms ->
    FinNMap.find from map = Some x0 ->
    sum_fail_map_incoming ns (update2 f from to ms) to adj (FinNMap.add from (x0 * x) map) =
    sum_fail_map_incoming ns f to adj map * x.
Proof.
elim => //=.
move => n ns IH f from to ms m' x x0 adj map H_ins H_in H_nd H_in' H_eq H_find.
case: H_in => H_in.
  inversion H_nd.
  rewrite H_in.
  rewrite H_in {H_in l x1 H H0 n H_nd} in H1.
  have H_in'' := H_in'.
  rewrite H_eq in H_in''.
  case: H_in'' => H_in'' //.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite /sum_fail_map.
  case (in_dec _ _) => H_dec' //=.
  case (in_dec _ _) => H_dec'' //=.
  case H_mem: (FinNSet.mem _ _).
    rewrite /sum_fold.
    case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|].
    - rewrite H_find'' in H_find.
      injection H_find => H_eq'.
      rewrite H_eq'.
      rewrite FinNMapFacts.add_eq_o // in H_find'.
      injection H_find' => H_eq''.
      rewrite -H_eq''.
      by gsimpl.
    - by rewrite H_find'' in H_find.
    - by rewrite FinNMapFacts.add_eq_o in H_find'.
    - by rewrite H_find'' in H_find.
  apply FinNSetFacts.mem_1 in H_ins.
  by rewrite H_ins in H_mem.
inversion H_nd.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ H_eq) //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
rewrite /sum_fail_map /sum_fold.
case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|] //.
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  injection H_find'' => H_eq'.
  rewrite H_eq'.
  by aac_reflexivity.
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.  
- apply FinNMapFacts.find_mapsto_iff in H_find''.
  apply (FinNMapFacts.add_neq_mapsto_iff _ (x0 * x) _ H_neq) in H_find''.
  apply FinNMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find' in H_find''.
- by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate_in_fail :
  forall ns f from to ms m' adj map,
    In from ns ->
    NoDup ns ->
    f from to = Aggregate m' :: ms ->
    sum_fail_map_incoming ns (update2 f from to ms) to adj map =
    sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms m' adj map H_in H_nd H_eq.
inversion H_nd => {x l H H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  rewrite H_eq.
  rewrite /sum_fail_map.
  by case (in_dec _ _ _) => /= H_dec'; case (in_dec _ _ _) => /= H_dec''.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite (IH _ _ _ _ _ _ _ _ _ H_eq) //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
Qed.

Lemma sum_fail_map_incoming_update2_remove_eq :
  forall ns f from to ms adj map,
  ~ In from ns ->
  sum_fail_map_incoming ns (update2 f from to ms) to (FinNSet.remove from adj) (FinNMap.remove from map) =
  sum_fail_map_incoming ns (update2 f from to ms) to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms adj map H_in.
have H_neq: from <> n by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite {2 4}/update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and' //.
- rewrite /sum_fold.
  case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|] //.
  * apply FinNMapFacts.find_mapsto_iff in H_find'.
    apply FinNMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply FinNMapFacts.find_mapsto_iff in H_find'.
    rewrite H_find' in H_find''.
    injection H_find'' => H_eq'.
    rewrite H_eq'.
    by aac_reflexivity.
  * apply FinNMapFacts.find_mapsto_iff in H_find'.
    apply FinNMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply FinNMapFacts.find_mapsto_iff in H_find'.
    by rewrite H_find' in H_find''.
  * apply FinNMapFacts.find_mapsto_iff in H_find''.
    apply (FinNMapFacts.remove_neq_mapsto_iff _ m1 H_neq) in H_find''.
    apply FinNMapFacts.find_mapsto_iff in H_find''.
    by rewrite H_find' in H_find''.
- move: H_and =>  [H_dec' H_mem].
  case: H_and'.
  split => //.
  apply FinNSetFacts.mem_2 in H_mem.
  apply FinNSetFacts.mem_1.
  by apply FinNSetFacts.remove_3 in H_mem.
- move: H_and' => [H_dec' H_mem].
  apply FinNSetFacts.mem_2 in H_mem.
  case: H_and.
  split => //.
  apply FinNSetFacts.mem_1.
  by apply FinNSetFacts.remove_2.
Qed.

Lemma sum_fail_map_incoming_fail_remove_eq :
  forall ns f from to ms x adj map,
    In from ns ->
    NoDup ns ->
    FinNSet.In from adj ->
    f from to = Fail :: ms ->
    ~ In Fail ms ->
    FinNMap.find from map = Some x ->
    sum_fail_map_incoming ns (update2 f from to ms) to (FinNSet.remove from adj) (FinNMap.remove from map) =
    sum_fail_map_incoming ns f to adj map * x^-1.
Proof.
elim => //=.
move => n ns IH f from to ms x adj map H_in H_nd H_ins H_eq H_in' H_find.
inversion H_nd.
move {x0 H0 l H H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1.
  rewrite sum_fail_map_incoming_update2_remove_eq //.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  rewrite /sum_fail_map.
  case: andP => H_and; case: andP => H_and'.
  - move: H_and => [H_f H_mem].
    move: H_f.
    by case (in_dec _ _) => /= H_f.
  - move: H_and => [H_f H_mem].
    move: H_f.
    by case (in_dec _ _) => /= H_f.
  - rewrite sum_fail_map_incoming_not_in_eq //.
    rewrite /sum_fold.
    case H_find': (FinNMap.find _ _) => [m0|]; last by rewrite H_find' in H_find.
    rewrite H_find in H_find'.
    inversion H_find'.
    by gsimpl.
  - case: H_and'.
    split; first by rewrite H_eq.
    exact: FinNSetFacts.mem_1.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
rewrite (IH _ _ _ _ x) //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and'.
- rewrite /sum_fold.
  case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|].
  * apply FinNMapFacts.find_mapsto_iff in H_find'.
    apply FinNMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply FinNMapFacts.find_mapsto_iff in H_find'.
    rewrite H_find' in H_find''.
    injection H_find'' => H_eq'.
    rewrite H_eq'.
    by aac_reflexivity.
  * apply FinNMapFacts.find_mapsto_iff in H_find'.
    apply FinNMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply FinNMapFacts.find_mapsto_iff in H_find'.
    by rewrite H_find' in H_find''.
  * apply FinNMapFacts.find_mapsto_iff in H_find''.
    apply (FinNMapFacts.remove_neq_mapsto_iff _ m1 H_neq) in H_find''.
    apply FinNMapFacts.find_mapsto_iff in H_find''.
    by rewrite H_find' in H_find''.
  * by gsimpl.
- move: H_and => [H_f H_mem].
  case: H_and'.
  split => //.
  apply FinNSetFacts.mem_2 in H_mem.
  apply FinNSetFacts.remove_3 in H_mem.
  exact: FinNSetFacts.mem_1.
- move: H_and' => [H_f H_mem].
  case: H_and.
  split => //.
  apply FinNSetFacts.mem_2 in H_mem.
  apply FinNSetFacts.mem_1.
  exact: FinNSetFacts.remove_2.
- by gsimpl.
Qed.

Lemma sum_aggregate_ms_no_aggregate_1 : 
  forall ms,
  (forall m' : m, ~ In (Aggregate m') ms) -> 
  sum_aggregate_msg ms = 1.
Proof.
elim => //.
move => mg ms IH.
case: mg; first by move => m' H_in; case (H_in m'); left.
move => H_in /=.
rewrite IH //.
move => m' H_in'.
case (H_in m').
by right.
Qed.

Lemma sum_aggregate_msg_incoming_fail_update2_eq :
  forall ns f from to ms,
    (forall m', In_all_before (Aggregate m') Fail (f from to)) ->
    In from ns ->
    NoDup ns ->
    ~ In Fail ms ->
    f from to = Fail :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
elim => //=.
move => n ns IH f from to ms H_bef H_in H_nd H_in' H_eq.
inversion H_nd => {x H l H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {n H_in} in H1. 
  case (in_dec _ _ _) => /= H_dec; case (in_dec _ _ _) => /= H_dec' //.
  - move: H_dec.
    rewrite {1}/update2.
    case (sumbool_and _ _ _ _) => H_s //.
    by case: H_s.
  - rewrite H_eq in H_dec'.
    by case: H_dec'; left.
  - rewrite {2}/update2.
    case (sumbool_and _ _ _ _) => H_s; last by case: H_s.
    rewrite sum_aggregate_msg_incoming_update2_eq //.
    have H_not_in: forall m', ~ In (Aggregate m') ms.
      move => m'.
      apply (@head_before_all_not_in _ _ _ Fail) => //.
      rewrite -H_eq.
      exact: H_bef.
    by rewrite sum_aggregate_ms_no_aggregate_1.
  - rewrite H_eq in H_dec'.
    by case: H_dec'; left.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
case (in_dec _ _ _) => /= H_dec; case (in_dec _ _ _) => /= H_dec' //.
- by rewrite IH.
- move: H_dec.
  rewrite {1}/update2.
  by case (sumbool_and _ _ _ _) => H_dec.
- case: H_dec.
  rewrite {1}/update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_s //.
  by move: H_s => [H_eq' H_eq''].
Qed.

Lemma Nodes_data_split :
  forall ns0 ns1 onet,
    Nodes_data (ns0 ++ ns1) onet =
    Nodes_data ns0 onet ++ Nodes_data ns1 onet.
Proof.
elim => //.
move => n ns0 IH ns1 onet.
rewrite /=.
by rewrite IH.
Qed.

Lemma Nodes_data_not_in_eq :
  forall ns net from to ms d l,
    ~ In to ns ->
    Nodes_data ns {| onwPackets := collate to (update2 (onwPackets net) from to ms) l; onwState := update (onwState net) to d |} =
    Nodes_data ns net.
Proof.
elim => //.
move => n ns IH net from to ms d l H_in.
rewrite /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite {1}/update /=.
case (Name_eq_dec _ _) => H_dec //.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma Nodes_data_not_in_eq_alt :
  forall ns net h d l,
    ~ In h ns ->
    Nodes_data ns {| onwPackets := collate h (onwPackets net) l; onwState := update (onwState net) h d |} =
    Nodes_data ns net.
Proof.
elim => //.
move => n ns IH net h d l H_in.
rewrite /=.
have H_neq: n <> h by move => H_eq; case: H_in; left.
rewrite {1}/update /=.
case (Name_eq_dec _ _) => H_dec //.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma sum_sent_distr : 
  forall dl dl',
    sum_sent (dl ++ dl') = sum_sent dl * sum_sent dl'.
Proof.
elim => /=; first by move => dl'; gsimpl.
move => d dl IH dl'.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_received_distr : 
  forall dl dl',
    sum_received (dl ++ dl') = sum_received dl * sum_received dl'.
Proof.
elim => /=; first by move => dl'; gsimpl.
move => d dl IH dl'.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma in_not_in_exclude : 
  forall ns ns' n,
    In n ns' ->
    ~ In n (exclude ns' ns).
Proof.
elim => //=; first by move => ns' n H_in H_n.
move => n ns IH ns' n' H_in.
case (in_dec _ _) => H_dec; first exact: IH.
move => H_in'.
case: H_in' => H_in'; first by rewrite H_in' in H_dec.
contradict H_in'.
exact: IH.
Qed.

Lemma sum_aggregate_msg_incoming_active_not_in_eq_alt2 :
  forall ns ns' from to ms h d net,
    ~ In to ns ->
    sum_aggregate_msg_incoming_active ns' ns 
      {| onwPackets := update2 (onwPackets net) from to ms;
         onwState := update (onwState net) h d |} =
    sum_aggregate_msg_incoming_active ns' ns net.
Proof.
elim => //=.
move => n ns IH ns' from to ms h d net H_in.
have H_not_in: ~ In to ns by move => H_in'; case: H_in; right.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma sum_fail_map_incoming_sent_neq_eq_alt :
  forall ns net from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 (onwPackets net) from to ms) n
    (adjacent (update (onwState net) h d n))
    (sent (update (onwState net) h d n)) =
  sum_fail_map_incoming ns (onwPackets net) n (adjacent (onwState net n)) (sent (onwState net n)).
Proof.
elim => //=.
move => n ns IH net from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update.
case (Name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt2 :
  forall ns0 ns1 net from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_sent_incoming_active ns1 ns0
      {| onwPackets := update2 (onwPackets net) from to ms; 
         onwState := update (onwState net) h d |} =
    sum_fail_sent_incoming_active ns1 ns0 net.
Proof.
elim => //.
move => n ns IH ns1 net from to ms h d H_in H_in'.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
rewrite sum_fail_map_incoming_sent_neq_eq_alt //.
rewrite -/(sum_fail_sent_incoming_active _ _ _).
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
have IH' := IH ns1 net from to ms h d H_inn H_inn'.
by rewrite -IH'.
Qed.

Lemma sum_fail_map_incoming_received_neq_eq_alt :
  forall ns net from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 (onwPackets net) from to ms) n
    (adjacent (update (onwState net) h d n))
    (received (update (onwState net) h d n)) =
  sum_fail_map_incoming ns (onwPackets net) n (adjacent (onwState net n)) (received (onwState net n)).
Proof.
elim => //=.
move => n ns IH net from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update.
case (Name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt2 :
  forall ns0 ns1 net from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_received_incoming_active ns1 ns0
      {| onwPackets := update2 (onwPackets net) from to ms; 
         onwState := update (onwState net) h d |} =
    sum_fail_received_incoming_active ns1 ns0 net.
Proof.
elim => //.
move => n ns IH ns1 net from to ms h d H_in H_in'.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
rewrite sum_fail_map_incoming_received_neq_eq_alt //.
rewrite -/(sum_fail_received_incoming_active _ _ _).
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
have IH' := IH ns1 net from to ms h d H_inn H_inn'.
by rewrite -IH'.
Qed.

Lemma sum_fail_map_incoming_update2_not_eq :
  forall ns f h n ms adj map,
      h <> n ->
      sum_fail_map_incoming ns (update2 f h n ms) h adj map =
      sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n0 l IH f h n ms adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_map_incoming_add_aggregate_eq :
  forall ns f x h x0 m' adj map,
    h <> x ->
    In x ns ->
    NoDup ns ->
    In Fail (f x h) ->
    FinNMap.find x map = Some x0 ->
    FinNSet.In x adj ->
    sum_fail_map_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) h adj (FinNMap.add x (x0 * m') map) =
    sum_fail_map_incoming ns f h adj map * m'.
Proof.
elim => //.
move => n ns IH f x h x0 m' adj map H_neq H_in H_nd H_in' H_find H_ins.
rewrite /=.
inversion H_nd => {x1 H l H0}.
case: H_in => H_in.
  rewrite -H_in.
  rewrite -H_in {H_in x} in H_in' H_neq H_find H_ins.
  rewrite sum_fail_map_incoming_update2_not_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite /sum_fail_map.
  case (in_dec _ _ _) => /= H_dec' //=.
  case H_mem: (FinNSet.mem _ _); last by rewrite FinNSetFacts.mem_1 in H_mem.
  rewrite /sum_fold.
  case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|].
  - rewrite FinNMapFacts.add_eq_o // in H_find'.
    inversion H_find'.
    rewrite H_find'' in H_find.
    inversion H_find.
    by gsimpl.
  - by rewrite H_find'' in H_find.
  - by rewrite FinNMapFacts.add_eq_o // in H_find'.
  - by rewrite H_find'' in H_find.
rewrite IH //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec //; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
have H_neq': x <> n by move => H_eq; rewrite H_eq in H_in.
rewrite /sum_fail_map.
rewrite /sum_fold.
case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|].
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  inversion H_find''.
  by case: andP => H_and; gsimpl; aac_reflexivity.  
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.
- apply FinNMapFacts.find_mapsto_iff in H_find''.
  apply (FinNMapFacts.add_neq_mapsto_iff _ (x0 * m') _ H_neq') in H_find''.
  apply FinNMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find'' in H_find'.
- by gsimpl; aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_not_in_fail_add_update2_eq :
  forall ns f h x ms m' adj map,
    h <> x ->
    In x ns ->
    NoDup ns ->
    ~ In Fail (f x h) ->
    sum_fail_map_incoming ns (update2 f h x ms) h adj (FinNMap.add x m' map) =
    sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n ns IH f h x ms m' adj map H_neq H_in H_nd H_in'.
inversion H_nd => {l H0 x0 H H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {n H_in} in H1.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite sum_fail_map_incoming_update2_not_eq //.
  rewrite /sum_fail_map.
  by case (in_dec _ _) => /= H_dec'.
have H_neq': x <> n by move => H_eq; rewrite H_eq in H_in.
rewrite IH //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite /sum_fail_map /sum_fold.
case H_find': (FinNMap.find _ _) => [m0|]; case H_find'': (FinNMap.find _ _) => [m1|].
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  inversion H_find''.
  by case: andP => H_and; gsimpl; aac_reflexivity.  
- apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.
- apply FinNMapFacts.find_mapsto_iff in H_find''.
  apply (FinNMapFacts.add_neq_mapsto_iff _ m' _ H_neq') in H_find''.
  apply FinNMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find'' in H_find'.
- by gsimpl; aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_not_in_fail_update2_eq :
  forall ns f h x ms adj map,
    h <> x ->
    sum_fail_map_incoming ns (update2 f h x ms) h adj map =
    sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n ns IH f h x ms adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_update_not_in_eq :
  forall ns0 ns1 f g h d,
    ~ In h ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 {| onwPackets := f; onwState := update g h d |} =
    sum_fail_sent_incoming_active ns1 ns0 {| onwPackets := f; onwState := g |}.
Proof.
elim => //=.
move => n ns IH ns1 f g h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (Name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_update_not_in_eq :
  forall ns0 ns1 f g h d,
    ~ In h ns0 ->
    sum_fail_received_incoming_active ns1 ns0 {| onwPackets := f; onwState := update g h d |} =
    sum_fail_received_incoming_active ns1 ns0 {| onwPackets := f; onwState := g |}.
Proof.
elim => //=.
move => n ns IH ns1 f g h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (Name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_map_incoming_update2_app_eq : 
  forall ns f h x n m' adj map,
    sum_fail_map_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) n adj map = 
    sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n ns IH f h x n0 m' adj map.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _ _ _) => /= H_dec //.
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and' //.
  move: H_dec => [H_eq H_eq'].
  rewrite H_eq H_eq' {h x H_eq H_eq'} in H_and H_and'.
  move: H_and => [H_dec' H_mem].
  move: H_dec'.
  case (in_dec _ _) => /= H_dec' H_eq //.
  apply in_app_or in H_dec'.
  case: H_dec' => H_dec'; last by case: H_dec'.
  case: H_and'.
  split => //.
  by case (in_dec _ _).
move: H_dec => [H_eq H_eq'].
rewrite H_eq H_eq' {h x H_eq H_eq'} in H_and H_and'.
move: H_and' => [H_dec' H_mem].
move: H_dec'.
case (in_dec _ _) => /= H_dec' H_eq //.
case: H_and.
case (in_dec _ _) => /= H_dec //.
split => //.
case: H_dec.
apply in_or_app.
by left.
Qed.

Lemma sum_fail_sent_incoming_active_update2_app_eq :
  forall ns0 ns1 f h x m' g,
    (*~ In Fail (f h x) ->*)
    sum_fail_sent_incoming_active ns1 ns0 
      {| onwPackets := update2 f h x (f h x ++ [Aggregate m']); onwState := g |} =
    sum_fail_sent_incoming_active ns1 ns0 {| onwPackets := f; onwState := g |}.
Proof.
elim => //=.
move => n ns IH ns1 f h x m' g.
rewrite IH //.
by rewrite sum_fail_map_incoming_update2_app_eq.
Qed.

Lemma sum_fail_received_incoming_active_update2_app_eq :
  forall ns0 ns1 f h x m' g,
    (*~ In Fail (f h x) ->*)
    sum_fail_received_incoming_active ns1 ns0 
      {| onwPackets := update2 f h x (f h x ++ [Aggregate m']); onwState := g |} =
    sum_fail_received_incoming_active ns1 ns0 {| onwPackets := f; onwState := g |}.
Proof.
elim => //=.
move => n ns IH ns1 f h x m' g.
rewrite IH //.
by rewrite sum_fail_map_incoming_update2_app_eq.
Qed.

Lemma sum_sent_step_o_init : 
  forall ns, sum_sent ((Nodes_data ns) step_o_init) = 1.
Proof.
elim => //=.
move => n ns IH.
rewrite IH sumM_init_map_1.
by gsimpl.
Qed.

Lemma sum_received_step_o_init : 
  forall ns, sum_received ((Nodes_data ns) step_o_init) = 1.
Proof.
elim => //=.
move => n ns IH.
rewrite IH sumM_init_map_1.
by gsimpl.
Qed.

Lemma sum_fail_map_incoming_init : 
  forall ns1 ns0 n,
    sum_fail_map_incoming ns1 (fun _ _ : Name => []) n (adjacency n ns0) (init_map (adjacency n ns0)) = 1.
Proof.
elim => //=.
move => n ns IH ns0 n0.
rewrite IH.
rewrite /sum_fail_map.
case: andP => H_and; last by gsimpl.
move: H_and => [H_eq H_eq'].
by contradict H_eq.
Qed.

Lemma sum_fail_sent_incoming_active_step_o_init :
  forall ns0 ns1, sum_fail_sent_incoming_active ns1 ns0 step_o_init = 1.
Proof.
elim => //=.
move => n ns0 IH ns1.
rewrite IH sum_fail_map_incoming_init.
by gsimpl.
Qed.

Lemma sum_fail_received_incoming_active_step_o_init :
  forall ns0 ns1, sum_fail_received_incoming_active ns1 ns0 step_o_init = 1.
Proof.
elim => //=.
move => n ns0 IH ns1.
rewrite IH sum_fail_map_incoming_init.
by gsimpl.
Qed.

Lemma nodup_in_not_in_right : 
  forall ns0 ns1 (x : Name),
    NoDup (ns0 ++ ns1) -> In x ns0 -> ~ In x ns1.
Proof.
elim => //=.
move => n ns0 IH ns1 x H_nd H_in.
inversion H_nd => {l H0 x0 H}.
case: H_in => H_in; last exact: IH.
rewrite H_in in H1.
move => H_in'.
case: H1.
apply in_or_app.
by right.
Qed.

Lemma nodup_in_not_in_left : 
  forall ns0 ns1 (x : Name),
    NoDup (ns0 ++ ns1) -> In x ns1 -> ~ In x ns0.
Proof.
elim => [|n ns0 IH] ns1 x H_nd H_in //.
inversion H_nd => {l H0 x0 H}.
move => H_in'.
case: H_in' => H_in'.
  rewrite H_in' in H1.
  case: H1.
  apply in_or_app.
  by right.
contradict H_in'.
exact: (IH _ _ H2).
Qed.

Lemma nodup_app_split_left : 
  forall (ns0 ns1 : list Name), 
    NoDup (ns0 ++ ns1) -> NoDup ns0.
Proof.
elim => [|n ns0 IH] ns1 H_nd; first exact: NoDup_nil.
inversion H_nd => {l H0 x H}.
apply NoDup_cons.
  move => H_in.
  case: H1.
  apply in_or_app.
  by left.
move: H2.
exact: IH.
Qed.

Lemma nodup_app_split_right : 
  forall (ns0 ns1 : list Name), 
    NoDup (ns0 ++ ns1) -> NoDup ns1.
Proof.
elim => [|n ns0 IH] ns1 H_nd //.
inversion H_nd => {l H0 x H}.
exact: IH.
Qed.

Lemma sum_aggregate_msg_incoming_app_aggregate_eq :
  forall ns f h x m',
    In h ns ->
    NoDup ns ->
    ~ In Fail (f h x) ->
    sum_aggregate_msg_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) x =
    sum_aggregate_msg_incoming ns f x * m'.
Proof.
elim => //.
move => n ns IH f h x m' H_in H_nd H_in'.
inversion H_nd => {x0 H H0 l H_nd}.
case: H_in => H_in.
  rewrite H_in in H1.
  rewrite H_in {H_in n}.
  rewrite /=.
  rewrite sum_aggregate_msg_incoming_update2_eq //.
  case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
    case: H_dec'.
    move: H_dec.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in //.
    by case: H_in.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_and; last by case: H_and.
  rewrite sum_aggregate_msg_split /=.
  by gsimpl.
rewrite /= IH //.
have H_neq: h <> n by move => H_eq; rewrite H_eq in H_in.
case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
- by aac_reflexivity.
- case: H_dec'.
  move: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq H_eq'].
- case: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq H_eq'].
- rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_eq H_eq'].
  by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_in_update2_app_eq :
  forall ns0 ns1 f g x h d m',
    NoDup ns0 ->
    NoDup ns1 ->
    In x ns0 ->
    In h ns1 ->
    ~ In h ns0 ->
    ~ In Fail (f h x) ->
    sum_aggregate_msg_incoming_active ns1 ns0 {| onwPackets := update2 f h x (f h x ++ [Aggregate m']); onwState := update g h d |} = 
    sum_aggregate_msg_incoming_active ns1 ns0 {| onwPackets := f; onwState := g |} * m'.
Proof.
elim => //=.
move => n ns0 IH ns1 f g x h d m' H_nd H_nd' H_in H_inn H_in' H_f.
have H_neq: h <> n by move => H_neq; case: H_in'; left.
have H_nin: ~ In h ns0 by move => H_nin; case: H_in'; right.
move {H_in'}.
inversion H_nd => {l x0 H H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1 H_neq.
  rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
  rewrite sum_aggregate_msg_incoming_app_aggregate_eq //.
  by gsimpl.
have H_neq': n <> x by move => H_eq; rewrite -H_eq in H_in.
rewrite IH //.
rewrite sum_aggregate_msg_incoming_neq_eq //.
by aac_reflexivity.
Qed.

Lemma exclude_failed_not_in :
  forall ns h failed,
    ~ In h ns ->
    exclude (h :: failed) ns = exclude failed ns.
Proof.
elim => //.
move => n ns IH h failed H_in.
have H_neq: h <> n by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite /=.
case (Name_eq_dec _ _) => H_dec //.
case (in_dec _ _) => H_dec'; first exact: IH.
by rewrite IH.
Qed.

Lemma exclude_in_app : 
  forall ns ns0 ns1 h failed, 
  NoDup ns ->
  exclude failed ns = ns0 ++ h :: ns1 -> 
  exclude (h :: failed) ns = ns0 ++ ns1.
Proof.
elim; first by case.
move => n ns IH ns0 ns1 h failed H_nd.
inversion H_nd => {x H0 l H H_nd}.
rewrite /=.
case (in_dec _ _) => H_dec; case (Name_eq_dec _ _) => H_dec' H_eq.
- exact: IH.
- exact: IH.
- rewrite -H_dec' {n H_dec'} in H_eq H1 H_dec.
  case: ns0 H_eq.
    rewrite 2!app_nil_l.
    move => H_eq.
    inversion H_eq.
    by rewrite exclude_failed_not_in.
  move => x ns' H_eq.
  inversion H_eq => {H_eq}.
  rewrite H0 {h H0} in H1 H_dec.
  have H_in: In x (exclude failed ns).
    rewrite H3.
    apply in_or_app.
    by right; left.
  by apply exclude_in in H_in.
- case: ns0 H_eq.
    rewrite app_nil_l.
    move => H_eq.
    inversion H_eq.
    by rewrite H0 in H_dec'.
  move => n' ns0 H_eq.
  inversion H_eq.
  by rewrite (IH _ _ _ _ _ H3).
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  conserves_network_mass (exclude failed Nodes) Nodes onet.
Proof.
move => onet failed tr H_step.
rewrite /conserves_network_mass.
have H_cons := Aggregation_conserves_node_mass_all H_step.
apply global_conservation in H_cons.
rewrite /conserves_mass_globally in H_cons.
rewrite H_cons {H_cons}.
suff H_suff: sum_sent (Nodes_data (exclude failed Nodes) onet) * (sum_received (Nodes_data (exclude failed Nodes) onet))^-1 =
             sum_aggregate_msg_incoming_active Nodes (exclude failed Nodes) onet *
             sum_fail_sent_incoming_active Nodes (exclude failed Nodes) onet *
             (sum_fail_received_incoming_active Nodes (exclude failed Nodes) onet)^-1 by aac_rewrite H_suff; aac_reflexivity.
remember step_o_f_init as y in *.
have ->: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite {2 4 6 8 10}H_eq_o {H_eq_o}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init {H_init} /=.
  rewrite sum_aggregate_msg_incoming_all_step_o_init.
  rewrite sum_sent_step_o_init.
  rewrite sum_received_step_o_init.
  rewrite sum_fail_sent_incoming_active_step_o_init.
  rewrite sum_fail_received_incoming_active_step_o_init.
  by gsimpl.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H_step2}.
  have H_in_from : In from Nodes by exact: In_n_Nodes.
  rewrite /= in IHH_step1.
  have H_inn : In to (exclude failed0 Nodes).
    have H_inn := In_n_Nodes to.
    exact: In_n_exclude _ _ _ H1 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := nodup_exclude failed0 nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_to_nin: ~ In to ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In to ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2 5}/update.
  case (Name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq //.
  rewrite Nodes_data_not_in_eq //.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.  
  gsimpl.
  move => IH.  
  net_handler_cases => //=.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    rewrite sumM_add_map //.
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin').
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin').
    have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
    rewrite /update.
    case (Name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H5 H6 H7 {H3 H4 H5 H6 H7}.
    case (In_dec Msg_eq_dec Fail (net.(onwPackets) from to)) => H_in_fail.
      rewrite (sum_aggregate_msg_incoming_update2_fail_eq _ _ _ _ nodup _ H0) //.
      rewrite (sum_aggregate_msg_incoming_update2_aggregate_in_fail_add _ _ _ _ H_ins _ nodup _ H0) //.
      rewrite (sum_aggregate_msg_incoming_update2_aggregate_in_fail _ _ _ _ _ _ nodup H0) //.    
      gsimpl.
      by aac_reflexivity.
    rewrite (sum_aggregate_msg_incoming_update2_aggregate _ _ _ H_in_from nodup H_in_fail H0).
    rewrite (no_fail_sum_fail_map_incoming_eq _ _ _ _ _ (In_n_Nodes from) nodup H0 H_in_fail).
    rewrite (no_fail_sum_fail_map_incoming_add_eq _ _ _ _ _ _ (In_n_Nodes from) nodup H0 H_in_fail).
    by aac_reflexivity.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H_step1 _ H1 H_ins.
    by rewrite H_rcd in H.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_in': ~ In Fail ms.
      have H_le := Aggregation_le_one_fail H_step1 _ from H1.
      rewrite H0 /= in H_le.
      move: H_le.
      case H_cnt: (count_occ _ _ _) => H_le; last by omega.
      by apply count_occ_not_In in H_cnt.      
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    rewrite (sumM_remove_remove _ H_ins H).
    rewrite (sumM_remove_remove _ H_ins H3).
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin').
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ H_to_nin').
    have H_bef := Aggregation_in_after_all_fail_aggregate H_step1 _ H1 from.
    rewrite (sum_aggregate_msg_incoming_fail_update2_eq _ _ _ H_bef _ nodup) //.
    rewrite /update.
    case (Name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H6 H7 H8.
    rewrite (sum_fail_map_incoming_fail_remove_eq _ _ _ _ nodup H_ins _ H_in' H) //.
    rewrite (sum_fail_map_incoming_fail_remove_eq _ _ _ _ nodup H_ins _ H_in' H3) //.
    have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
    gsimpl.
    by aac_reflexivity.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    have [m5 H_snt] := Aggregation_in_set_exists_find_sent H_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H_step1 _ H1 H_ins.
    by rewrite H_rcd in H9.
- find_apply_lem_hyp input_handlers_IOHandler.
  move {H_step2}.
  have H_in_from : In h Nodes by exact: In_n_Nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (exclude failed0 Nodes).
    have H_inn := In_n_Nodes h.
    exact: In_n_exclude _ _ _ H0 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := nodup_exclude failed0 nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_h_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_h_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2 5}/update.
  case (Name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq_alt //.
  rewrite Nodes_data_not_in_eq_alt //.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.
  gsimpl.
  move => IH.
  io_handler_cases => //=.
  * rewrite 2!sum_aggregate_msg_incoming_active_not_in_eq_alt.
    rewrite sum_fail_sent_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_sent_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_received_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_received_incoming_active_not_in_eq_alt //.
    rewrite /update.
    case (Name_eq_dec _ _) => H_dec {H_dec} //.
    by rewrite H3 H4 H5.
  * have H_x_Nodes: In x Nodes by exact: In_n_Nodes.
    have H_neq: h <> x by move => H_eq; have H_self := Aggregation_node_not_adjacent_self H_step1 H0; rewrite {1}H_eq in H_self.
    rewrite (sumM_add_map _ _ H H3).
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_neq_eq //.
    rewrite {5 6 7 8}/update.
    case (Name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H6 H7 H8.
    set up2 := update2 _ _ _ _.
    set netu := {| onwPackets := _; onwState := _ |}.
    case (In_dec Name_eq_dec x failed0) => H_dec.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H0 H.
      case: H_or => H_or //.
      move: H_or => [H_dec' H_in] {H_dec'}.
      have H_x_ex: ~ In x (exclude failed0 Nodes) by exact: in_not_in_exclude.
      rewrite H_inn in H_x_ex.
      have H_x_nin: ~ In x ns0 by move => H_x_in; case: H_x_ex; apply in_or_app; left.
      have H_x_nin': ~ In x ns1 by move => H_x_in; case: H_x_ex; apply in_or_app; right; right.      
      rewrite sum_aggregate_msg_incoming_active_not_in_eq_alt2 //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_sent_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_sent_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_received_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_received_incoming_active_not_in_eq_alt2 //.
      rewrite (sum_fail_map_incoming_add_aggregate_eq _ _ _ _ _ nodup) //.
      rewrite sum_fail_map_incoming_update2_not_eq //.
      by aac_reflexivity.
    have H_in := Aggregation_not_failed_no_fail H_step1 _ x H0.
    have H_in' := Aggregation_not_failed_no_fail H_step1 _ h H_dec.
    rewrite (sum_fail_map_incoming_not_in_fail_add_update2_eq _ _ _ _ _ _ _ nodup) //.
    rewrite (sum_fail_map_incoming_not_in_fail_update2_eq _ _ _ _ _ H_neq).
    rewrite sum_fail_sent_incoming_active_update_not_in_eq //.
    rewrite sum_fail_sent_incoming_active_update_not_in_eq //.   
    rewrite sum_fail_received_incoming_active_update_not_in_eq //.
    rewrite sum_fail_received_incoming_active_update_not_in_eq //.
    rewrite sum_fail_sent_incoming_active_update2_app_eq //.
    rewrite sum_fail_sent_incoming_active_update2_app_eq //.
    rewrite sum_fail_received_incoming_active_update2_app_eq //.
    rewrite sum_fail_received_incoming_active_update2_app_eq //.    
    have H_in_x: In x (exclude failed0 Nodes) by exact: In_n_exclude.
    rewrite H_inn in H_in_x.
    apply in_app_or in H_in_x.
    case: H_in_x => H_in_x.
      have H_nin_x: ~ In x ns1.
        move => H_nin_x.
        apply NoDup_remove_1 in H_nd.
        contradict H_nin_x.
        move: H_in_x.
        exact: nodup_in_not_in_right.
      have H_nd': NoDup ns0 by move: H_nd; exact: nodup_app_split_left.
      rewrite (sum_aggregate_msg_incoming_active_not_in_eq_alt2 ns1) //.
      rewrite (sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ _ _ nodup) //.
      have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
      by aac_reflexivity.
    case: H_in_x => H_in_x //.
    have H_nin_x: ~ In x ns0.
      move => H_nin_x.
      apply NoDup_remove_1 in H_nd.
      contradict H_nin_x.
      move: H_in_x.
      exact: nodup_in_not_in_left.
    have H_nd': NoDup ns1.
      apply nodup_app_split_right in H_nd.
      by inversion H_nd.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq_alt2 //.
    rewrite (sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ _ _ nodup) //.
    have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
    by aac_reflexivity.
  * have [m' H_snt] := Aggregation_in_set_exists_find_sent H_step1 _ H0 H.
    by rewrite H_snt in H3.
  * rewrite update_nop.
    rewrite update_nop_ext.
    by have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
  * rewrite update_nop.
    rewrite update_nop_ext.
    by have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
  * rewrite update_nop.
    rewrite update_nop_ext.
    by have ->: {| onwPackets := onwPackets net; onwState := onwState net |} = net by destruct net.
- move {H_step2}.
  have H_in_from : In h Nodes by exact: In_n_Nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (exclude failed0 Nodes).
    have H_inn := In_n_Nodes h.
    exact: In_n_exclude _ _ _ H0 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  have H_nd := nodup_exclude failed0 nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_to_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite (exclude_in_app ns0 ns1 _ _ nodup) //.
  rewrite H_inn.
  have H_nd': NoDup ns0 by move: H_nd; exact: nodup_app_split_left.
  have H_nd'': NoDup ns1 by apply nodup_app_split_right in H_nd; inversion H_nd.
  rewrite 2!Nodes_data_split /=.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.
  gsimpl.
  move => IH {H_inn H_nin}.
  set l := collate _ _ _.
  have ->: Nodes_data ns0 {| onwPackets := l; onwState := onwState net |} = Nodes_data ns0 net by [].
  have ->: Nodes_data ns1 {| onwPackets := l; onwState := onwState net |} = Nodes_data ns1 net by [].
Admitted.



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
