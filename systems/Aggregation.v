Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import OrderedTypeEx.
Require Import FMapList.
Module IMap <: FMapInterface.S := FMapList.Make Nat_as_OT.

(*
Require Import Orders.
Require Import NPeano.
Require Import MSetList.
Module ISet <: MSetInterface.S := MSetList.Make Nat.
*)

Require Import ssreflect.

Set Implicit Arguments.

Open Scope Z_scope.

Section Aggregation.

  Variable num_sources : nat.

  Definition Mass := Z.

  Definition source_index := (fin num_sources).

  Inductive Name :=
  | Source : source_index -> Name.

  Definition list_sources := map Source (all_fin num_sources).

  Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
    decide equality.
    by apply fin_eq_dec.
  Defined.

  Inductive Msg := 
   | Aggregate : Mass -> Msg.

  Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
    decide equality.
    by apply Z_eq_dec.
  Defined.

  Inductive Input :=
   | Local : Mass -> Input
   | Send : Name -> Input
   | Query : Input.

  Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
    decide equality.
    - by apply Z_eq_dec.
    - by apply Name_eq_dec.
  Defined.

  Inductive Output :=
    | Response : Mass -> Output.

  Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
    decide equality.
    by apply Z_eq_dec.
  Defined.
 
  Record Data := mkData { local : Z ; aggregate : Z }.

  Definition init_Data (n : Name) := mkData 0 0.

  Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

  Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
    match msg with
    | Aggregate m => 
      st <- get ;;
      let new_aggregate := st.(aggregate) + m in
      put (mkData st.(local) new_aggregate) 
    end.

  Definition IOHandler (me : Name) (i : Input) : Handler Data :=
  match i with
  | Local m => 
    st <- get ;;
    let new_local := m in
    let new_aggregate := (st.(aggregate) + m - st.(local)) in
    put (mkData new_local new_aggregate)
  | Send n => 
    st <- get ;;
    when 
    (Zneq_bool st.(aggregate) 0)
    (put (mkData st.(local) 0) >> (send (n, (Aggregate st.(aggregate)))))
  | Query =>
    st <- get ;;
    write_output (Response st.(aggregate))
  end.

  Definition Nodes := list_sources.

  Theorem In_n_Nodes :
    forall n : Name, In n Nodes.
  Proof.
    intros.
    unfold Nodes, list_sources.
    simpl.
    destruct n.
    apply in_map.
    by apply all_fin_all.
  Qed.

  Theorem nodup :
    NoDup Nodes.
  Proof.
    unfold Nodes, list_sources.
    apply NoDup_map_injective.
      + intros. congruence.
      + apply all_fin_NoDup.
  Qed.

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

  Check net_handlers.

  Lemma net_handlers_NetHandler :
    forall dst src m d os d' ms,
      net_handlers dst src m d = (os, d', ms) ->
      NetHandler dst src m d = (tt, os, d', ms).
  Proof.
    intros.
    simpl in *.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct u. auto.
  Qed.

  (* Definition conserves_node_mass (nodes : list node) : Prop := forall (n : node), In n nodes -> 
    n.(local) = n.(aggregate) + (sum_mass n.(adjacent) n.(sent)) - (sum_mass n.(adjacent) n.(received)) *)

  (* Definition conserves_mass_globally (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) + (sum_sent nodes) - (sum_received nodes). *)

  (* Definition conserves_network_mass (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) + (sum_aggregate_queues nodes) + (sum_sent_fail_queues nodes) - 
     (sum_received_fail_queues nodes). *)

  Definition trprop (trace : list (name * (input + list output))) : Prop :=
    True.

  Lemma cross_relation :
    forall (P : network -> list (name * (input + list output)) -> Prop),
      P step_m_init [] ->
      (forall st st' tr ev,
         step_m_star step_m_init st tr ->
         P st tr ->
         step_m st st' ev ->
         P st' (tr ++ ev)) ->
      forall st tr,
        step_m_star step_m_init st tr ->
        P st tr.
Proof.
    intros.
    find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H1.
    induction H1; intros; subst; eauto.
    eapply H3; eauto.
    - apply refl_trans_n1_1n_trace. auto.
    - apply IHrefl_trans_n1_trace; auto.
  Qed.

  Lemma Aggregation_mutual_exclusion_trace :
    forall st tr,
      step_m_star step_m_init st tr ->
      trprop tr.
  Proof.
  apply cross_relation; intros.
  - by [].
  - case: H1.
    intros.
    rewrite /= /NetHandler in e0.
    move: e0 e1 e.
    case: p => pDst pSrc.
    case => m.
    rewrite /=.
    monad_unfold.
    rewrite /=.
    move => H_eq.
    injection H_eq.
Admitted.


End Aggregation.
