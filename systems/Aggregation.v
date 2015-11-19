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

Require Import ssreflect.

Set Implicit Arguments.

Open Scope Z_scope.

Module Aggregation (N : NatValue) <: NatValue.

  Definition n := N.n.
 
  Definition num_sources := N.n.  

  Require Import OrderedTypeEx.
  Require Import FMapList.
  Module fin_n_compat_OT := fin_OT_compat N.
  Module FinNMap <: FMapInterface.S := FMapList.Make fin_n_compat_OT.
  
  Require Import Orders.
  Require Import MSetList.
  Module fin_n_OT := fin_OT N.
  Module FinNSet <: MSetInterface.S := MSetList.Make fin_n_OT.

  Require Import MSetFacts.
  Module FinNSetFacts := Facts FinNSet.

  Require Import MSetProperties.
  Module FinNSetProps := Properties FinNSet.
  Module FinNSetOrdProps := OrdProperties FinNSet.
  Require Import FMapFacts.
  Module FinNMapFacts := Facts FinNMap.
  
  Definition m := Z.

  Definition m_neq_bool := Zneq_bool.

  Definition Name := (fin num_sources).

  Definition list_sources := (all_fin num_sources).

  Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
  exact: fin_eq_dec.
  Defined.

  Definition Name_neq_bool (x y : Name) : bool :=
  match Name_eq_dec x y with
  | left _ => false
  | right _ => true
  end.

  Lemma Name_neq_bool_true_neq : forall (x y : Name),
    Name_neq_bool x y = true -> x <> y.
  Proof.
  move => x y.
  rewrite /Name_neq_bool.
  by case (Name_eq_dec _ _).
  Qed.

  Lemma Name_neq_bool_neq_true : forall (x y : Name),
    x <> y -> Name_neq_bool x y = true.
  Proof.
  move => x y.
  rewrite /Name_neq_bool.
  by case (Name_eq_dec _ _).
  Qed.

  Inductive Msg := 
   | Aggregate : m -> Msg.

  Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
    decide equality.
    by apply Z_eq_dec.
  Defined.

  Inductive Input :=
   | Local : m -> Input
   | Send : Name -> Input
   | Query : Input.

  Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
    decide equality.
    - by apply Z_eq_dec.
    - by apply Name_eq_dec.
  Defined.

  Inductive Output :=
    | Response : m -> Output.

  Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
    decide equality.
    by apply Z_eq_dec.
  Defined.

  Record Data := mkData { local : m ; aggregate : m ; adjacent : FinNSet.t ; sent : FinNMap.t m ; received : FinNMap.t m }.

  Definition init_Data (n : Name) := mkData 0 0 FinNSet.empty (FinNMap.empty m) (FinNMap.empty m).

  Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

  Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
    match msg with
    | Aggregate m_msg => 
      st <- get ;;
      let new_aggregate := st.(aggregate) + m_msg in
      let new_received := 
        match FinNMap.find src st.(received) with
        | Some m_src => FinNMap.add src (m_src + m_msg) st.(received)
        | None => FinNMap.add src m_msg st.(received)
        end in
      put (mkData st.(local) new_aggregate st.(adjacent) st.(sent) new_received)
    end.

  Definition IOHandler (me : Name) (i : Input) : Handler Data :=
  match i with
  | Local m_msg => 
    st <- get ;;
    let new_local := m_msg in
    let new_aggregate := st.(aggregate) + m_msg - st.(local) in
    put (mkData new_local new_aggregate st.(adjacent) st.(sent) st.(received))
  | Send dst => 
    st <- get ;;
    when 
    (m_neq_bool st.(aggregate) 0 && Name_neq_bool me dst)
    (let new_aggregate := 0 in
     let new_sent := 
       match FinNMap.find dst st.(sent) with
       | Some m_dst => FinNMap.add dst (m_dst + st.(aggregate)) st.(sent)
       | None => FinNMap.add dst st.(aggregate) st.(sent)
       end in
     put (mkData st.(local) new_aggregate st.(adjacent) new_sent st.(received)) >> (send (dst, (Aggregate st.(aggregate)))))
  | Query =>
    st <- get ;;
    write_output (Response st.(aggregate))
  end.

  Definition Nodes := list_sources.

  Theorem In_n_Nodes :
    forall n : Name, In n Nodes.
  Proof.
    exact: all_fin_all.
  Qed.

  Theorem nodup :
    NoDup Nodes.
  Proof.
    exact: all_fin_NoDup.
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


  Definition fold_sum := fun (key : Name) val sum => sum + val.
  
  Definition sum_mass (map : FinNMap.t m) : m := 
  FinNMap.fold fold_sum map 0.

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

Lemma sum_mass_add_Some : forall (n : Name) (map : FinNMap.t m) (m5 m' : m),
  FinNMap.find n map = Some m5 ->
  sum_mass (FinNMap.add n (m5 + m') map) = sum_mass map + m'.
Proof.
move => n map m5 m'.
rewrite /sum_mass.
rewrite (FinNMap.fold_1 map _ fold_sum).
rewrite (FinNMap.fold_1 _ _ fold_sum).
move => H_find.
apply FinNMap.find_2 in H_find.
have H_el := FinNMap.elements_1 H_find.
have H_add := FinNMap.add_3.
elim (FinNMap.elements map) => [|e map' IH].
Admitted.

Lemma sum_mass_add_None : forall (n : Name) (map : FinNMap.t m) (m' : m),
  FinNMap.find n map = None ->
  sum_mass (FinNMap.add n m' map) = sum_mass map + m'.
Proof.
Admitted.

Lemma conserves_node_mass : 
forall net tr n, 
 step_m_star (params := Aggregation_MultiParams) step_m_init net tr ->
 (nwState net n).(local) = (nwState net n).(aggregate) + 
   (sum_mass (nwState net n).(sent)) - (sum_mass (nwState net n).(received)).
Proof.
move => net tr n H.
remember step_m_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_m _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  destruct (pBody p).
  rewrite /= in H3.
  monad_unfold.
  rewrite /= in H3.
  injection H3.
  move => H_l H_st H_out.
  rewrite -H_st /=.
  rewrite /update.
  case (name_eq_dec _ _) => H_eq //.
  rewrite /= -H_eq {H_eq}.
  case H_find: (FinNMap.find _ _) => [m'|].
    rewrite IHrefl_trans_1n_trace1 /=.
    rewrite (sum_mass_add_Some _ _ _ H_find).
    by ring_simplify.
  rewrite IHrefl_trans_1n_trace1 /=.
  rewrite (sum_mass_add_None _ _ _ H_find).
  by ring_simplify.
apply input_handlers_IOHandler in H2.
destruct inp.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq //.
  rewrite /= -H_eq {H_eq}.
  rewrite IHrefl_trans_1n_trace1 /=.
  symmetry.
  by ring_simplify.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  move: H2.
  case H_m_neq: (m_neq_bool _); case H_n_neq: (Name_neq_bool _ _) => //= H2; injection H2 => H_l H_st H_o.
  * rewrite -H_st /update /= {H_st H2}.
    case (Name_eq_dec _) => H_eq //=.
    rewrite -H_eq {H_eq}.
    case H_find: (FinNMap.find _ _) => [m'|].
      rewrite IHrefl_trans_1n_trace1 /=.
      rewrite (sum_mass_add_Some _ _ _ H_find).
      by ring_simplify.
    rewrite IHrefl_trans_1n_trace1 /=.
    rewrite (sum_mass_add_None _ _ _ H_find).
    by ring_simplify.          
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq //.
  by rewrite -H_eq.
Qed.

  (* Definition conserves_mass_globally (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) + (sum_sent nodes) - (sum_received nodes). *)

  (* Definition conserves_network_mass (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) + (sum_aggregate_queues nodes) + (sum_sent_fail_queues nodes) - 
     (sum_received_fail_queues nodes). *)

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
