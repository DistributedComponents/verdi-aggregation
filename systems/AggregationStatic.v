(* at recovery time, send new to all existing neighbors, handle problem with unprocessed fail messages for recovery *)
(* higher-level language like ott/lem for protocols that exports to handlers? *)
(* must use v8.5 branch of https://github.com/coq-contribs/aac-tactics *)
Require Import Verdi.
Require Import HandlerMonad.
Require Import NameOverlay.

Require Import TotalMapSimulations.
Require Import PartialMapSimulations.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import Sorting.Permutation.

Require Import AAC_tactics.AAC.

Require Import OrderedLemmas.
Require Import AggregationDefinitions.
Require Import AggregatorStatic.
Require Import FailureRecorderStatic.

Set Implicit Arguments.

Module Aggregation (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import CFG : CommutativeFinGroup) (Import ANT : AdjacentNameType NT).

Module OA := SingleAggregator NT NOT NSet NOTC NMap CFG ANT.

(* FIXME *)
Import OA.A.
Import OA.AX.AD.
Import OA.AX.

Module FR := FailureRecorder NT NOT NSet ANT.

Import GroupScope.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Inductive Msg : Type := 
| Aggregate : m -> Msg
| Fail : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Input : Type :=
| Local : m -> Input
| SendAggregate : name -> Input
| AggregateRequest : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: name_eq_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data := mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : NS ; 
  balance : NM
}.

Definition InitData (n : name) := 
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     balance := init_map (adjacency n nodes) |}.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match NMap.find src st.(balance) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_msg)^-1) st.(balance) |}
  end
| Fail => 
  match NMap.find src st.(balance) with
  | Some m_bal =>    
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_bal ;
           adjacent := NSet.remove src st.(adjacent) ;
           balance := NMap.remove src st.(balance) |}
  | None => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := NSet.remove src st.(adjacent) ;
           balance := st.(balance) |}
  end
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg ;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1 ;
         adjacent := st.(adjacent) ;
         balance := st.(balance) |}
| AggregateRequest =>
  write_output (AggregateResponse st.(aggregate))
| SendAggregate dst => 
  when (NSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match NMap.find dst st.(balance) with
   | None => nop
   | Some m_dst =>        
     put {| local := st.(local) ;
            aggregate := 1 ;
            adjacent := st.(adjacent) ;
            balance := NMap.add dst (m_dst * st.(aggregate)) st.(balance) |} ;; 
     send (dst, (Aggregate st.(aggregate)))
   end)
end.

Instance Aggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Aggregation_MultiParams : MultiParams Aggregation_BaseParams :=
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

Instance Aggregation_NameOverlayParams : NameOverlayParams Aggregation_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance Aggregation_FailMsgParams : FailMsgParams Aggregation_MultiParams :=
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
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = st.(balance) /\
         out = [] /\ ms = []) \/
      (exists dst m_bal, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(balance) = Some m_bal /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = NMap.add dst (m_bal * st.(aggregate)) st.(balance) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(balance) = None /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) = 1 /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ ~ NSet.In dst st.(adjacent) /\ 
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
- case H_mem: (NSet.mem _ _); case (m_eq_dec _ _) => H_dec; rewrite /sumbool_not //=.
  * apply NSetFacts.mem_2 in H_mem.
    move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left; exists dst.
  * apply NSetFacts.mem_2 in H_mem.
    case H_find: (NMap.find _ _) => [m'|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    + by right; left; exists dst; exists m'.
    + by right; right; left; exists dst.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply NSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply NSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
- move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
  by right; right; right; right; right.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ NMap.find src st.(balance) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = NMap.add src (m_src * (m_msg^-1)) st.(balance) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ NMap.find src st.(balance) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_bal, msg = Fail /\ NMap.find src st.(balance) = Some m_bal /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (NMap.find src st.(balance) = None) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg|]; monad_unfold; repeat break_let.
- break_match; repeat find_injection.
  * by left; exists m_msg, a.
  * by right; left; exists m_msg.
- break_match; repeat find_injection.
  * by right; right; left; exists a.
  * by right; right; right.
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

Instance Aggregation_FailureRecorder_base_params_pt_map : BaseParamsPartialMap Aggregation_BaseParams FR.FailureRecorder_BaseParams :=
  {
    pt_map_data := fun d => FR.mkData d.(adjacent) ;
    pt_map_input := fun _ => None ;
    pt_map_output := fun _ => None
  }.

Instance Aggregation_FailureRecorder_name_tot_map : MultiParamsNameTotalMap Aggregation_MultiParams FR.FailureRecorder_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance Aggregation_FailureRecorder_name_tot_map_bijective : MultiParamsNameTotalMapBijective Aggregation_FailureRecorder_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance Aggregation_FailureRecorder_multi_params_pt_map : MultiParamsMsgPartialMap Aggregation_MultiParams FR.FailureRecorder_MultiParams :=
  {
    pt_map_msg := fun m => match m with Fail => Some FR.Fail | _ => None end ;
  }.

Instance Aggregation_FailureRecorder_multi_params_pt_map_congruency : MultiParamsPartialMapCongruency Aggregation_FailureRecorder_base_params_pt_map Aggregation_FailureRecorder_name_tot_map Aggregation_FailureRecorder_multi_params_pt_map :=
  {
    pt_init_handlers_eq := fun _ => Logic.eq_refl ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
Proof.
- move => me src mg st mg' H_eq.
  rewrite /pt_mapped_net_handlers.
  repeat break_let.
  case H_n: net_handlers => [[out st'] ps].
  rewrite /= /runGenHandler_ignore /= in Heqp H_n.
  repeat break_let.
  repeat tuple_inversion.
  unfold id in *.  
  destruct u, u0, st'.
  by net_handler_cases; FR.net_handler_cases; simpl in *; congruence.
- move => me src mg st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct u, st'.
  by net_handler_cases; simpl in *; congruence.
- move => me inp st inp' H_eq.
  rewrite /pt_mapped_input_handlers.
  repeat break_let.
  case H_i: input_handlers => [[out st'] ps].
  rewrite /= /runGenHandler_ignore /= in Heqp H_i.
  repeat break_let.
  repeat tuple_inversion.
  destruct u.
  by io_handler_cases.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  repeat break_let.  
  repeat tuple_inversion.
  destruct u, st'.
  by io_handler_cases; simpl in *; congruence.
Qed.

Instance Aggregation_FailureRecorder_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency Aggregation_FailMsgParams FR.FailureRecorder_FailMsgParams Aggregation_FailureRecorder_multi_params_pt_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance Aggregation_FailureRecorder_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency Aggregation_NameOverlayParams FR.FailureRecorder_NameOverlayParams Aggregation_FailureRecorder_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem Aggregation_Failed_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_o_f_star _ _ _ Aggregation_FailMsgParams step_o_f_init (failed, net) tr ->
    @step_o_f_star _ _ _ FR.FailureRecorder_FailMsgParams step_o_f_init (failed, pt_map_onet net) (pt_map_traces tr).
Proof.
move => onet failed tr H_st.
apply step_o_f_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Instance Aggregation_Aggregator_multi_single_map : MultiSingleNodeParamsTotalMap Aggregation_MultiParams OA.Aggregator_BaseParams := 
  {
    tot_s_map_data := fun d => OA.mkData d.(local) d.(aggregate) d.(adjacent) d.(balance) ;
    tot_s_map_input := fun n i => 
                        match i with
                        | Local m_inp => OA.Local m_inp
                        | AggregateRequest => OA.AggregateRequest
                        | SendAggregate dst => OA.SendAggregate dst
                        end ;
    tot_s_map_output := fun o =>
                         match o with 
                         | AggregateResponse m_out => OA.AggregateResponse m_out
                         end ;
    tot_s_map_msg := fun dst src m =>
                        match m with
                        | Fail => OA.Fail src
                        | Aggregate m_msg => OA.Aggregate src m_msg
                        end
  }.

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr n, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 ~ In n failed ->
 ~ NSet.In n (onwState net n).(adjacent).
Proof.
move => onet failed tr n H_st H_in_f.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: FR.Failure_node_not_adjacent_self H_st' H_in_f.
Qed.

Lemma Aggregation_not_failed_no_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_not_failed_no_fail H_st' n n' H_in_f.
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
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact (FR.Failure_in_adj_adjacent_to H_st' n H_in_f H_ins).
Qed.

Lemma Aggregation_pt_map_msg_injective : 
  forall m0 m1 m2 : msg,
   pt_map_msg m0 = Some m2 -> pt_map_msg m1 = Some m2 -> m0 = m1.
Proof.
by case => [m0|]; case => [m1|] H_eq.
Qed.

Lemma Aggregation_in_adj_or_incoming_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_adj_or_incoming_fail H_st' _ H_in_f H_ins.
case: H_inv' => H_inv'; first by left.
right.
move: H_inv' => [H_in_f' H_inv'].
split => //.
move: H_inv'.
apply: in_pt_map_msgs_in_msg; last exact: pt_fail_msg_fst_snd.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_le_one_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_le_one_fail H_st' _ n' H_in_f.
rewrite /= /id /= in H_inv'.
move: H_inv'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite -H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_pt_map_msgs_eq => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_adjacent_to_in_adj :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_in_f' H_adj.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: (FR.Failure_adjacent_to_in_adj H_st' H_in_f H_in_f' H_adj).
Qed.

Lemma Aggregation_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_ins.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_queue_fail_then_adjacent H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_ins.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_first_fail_in_adj : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_first_fail_in_adj H_st' _ n' H_in_f.
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
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Aggregation_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

Lemma Aggregation_in_set_exists_find_balance : 
forall net failed tr, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 forall n, ~ In n failed ->
 forall n', NSet.In n' (net.(onwState) n).(adjacent) -> 
       exists m5 : m, NMap.find n' (net.(onwState) n).(balance) = Some m5.
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
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 balance0.
    move => H7 H8 H9 H10.
    rewrite H9 H10.
    move => H_ins.
    case (name_eq_dec n' from) => H_dec'.
      rewrite H_dec'.
      exists (x0 * x^-1).
      exact: NMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H4 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H5 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 balance0.
    move => H7 H8 H9 H10.
    rewrite H9 H10.
    move => H_ins.
    have H_neq': n' <> from.
      move => H_eq.
      rewrite H_eq in H_ins.
      by apply NSetFacts.remove_1 in H_ins.
    apply NSetFacts.remove_3 in H_ins.
    rewrite /= in IHrefl_trans_1n_trace1.
    have [m5 IH'] := IHrefl_trans_1n_trace1 _ H3 _ H_ins.
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H12 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 => /= local0 aggregate0 adjacent0 balance0.
    move => H5 H6 H7 H8.
    rewrite H7 H8.
    move => H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H6 H7 H8 => /= local0 aggregate0 adjacent0 balance0.
    move => H6 H7 H8.
    rewrite H7 H8 /=.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 balance0.
    move => H8 H9 H10 H11.
    rewrite H10 H11.
    move => H_ins.
    case (name_eq_dec n' x) => H_dec'.
      rewrite H_dec'.
      exists (x0 * aggregate (onwState net h)).
      exact: NMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H7 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
- move => n H_in n' H_ins.
  have H_neq: ~ In n failed by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Section SingleNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variable n : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_aggregate : 
  forall onet failed tr n' m' m0,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NMap.find n' (onet.(onwState) n).(balance) = Some m0 ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (NMap.add n' (m0 * (m')^-1) (onet.(onwState) n).(balance))).

Hypothesis recv_fail : 
  forall onet failed tr n' m_bal,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NMap.find n' (onet.(onwState) n).(balance) = Some m_bal ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m_bal) (NSet.remove n' (onet.(onwState) n).(adjacent)) (NMap.remove n' (onet.(onwState) n).(balance))).

Hypothesis recv_local_weight : 
  forall onet failed tr m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  P (onet.(onwState) n) ->
  P (mkData m' ((onwState onet n).(aggregate) * m' * ((onwState onet n).(local))^-1) (onwState onet n).(adjacent) (onwState onet n).(balance)).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n' m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NSet.In n' (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    NMap.find n' (onwState onet n).(balance) = Some m' ->
    P (onet.(onwState) n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add n' (m' * (onwState onet n).(aggregate)) (onwState onet n).(balance))).

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
  case name_eq_dec => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2 to} in H0, H1, H2.
  net_handler_cases => //.
  * case: d H4 H5 H6 H7 => /=.
    move => local0 aggregate0 adjacent0 balance0.
    move => H4 H5 H6 H7.
    rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
    exact: (recv_aggregate _ H'_step1).
  * case: d H4 H5 H6 H7 => /=.
    move => local0 aggregate0 adjacent0 balance0.
    move => H4 H6 H7 H8.
    rewrite H4 H6 H7 H8 {local0 aggregate0 adjacent0 balance0 H4 H6 H7 H8}.
    exact: (recv_fail H'_step1).
  * case (In_dec name_eq_dec from failed) => H_in; first last.
      have H_fail := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      case: H_fail.
      rewrite H0.
      by left.
    have H_in': In Fail (onwPackets net from n) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ from H1 H_in'.
    have [m5 H_bal] := Aggregation_in_set_exists_find_balance H'_step1 _ H1 H_ins.
    by rewrite H_bal in H.
- move => H_in_f.
  find_apply_lem_hyp input_handlers_IOHandler.
  rewrite /update /=.
  case name_eq_dec => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2} in H0 H1.
  io_handler_cases => //.
  * case: d H3 H4 H5 => /=.
    move => local0 aggregate0 adjacent0 balance0.
    move => H3 H4 H5.
    rewrite H3 H4 H5 {aggregate0 adjacent0 balance0 H3 H4 H5}.
    exact: (recv_local_weight _ H'_step1).
  * case: d H5 H6 H7 H8 => /=.
    move => local0 aggregate0 adjacent0 balance0.
    move => H5 H6 H7 H8.
    rewrite H5 H6 H7 H8 {local0 aggregate0 adjacent0 balance0 H5 H6 H7 H8}.
    exact: (recv_send_aggregate H'_step1).
- move => H_in_f.
  apply: IHH'_step1.
  move => H'_in_f.
  case: H_in_f.
  by right.
Qed.

End SingleNodeInv.

Definition self_channel_empty (n : name) (onet : ordered_network) : Prop :=
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
 forall (n : name), ~ In n failed ->
 forall (n' : name) m', before_all (Aggregate m') Fail (onet.(onwPackets) n' n).
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
    exact: before_all_not_in.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H1 H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; last by move: IH' => [H_neq H_bef].
    exact: before_all_not_in.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H1 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: before_all_not_in.
    by move: IH' => [H_neq H_bef].
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H9 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: before_all_not_in.
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
    apply: before_all_not_in_append.
    exact: Aggregation_not_failed_no_fail H _ _ H2.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
- move {H1} => n0 H_in_f n' m'.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  move {H_in_f}.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec in H_neq H2.
  rewrite H_dec {H_dec h}.
  case (adjacent_to_dec n' n0) => H_dec; last first.
    rewrite collate_map2snd_not_related //.
    exact: IHrefl_trans_1n_trace1.
  rewrite collate_map2snd_not_in_related //.
  * apply: before_all_neq_append => //.
    exact: IHrefl_trans_1n_trace1.
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
  forall onet failed tr, 
    step_o_f_star step_o_f_init (failed, onet) tr ->
    forall n, ~ In n failed ->
     forall n' m5, In (Aggregate m5) (onet.(onwPackets) n' n) ->
     NSet.In n' (onet.(onwState) n).(adjacent).
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
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      case: d H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 balance0.
      move => H6 H7 H8 H9.
      rewrite H8 -H_dec'.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + case: d H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 balance0.
      move => H6 H7 H8 H9.
      rewrite H8 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * rewrite /= in IHrefl_trans_1n_trace1.
    move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      rewrite H_eq'.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + rewrite -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
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
      case: d H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 balance0.
      move => H6 H8 H9 H10.
      rewrite H9.
      move => H_ins.
      apply NSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H11.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H9 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H4 H5 H6 H7 => /= local0 aggregate0 adjacent0 balance0.
      move => H4 H5 H6 H7.
      rewrite H6.
      move => H_ins.
      apply NSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
- move {H1}. 
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * move: H3.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    move => H_in.
    case: d H6 H7 H5 => /= local0 aggregate0 adjacent0 balance0.
    move => H6 H7 H8.
    rewrite H6 -H_dec.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update2 /update.
    case sumbool_and => H_dec; case name_eq_dec => H_dec'.
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
      apply adjacent_to_symmetric in H_adj.
      by have H_adj' := Aggregation_adjacent_to_in_adj H H0 H2 H_adj.
    + case: d H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 balance0.
      move => H7 H8 H9 H10.
      rewrite H9 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H6.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
- move => n0 H_in_f n' m5 H_in {H1}.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  case (name_eq_dec h n') => H_dec; last first.
    move: H_in.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec {h H_dec H_in_f} in H_in H_neq H2.
  case (adjacent_to_dec n' n0) => H_dec; last first.
    move: H_in.
    rewrite collate_map2snd_not_related //.
    exact: IHrefl_trans_1n_trace1.
  move: H_in.
  rewrite collate_map2snd_not_in_related //.
  * move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in; last by case: H_in => H_in.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

Section SingleNodeInvOut.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_aggregate_neq_from :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n ->
  NMap.find from (onwState onet n).(balance) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (NMap.add from (m0 * (m')^-1) (onet.(onwState) n).(balance))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  from <> n ->
  NMap.find from (onwState onet n).(balance) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (NMap.add from (m0 * (m')^-1) (onet.(onwState) n).(balance))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq_other_some :
  forall onet failed tr m' m0 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    NMap.find n ((onet.(onwState) n').(balance)) = Some m0 ->
    onet.(onwPackets) n n' = Aggregate m' :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (onet.(onwState) n) ms.

Hypothesis recv_fail_neq_from :
  forall onet failed tr from m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  from <> n ->
  NMap.find from (onwState onet n).(balance) = Some m0 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(balance))) (onet.(onwPackets) n n').

Hypothesis recv_fail_neq :
  forall onet failed tr from m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  n <> n' ->
  from <> n ->
  NMap.find from (onwState onet n).(balance) = Some m0 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(balance))) (onet.(onwPackets) n n').

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(balance)) (onet.(onwPackets) n n').

Hypothesis recv_local_eq_some :
  forall onet failed tr m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      n <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      NSet.In n' (onet.(onwState) n).(adjacent) ->
      NMap.find n' (onet.(onwState) n).(balance) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (NMap.add n' (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(balance))) (onet.(onwPackets) n n' ++ [Aggregate (onet.(onwState) n).(aggregate)]).

Hypothesis recv_local_neq_some :
  forall onet failed tr to m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      to <> n ->
      to <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      NSet.In to (onet.(onwState) n).(adjacent) ->
      NMap.find to (onet.(onwState) n).(balance) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (NMap.add to (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(balance))) (onet.(onwPackets) n n').

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
    case name_eq_dec => H_dec.
      rewrite -H_dec in H H2 H4 H5 H6 H7 H0 H1.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H6 H0 H7.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec.
        case: d H4 H5 H6 H7 => /=.
        move => local0 aggregate0 adjacent0 balance0.
        move => H4 H5 H6 H7.
        rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
        exact: (recv_aggregate_neq_from H'_step1 _ H_dec H H0).
      case: d H4 H5 H6 H7 => /=.
      move => local0 aggregate0 adjacent0 balance0.
      move => H4 H5 H6 H7.
      rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
      case (name_eq_dec from n) => H_dec'.
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1 _ H1) in H0.
      exact: (recv_aggregate_neq H'_step1 H1 H_dec H_dec' H H0).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' in H_dec.
    rewrite H_dec' {from H_dec' H'_step2} in H H0 H7.
    rewrite H_dec'' {H_dec'' to} in H H1 H2 H4 H5 H6 H7 H0.
    exact: (recv_aggregate_neq_other_some H'_step1 _ H_dec H H0).
  * rewrite /update.
    case (name_eq_dec _ _) => H_dec.
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
    have [m5 H_snt] := Aggregation_in_set_exists_find_balance H'_step1 _ H1 H_ins.
    by rewrite H_snt in H2.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H4 H5 H6 H7.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      move {H'_step2 H_dec H1}.
      case: d H4 H5 H6 H7 => /=.
      move => local0 aggregate0 adjacent0 balance0.
      move => H4 H5 H6 H7.
      rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
      case: H_dec' => H_dec'.
        case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_neq_from H'_step1 H_in_f H_in H_dec' H H0 H2).
        have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
        rewrite H0 in H_inl.
        by case: H_inl; left.
      case (name_eq_dec from n) => H_neq; first by rewrite H_neq (Aggregation_self_channel_empty H'_step1) in H0.
      case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_neq H'_step1 _ _ H_dec' _ _ H0 H2).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H H4 H5 H6 H7 H0.
    rewrite H_eq' in H_dec.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H5.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      rewrite -H_dec in H6.
      have H_in: In Fail (onwPackets net from n) by rewrite H0; left.
      have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H_in_f H_in.
      have [m' H_bal] := Aggregation_in_set_exists_find_balance H'_step1 _ H_in_f H_ins.
      by rewrite H_bal in H.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H_dec H1 H0.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.   
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec H'_step2} in H3 H4 H5 H0.
    case: d H3 H4 H5 => /=.
    move => local0 aggregate0 adjacent0 balance0.
    move => H3 H4 H5.
    rewrite H3 H4 H5 {aggregate0 adjacent0 balance0 H3 H4 H5}.
    exact: (recv_local _ H'_step1).
  * rewrite /update /= /update2.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec {h H_dec H'_step2} in H0 H1 H3 H4 H5 H6 H7 H8.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec''.
        rewrite H_dec'' {x H_dec'' H_dec'} in H1 H3 H4 H8.
        case: d H4 H5 H6 H7 H8 => /=.
        move => local0 aggregate0 adjacent0 balance0.
        move => H4 H5 H6 H7 H8.
        rewrite H5 H6 H7 H8 {local0 aggregate0 adjacent0 balance0 H5 H6 H7 H8}.
        case (name_eq_dec n n') => H_dec.
          have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
          by rewrite {1}H_dec in H_self.
        exact: (recv_local_eq_some H'_step1 H0 H_dec H3 H1).
      case: H_dec' => H_dec' //.
      case: d H4 H5 H6 H7 H8 => /=.
      move => local0 aggregate0 adjacent0 balance0.
      move => H4 H5 H6 H7 H8.
      rewrite H5 H6 H7 H8 {local0 aggregate0 adjacent0 balance0 H5 H6 H7 H8}.
      case (name_eq_dec x n) => H_dec.
        have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
        by rewrite -{1}H_dec in H_self.
      exact: (recv_local_neq_some H'_step1 H0 H_dec H_dec' H3 H1).
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec' in H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
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

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_aggregate : 
  forall onet failed tr m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  NMap.find n' (onet.(onwState) n).(balance) = Some m0 ->
  onet.(onwPackets) n' n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (NMap.add n' (m0 * (m')^-1) (onet.(onwState) n).(balance))) ms.

Hypothesis recv_aggregate_other : 
  forall onet failed tr m' from m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n' ->
  NMap.find from (onwState onet n).(balance) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (NMap.add from (m0 * (m'^-1)) (onet.(onwState) n).(balance))) (onet.(onwPackets) n' n).

Hypothesis recv_fail : 
  forall onet failed tr m0 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In n' failed ->
    n <> n' ->
    NMap.find n' (onwState onet n).(balance) = Some m0 ->
    onet.(onwPackets) n' n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0) (NSet.remove n' (onet.(onwState) n).(adjacent)) (NMap.remove n' (onet.(onwState) n).(balance))) ms.

Hypothesis recv_fail_other : 
  forall onet failed tr from m0 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In from failed ->
    from <> n' ->
    NMap.find from (onwState onet n).(balance) = Some m0 ->
    onet.(onwPackets) from n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(balance))) (onwPackets onet n' n).

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(balance)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate : 
  forall onet failed tr m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    NMap.find n' (onwState onet n).(balance) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add n' (m' * (onwState onet n).(aggregate)) (onwState onet n).(balance))) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet failed tr to m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    to <> n ->
    to <> n' ->
    NSet.In to (onet.(onwState) n).(adjacent) ->
    (onet.(onwState) n).(aggregate) <> 1 ->
    NMap.find to (onwState onet n).(balance) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add to (m' * (onwState onet n).(aggregate)) (onwState onet n).(balance))) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_neq :
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  ~ In n' failed ->
  n <> n' ->
  (onet.(onwState) n').(aggregate) <> 1 ->
  NSet.In n (onet.(onwState) n').(adjacent) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n ++ [Aggregate (onet.(onwState) n').(aggregate)]).

Hypothesis recv_fail_neq :
  forall onet failed tr ms m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  NMap.find n' (onet.(onwState) n).(balance) = Some m' ->
  onwPackets onet n' n = Fail :: ms ->
  P (onwState onet n) (onwPackets onet n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (NSet.remove n' ((onet.(onwState) n).(adjacent))) (NMap.remove n' (onet.(onwState) n).(balance))) ms.

Hypothesis fail_adjacent :
  forall onet failed tr,
step_o_f_star step_o_f_init (failed, onet) tr ->
~ In n failed ->
~ In n' failed ->
n' <> n ->
adjacent_to n' n ->
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
    case name_eq_dec => H_dec.
      rewrite -H_dec in H H1 H4 H5 H6 H7 H0.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H7 H0.
        case: d H4 H5 H6 H7 => /=.
        move => local0 aggregate0 adjacent0 balance0.
        move => H4 H5 H6 H7.
        rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
        case (name_eq_dec n n') => H_dec'.
          rewrite -H_dec' in H0.
          by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
        exact: (recv_aggregate H'_step1 H1 H_dec' H H0).
      case: H_dec => H_dec //.
      case: d H4 H5 H6 H7 => /=.
      move => local0 aggregate0 adjacent0 balance0.
      move => H4 H5 H6 H7.
      rewrite H4 H5 H6 H7 {local0 aggregate0 adjacent0 balance0 H4 H5 H6 H7}.
      exact: (recv_aggregate_other H'_step1 _ _ _ H0).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec'' in H_dec.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_balance H'_step1 _ H1 H_ins.
    by rewrite H_rcd in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H0 H H4 H5 H6 H7.
      case (In_dec name_eq_dec n' failed) => H_in.
        rewrite /update /=.
        case name_eq_dec => H_dec; last by rewrite H_eq' in H_dec.
        have H_neq: n <> n' by move => H_eq_n; rewrite -H_eq_n in H_in.
        move {H'_step2}.
        case: d H4 H5 H6 H7 => /= local0 aggregate0 adjacent0 balance0.
        move => H4 H5 H6 H7.
        rewrite H4 H5 H6 H7.
        exact: (recv_fail H'_step1).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update /=.
    case name_eq_dec => H_dec'; last exact: H2.
    rewrite -H_dec' in H_dec.
    case: H_dec => H_dec //.
    rewrite -H_dec' {H_dec'} in H H0 H4 H5 H6 H7.
    case (In_dec name_eq_dec from failed) => H_in.
      move {H'_step2}.
      case: d H4 H5 H6 H7 => /= local0 aggregate0 adjacent0 balance0.
      move => H5 H6 H7 H8.
      rewrite H5 H6 H7 H8 {H5 H6 H7 H8 local0 aggregate0 adjacent0 balance0}.
      by apply: (recv_fail_other H'_step1 _ _ _ _ _ H2); eauto.
    have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
    rewrite H0 in H_inl.
    by case: H_inl; left.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H1 H_in.
    have [m' H_snt] := Aggregation_in_set_exists_find_balance H'_step1 _ H1 H_ins.
    by rewrite H_snt in H.
- move {H'_step2}.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec} in H0 H3 H4 H1 H5.
    case: d H3 H4 H5 => /= local0 aggregate0 adjacent0 balance0.
    move => H3 H4 H5.
    rewrite H3 H4 H5 {aggregate0 adjacent0 balance0 H3 H4 H5}.
    exact: (recv_local _ H'_step1).
  - rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_eq].
        rewrite H_eq -H_dec in H1.
        contradict H1.
        exact: (Aggregation_node_not_adjacent_self H'_step1).
      case: H_dec' => H_dec'.
        rewrite -H_dec in H_dec'.
        rewrite -H_dec {H_dec h} in H1 H3 H4 H5 H0 H7 H8.
        case: d H6 H5 H7 H8 => /= local0 aggregate0 adjacent0 balance0.
        move => H6 H5 H7 H8.
        rewrite H6 H5 H7 H8 {local0 aggregate0 adjacent0 balance0 H6 H5 H7 H8}.
        case (name_eq_dec n' x) => H_eq.
          subst_max.
          exact: (recv_send_aggregate H'_step1).
        apply:(recv_send_aggregate_other H'_step1) => //; last by auto.
        move => H_eq'.
        rewrite H_eq' in H1.
        contradict H1.
        exact: (Aggregation_node_not_adjacent_self H'_step1).
      rewrite -H_dec {H_dec h} in H1 H0 H3 H4 H5 H7 H8.
      case: d H6 H5 H7 H8 => /= local0 aggregate0 adjacent0 balance0.
      move => H6 H5 H7 H8.
      rewrite H6 H5 H7 H8 {H6 H5 H7 H8 local0 aggregate0 adjacent0 balance0}.
      case (name_eq_dec n' x) => H_eq.
        subst_max.
        apply: (recv_send_aggregate H'_step1) => //.
        by auto.
      apply: (recv_send_aggregate_other H'_step1) => //.
      by auto.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec' in H_dec H H1 H4 H3 H5 H6 H7 H0 H8.
    rewrite H_dec' {H_dec' h}.
    rewrite H_dec'' in H4 H8 H1.
    rewrite H_dec'' {H_dec'' x}.
    exact: (recv_send_aggregate_neq H'_step1).
  * have [m' H_snt] := Aggregation_in_set_exists_find_balance H'_step1 _ H0 H.
    by rewrite H_snt in H4.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
- move => H_in_f {H'_step2}.
  have H_neq: h <> n by move => H_neq'; case: H_in_f; left.
  have H_in_f': ~ In n failed by move => H_in; case: H_in_f; right.
  have IH := IHH'_step1 H_in_f'.
  rewrite /= in IH.
  case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
  rewrite H_dec.
  rewrite H_dec {H_dec h H_in_f} in H0 H_neq.
  case (adjacent_to_dec n' n) => H_dec; last by rewrite collate_map2snd_not_related.
  rewrite collate_map2snd_not_in_related //.
  * exact: (fail_adjacent H'_step1).
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

End SingleNodeInvIn.

Instance Aggregation_Aggregator_congr (n : name) : MultiParamsSingleTotalMapCongruency (OA.Aggregator_SingleNodeParams n) Aggregation_Aggregator_multi_single_map n :=
  {
    tot_s_init_handlers_eq := _ ;
    tot_s_input_handlers_eq := _
  }.
Proof.
- by [].
- move => inp st out st' ps out' st'' H_inp H_inp'.
  unfold input_handlers, input_handler in *.  
  simpl in *.
  unfold runGenHandler_ignore, runGenHandler1_ignore in *.
  repeat break_let.
  repeat tuple_inversion.
  unfold runGenHandler in *.
  destruct st''.
  by io_handler_cases; OA.io_handler_cases; simpl in *; congruence.
Qed.

(* FIXME: trace projected for node *)
Lemma Aggregation_step_o_f_tot_one_mapped_simulation_star_1 :
  forall n net failed tr,
    step_o_f_star step_o_f_init (failed, net) tr ->
    exists tr', @step_s_star _ (OA.Aggregator_SingleNodeParams n) (@init_handler _ (OA.Aggregator_SingleNodeParams n)) (tot_s_map_data (net.(onwState) n)) tr'.
Proof.
move => n.
apply: step_o_f_tot_one_mapped_simulation_star_1.
move => net failed tr src m ms out st' ps out' st'' H_star H_eq H_in_f H_hnd H_inp.
unfold input_handlers, input_handler in *.  
simpl in *.
unfold runGenHandler_ignore, runGenHandler1_ignore in *.
repeat break_let.
repeat tuple_inversion.
unfold runGenHandler in *.
destruct st''.
destruct u0.
net_handler_cases; OA.io_handler_cases; simpl in *; (try by congruence); try repeat find_injection.
* case: H0.
  apply: (Aggregation_aggregate_msg_dst_adjacent_src H_star _ H_in_f _ x1).
  find_rewrite.
  by left.
* case: H0.
  apply: (Aggregation_in_queue_fail_then_adjacent H_star _ _ H_in_f).
  find_rewrite.
  by left.
* have [m' H_m] := Aggregation_in_set_exists_find_balance H_star _ H_in_f H0.
  by congruence.
* case: H0.
  apply: (Aggregation_in_queue_fail_then_adjacent H_star _ _ H_in_f).
  find_rewrite.
  by left.
Qed.

Instance AggregationData_Data : AggregationData Data :=
  {
    aggr_local := local ;
    aggr_aggregate := aggregate ;
    aggr_adjacent := adjacent ;
    aggr_balance := balance
  }.

Instance AggregationMsg_Aggregation : AggregationMsg :=
  {
    aggr_msg := msg ;
    aggr_msg_eq_dec := msg_eq_dec ;
    aggr_fail := Fail ;
    aggr_of := fun mg => match mg with | Aggregate m' => m' | _ => 1 end
  }.

Lemma Aggregation_conserves_node_mass : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall n, ~ In n failed -> conserves_node_mass (onet.(onwState) n).
Proof.
move => onet failed tr H n H_f.
apply (Aggregation_step_o_f_tot_one_mapped_simulation_star_1 n) in H.
move: H => [tr' H_st].
apply OA.Aggregator_conserves_node_mass in H_st.
by rewrite /= /conserves_node_mass /= in H_st.
Qed.

Lemma Aggregation_conserves_node_mass_all : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_node_mass_all (Nodes_data (remove_all name_eq_dec failed nodes) onet.(onwState)).
Proof.
move => onet failed tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data.
elim: nodes => /=; first by rewrite remove_all_nil.
move => n l IH.
move => d.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
move => H_or.
case: H_or => H_or.
  rewrite -H_or.
  exact: (Aggregation_conserves_node_mass H_st).
exact: IH.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_mass_globally (Nodes_data (remove_all name_eq_dec failed nodes) onet.(onwState)).
Proof.
move => onet failed tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed -> sum_aggregate_msg (onet.(onwPackets) n n) = 1.
Proof.
move => onet failed tr H_step n H_in_f.
by rewrite (Aggregation_self_channel_empty H_step).
Qed.

Lemma sum_local_step_o_init :
  forall ns, sum_local (Nodes_data ns init_handlers) = 1.
Proof.
rewrite /Nodes_data /step_o_init /=.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_step_o_init :
  forall ns, sum_aggregate (Nodes_data ns init_handlers) = 1.
Proof.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma Aggregation_sum_aggregate_msg_incoming_update2_aggregate : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    ~ In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) to =
    sum_aggregate_msg_incoming ns f to * (m')^-1.
Proof.
move => ns f from to ms m' H_in H_nd H_f H_eq.
by apply: sum_aggregate_msg_incoming_update2_aggregate; eauto.
Qed.

Lemma Aggregation_sum_aggregate_msg_incoming_update2_fail_eq : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
move => ns f from to ms m' H_in H_nd H_in' H_eq.
by apply: sum_aggregate_msg_incoming_update2_fail_eq; eauto.
Qed.

Lemma Aggregation_sum_aggregate_msg_incoming_update2_aggregate_in_fail_add :
  forall ns f from to ms m' x x0 adj map,
    NSet.In from adj ->
    In from ns ->
    NoDup ns ->
    In Fail (f from to) -> 
    f from to = Aggregate m' :: ms ->
    NMap.find from map = Some x0 ->
    sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) to adj (NMap.add from (x0 * x) map) =
    sum_fail_map_incoming ns f to adj map * x.
Proof.
move => ns f from to ms m' x x0 adj map H_ins H_f H_nd H_in H_eq H_find.
by apply: sum_aggregate_msg_incoming_update2_aggregate_in_fail_add; eauto.
Qed.


Lemma Aggregation_sum_aggregate_msg_incoming_update2_aggregate_in_fail :
  forall ns f from to ms m' adj map,
    In from ns ->
    NoDup ns ->
    f from to = Aggregate m' :: ms ->
    sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) to adj map =
    sum_fail_map_incoming ns f to adj map.
Proof.
move => ns f from to ms m' adj map H_in H_nd H_eq.
by apply: sum_aggregate_msg_incoming_update2_aggregate_in_fail; eauto.
Qed.

Lemma Aggregation_sum_aggregate_ms_no_aggregate_1 : 
  forall ms,
  (forall m' : m, ~ In (Aggregate m') ms) -> 
  sum_aggregate_msg ms = 1.
Proof.
move => ms H_in.
apply: sum_aggregate_ms_no_aggregate_1.
by case.
Qed.

Lemma Aggregation_sum_aggregate_msg_incoming_fail_update2_eq :
  forall ns f from to ms,
    (forall m', before_all (Aggregate m') Fail (f from to)) ->
    In from ns ->
    NoDup ns ->
    ~ In Fail ms ->
    f from to = Fail :: ms ->
    sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
move => ns f from to ms H_bef H_in H_nd H_f H_eq.
apply: sum_aggregate_msg_incoming_fail_update2_eq; eauto.
by case.
Qed.

Lemma Aggregation_sum_fail_map_incoming_add_aggregate_eq :
  forall ns f x h x0 m' adj map,
    h <> x ->
    In x ns ->
    NoDup ns ->
    In Fail (f x h) ->
    NMap.find x map = Some x0 ->
    NSet.In x adj ->
    sum_fail_map_incoming ns (update2 name_eq_dec f h x (f h x ++ [Aggregate m'])) h adj (NMap.add x (x0 * m') map) =
    sum_fail_map_incoming ns f h adj map * m'.
Proof.
move => ns f x h x0 m' adj map H_neq H_in H_nd H_f H_find H_ins.
by apply: sum_fail_map_incoming_add_aggregate_eq; eauto.
Qed.

Lemma Aggregation_sum_fail_balance_incoming_active_update2_app_eq :
  forall ns0 ns1 packets state h x m',
    sum_fail_balance_incoming_active ns1 ns0 (update2 name_eq_dec packets h x (packets h x ++ [Aggregate m'])) state =
    sum_fail_balance_incoming_active ns1 ns0 packets state.
Proof.
move => ns0 ns1 packets state h x m'.
by apply: sum_fail_balance_incoming_active_update2_app_eq.
Qed.

Lemma sum_balance_step_o_init : 
  forall ns, sum_balance ((Nodes_data ns) init_handlers) = 1.
Proof.
elim => //=.
move => n ns IH.
rewrite IH sumM_init_map_1.
by gsimpl.
Qed.

Lemma sum_fail_map_incoming_init : 
  forall ns1 ns0 n,
    sum_fail_map_incoming ns1 (fun _ _ : name => []) n (adjacency n ns0) (init_map (adjacency n ns0)) = 1.
Proof.
elim => //=.
move => n ns IH ns0 n0.
rewrite IH.
rewrite /sum_fail_map.
case: andP => H_and; last by gsimpl.
move: H_and => [H_eq H_eq'].
by contradict H_eq.
Qed.

Lemma sum_fail_balance_incoming_active_step_o_init :
  forall ns0 ns1, sum_fail_balance_incoming_active ns1 ns0 (fun _ _ => []) init_handlers = 1.
Proof.
elim => //=.
move => n ns0 IH ns1.
rewrite IH sum_fail_map_incoming_init.
by gsimpl.
Qed.

Lemma Aggregation_sum_aggregate_msg_incoming_active_in_update2_app_eq :
  forall ns0 ns1 f x h m',
    NoDup ns0 ->
    NoDup ns1 ->
    In x ns0 ->
    In h ns1 ->
    ~ In h ns0 ->
    ~ In Fail (f h x) ->
    sum_aggregate_msg_incoming_active ns1 ns0 (update2 name_eq_dec f h x (f h x ++ [Aggregate m'])) =
    sum_aggregate_msg_incoming_active ns1 ns0 f * m'.
Proof.
move => ns0 ns1 f x h m' H_nd H_nd' H_in H_in' H_not_in H_not_in'.
by apply: sum_aggregate_msg_incoming_active_in_update2_app_eq.
Qed.

Lemma sumM_sent_fail_active_eq_with_self : 
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed ->
   sumM (onet.(onwState) n).(adjacent) (onet.(onwState) n).(balance) * 
     (sum_fail_map_incoming nodes onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(balance))^-1 =
   sumM_active (onet.(onwState) n).(adjacent) (onet.(onwState) n).(balance) (remove_all name_eq_dec failed nodes).
Proof.
move => onet failed tr H_st n H_f.
have H_ex_map := Aggregation_in_set_exists_find_balance H_st _ H_f.
have H_ex_nd := Aggregation_in_adj_or_incoming_fail H_st _ H_f.
assert (H_adj_in: forall (n' : name), NSet.In n' (adjacent (onwState onet n)) -> In n' nodes).
  by move => n' H_ins; exact: all_names_nodes.
have H := @sumM_remove_fail_ex_eq AggregationMsg_Aggregation _ onet.(onwPackets) _ _ n _ H_adj_in H_ex_map.
have [adj' [H_eq [H_and H_or]]] := H no_dup_nodes.
rewrite H_eq.
have H_nd: NoDup (remove_all name_eq_dec failed nodes) by apply NoDup_remove_all; apply no_dup_nodes.
have H_eq' := sumM_sumM_active_eq _ _ H_nd _ H_and H_or H_ex_map.
rewrite H_eq' //.
  move => n' H_f' H_in.
  contradict H_f'.
  apply: (Aggregation_not_failed_no_fail H_st).
  move => H_in'.
  contradict H_in.
  by eauto using in_remove_all_not_in.
move => n' H_ins.
apply H_or in H_ins.
case: H_ins => H_ins; last by right.
apply H_and in H_ins.
move: H_ins => [H_ins H_f'].
left.
apply: in_remove_all_preserve; last exact: all_names_nodes.
apply H_ex_nd in H_ins.
case: H_ins => H_ins //.
by move: H_ins => [H_ins H_ins'].
Qed.

Lemma Aggregation_sent_received_eq : 
  forall net failed tr,
    step_o_f_star step_o_f_init (failed, net) tr ->
    forall n n' m0 m1,
     ~ In n failed ->
     ~ In n' failed ->
    NSet.In n' (net.(onwState) n).(adjacent) ->
    NSet.In n (net.(onwState) n').(adjacent) ->
    NMap.find n (net.(onwState) n').(balance) = Some m0 ->
    NMap.find n' (net.(onwState) n).(balance) = Some m1 ->
    m0 * (sum_aggregate_msg (net.(onwPackets) n n'))^-1 = (m1)^-1 * sum_aggregate_msg (net.(onwPackets) n' n).
Proof.
move => onet failed tr H_st.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {3 4 5 6 7 8}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /= {H_init}.
  move => n n' m0 m1 H_in H_in'.
  rewrite /init_map /=.
  case init_map_str => map H_init_map.
  case init_map_str => map' H_init_map'.
  move => H_ins H_ins' H_find H_find'.
  apply H_init_map in H_ins'.
  apply H_init_map' in H_ins.
  rewrite H_ins in H_find'.
  rewrite H_ins' in H_find.
  inversion H_find'.
  inversion H_find.
  by gsimpl.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move {H_st2}.
  rewrite /= in IHH_st1.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => /=.
  * move: H4 H5 H6 H7 H.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H11 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H3.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H11 H12 H_dec.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
        move => H_ins H_ins' H_find H_find' H_find''.
        rewrite NMapFacts.add_eq_o // in H_find'.
        find_injection.
        gsimpl.
        rewrite (IHH_st1 _ _ _ _ H2 H3 H_ins H_ins' H_find H_find'') H0 /= /aggregate_sum_fold /=.
        by aac_reflexivity.
      case: H_and' => H_and' //.
      move => H_ins H_ins' H_find H_find' H_find''.
      rewrite NMapFacts.add_neq_o // in H_find'.
      exact: IHH_st1.
    + rewrite H11 H12 H_dec'.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
        move => H_ins H_ins' H_find H_find' H_find''.
        rewrite NMapFacts.add_eq_o // in H_find.
        find_injection.
        rewrite -(IHH_st1 _ _ _ _ H2 H3 H_ins H_ins' H_find'' H_find') H0 /= /aggregate_sum_fold /=.
        by gsimpl.
      case: H_and => H_and //.
      move => H_ins H_ins' H_find H_find' H_find''.
      rewrite NMapFacts.add_neq_o // in H_find.
      exact: IHH_st1.
    + rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
      move => H_ins H_ins' H_find H_find' H_find''.
      exact: IHH_st1.
  * have H_agg := Aggregation_aggregate_msg_dst_adjacent_src H_st1 _ H1 from x.
    rewrite H0 in H_agg.
    suff H_suff: NSet.In from (adjacent (onwState net to)).
      have [m' H_ex] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H_suff.
      by rewrite H_ex in H2.
    apply: H_agg.
    by left.
  * move: H4 H5 H6 H7.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H11 -H_dec'.
      move => H_ins.
      apply NSetFacts.remove_3 in H_ins.
      contradict H_ins.
      move: H_st1 H3.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H11 H12 H_dec.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
        have H_in_f: In Fail (onwPackets net n' to) by rewrite H0; left.
        contradict H_in_f.
        exact: (Aggregation_not_failed_no_fail H_st1).
      case: H_and' => H_and' //.
      move => H_ins H_ins' H_find H_find'.
      apply NSetFacts.remove_3 in H_ins.
      rewrite NMapFacts.remove_neq_o // in H_find'.
      exact: IHH_st1.
    + rewrite H11 H12 H_dec'.
      move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=; first by apply NSetFacts.remove_1 in H_ins'.
      have H_neq': from <> n.
        move => H_eq.
        rewrite H_eq in H_ins'.
        by apply NSetFacts.remove_1 in H_ins'.
      apply NSetFacts.remove_3 in H_ins'.
      rewrite NMapFacts.remove_neq_o // in H_find.
      exact: IHH_st1.
    + rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
      exact: IHH_st1.
  * have H_f := Aggregation_in_queue_fail_then_adjacent H_st1 to from H1.
    rewrite H0 in H_f.
    concludes.
    suff H_suff: NSet.In from (adjacent (onwState net to)).
      have [m' H_ex] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H_suff.
      by rewrite H_ex in H.
    exact: H_f.
- move {H_st2}.
  rewrite /= in IHH_st1.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H9 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H9 H10 -H_dec.
      exact: IHH_st1.
    + rewrite H9 H10 -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H12 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H12 H13 H_dec.
      move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
        rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
        rewrite NMapFacts.add_eq_o // in H_find'.
        find_injection.
        gsimpl.
        aac_rewrite (IHH_st1 _ _ _ _ H0 H2 H_ins H_ins' H_find H9).
        by aac_reflexivity.
      case: H_and => H_and //.
      apply NMapFacts.find_mapsto_iff in H_find'.
      apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
      apply NMapFacts.find_mapsto_iff in H_find'.
      exact: IHH_st1.
    + move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; try subst => //=.
        repeat find_rewrite.
        rewrite NMapFacts.add_eq_o // in H_find.
        find_injection.
        rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
        aac_rewrite (IHH_st1 _ _ _ _ H H2 H_ins H_ins' H9 H_find').
        by gsimpl.
      case: H_and' => H_and' //.
      repeat find_rewrite.
      apply NMapFacts.find_mapsto_iff in H_find.
      apply NMapFacts.add_neq_mapsto_iff in H_find => //.
      apply NMapFacts.find_mapsto_iff in H_find.
      exact: IHH_st1.
    + move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; break_and; case sumbool_and => H_and'; break_and; subst => //=.
      exact: IHH_st1.
  * have [m' H_ex] := Aggregation_in_set_exists_find_balance H_st1 _ H0 H.
    by rewrite H_ex in H9.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H0.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * move: H3 H4 H5 H6.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * move: H6 H7 H8 H9.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H5.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
- move {H_st2}.
  rewrite /= in IHH_st1.
  move => n n' m0 m1 H_f H_f' H_ins H_ins' H_find H_find'.
  rewrite sum_aggregate_msg_collate_fail_eq //.
  rewrite sum_aggregate_msg_collate_fail_eq //.
  have H_in: ~ In n failed0 by move => H_in; case: H_f; right.
  have H_in': ~ In n' failed0 by move => H_in'; case: H_f'; right.
  exact: IHH_st1.
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  conserves_network_mass (remove_all name_eq_dec failed nodes) nodes onet.(onwPackets) onet.(onwState).
Proof.
move => onet failed tr H_step.
rewrite /conserves_network_mass.
have H_cons := Aggregation_conserves_node_mass_all H_step.
apply global_conservation in H_cons.
rewrite /conserves_mass_globally in H_cons.
rewrite H_cons {H_cons}.
set sb := sum_balance _.
set saa := sum_aggregate_msg_incoming_active _ _ _.
set sfb := sum_fail_balance_incoming_active _ _ _ _.
suff H_suff: sb = saa * sfb by aac_rewrite H_suff; rewrite /Nodes_data /=; aac_reflexivity.
rewrite /sb /saa /sfb {sb saa sfb}.
remember step_o_f_init as y in *.
have ->: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite {2 4 6 7} H_eq_o {H_eq_o}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init {H_init} /=.
  rewrite sum_aggregate_msg_incoming_active_step_o_init.
  rewrite sum_balance_step_o_init.
  rewrite sum_fail_balance_incoming_active_step_o_init.
  by gsimpl.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H_step2}.
  have H_in_from : In from nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In to (remove_all name_eq_dec failed0 nodes).
    have H_inn := all_names_nodes to.
    exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := NoDup_remove_all name_eq_dec failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_to_nin: ~ In to ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In to ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq //.
  rewrite Nodes_data_not_in_eq //.  
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_split /=.
  move => IH.  
  net_handler_cases => //=.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    rewrite sumM_add_map //.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_balance_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_balance_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H5 H6 {H3 H4 H5 H6}.
    case (In_dec Msg_eq_dec Fail (net.(onwPackets) from to)) => H_in_fail.
      rewrite (Aggregation_sum_aggregate_msg_incoming_update2_fail_eq _ _ _ _ no_dup_nodes _ H0) //.
      rewrite (Aggregation_sum_aggregate_msg_incoming_update2_aggregate_in_fail_add _ _ _ H_ins _ no_dup_nodes _ H0) //.
      by gsimpl.
    rewrite (Aggregation_sum_aggregate_msg_incoming_update2_aggregate _ _ _ H_in_from no_dup_nodes H_in_fail H0).
    rewrite (@no_fail_sum_fail_map_incoming_add_eq AggregationMsg_Aggregation _ _ _ _ _ _ _ _ _ (all_names_nodes from) no_dup_nodes H0 H_in_fail).
    by aac_reflexivity.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H_ins.
    by rewrite H_rcd in H.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_in': ~ In Fail ms.
      have H_le := Aggregation_le_one_fail H_step1 _ from H1.
      rewrite H0 /= in H_le.
      move: H_le.
      case H_cnt: (count_occ _ _ _) => H_le; last by omega.
      by apply count_occ_not_In in H_cnt.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    rewrite (sumM_remove_remove H_ins H).
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_balance_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_balance_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    have H_bef := Aggregation_in_after_all_fail_aggregate H_step1 _ H1 from.
    rewrite (Aggregation_sum_aggregate_msg_incoming_fail_update2_eq _ _ _ H_bef _ no_dup_nodes) //.
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H5 H6.
    rewrite (@sum_fail_map_incoming_fail_remove_eq AggregationMsg_Aggregation _ _ _ _ _ _ _ _ _ no_dup_nodes H_ins _ H_in' H) //.    
    by gsimpl.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    have [m5 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H_ins.
    by rewrite H_bal in H.
- find_apply_lem_hyp input_handlers_IOHandler.
  move {H_step2}.
  have H_in_from : In h nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (remove_all name_eq_dec failed0 nodes).
    have H_inn := all_names_nodes h.
    exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := NoDup_remove_all name_eq_dec failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_h_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_h_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq //.
  rewrite Nodes_data_not_in_eq //.  
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_split /=.
  move => IH.
  io_handler_cases => //=.
  * rewrite sum_fail_balance_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_balance_incoming_active_not_in_eq_alt //.
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    by rewrite H3 H4.
  * have H_x_Nodes: In x nodes by exact: all_names_nodes.
    have H_neq: h <> x by move => H_eq; have H_self := Aggregation_node_not_adjacent_self H_step1 H0; rewrite {1}H_eq in H_self.
    rewrite (sumM_add_map _ H H3).
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_neq_eq //.
    rewrite {3 4}/update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H6 H7.
    case (In_dec name_eq_dec x failed0) => H_dec.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H0 H.
      case: H_or => H_or //.
      move: H_or => [H_dec' H_in] {H_dec'}.
      have H_x_ex: ~ In x (remove_all name_eq_dec failed0 nodes) by eauto using in_remove_all_not_in.
      rewrite H_inn in H_x_ex.
      have H_x_nin: ~ In x ns0 by move => H_x_in; case: H_x_ex; apply in_or_app; left.
      have H_x_nin': ~ In x ns1 by move => H_x_in; case: H_x_ex; apply in_or_app; right; right.
      rewrite sum_fail_balance_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_balance_incoming_active_not_in_eq_alt2 //.
      rewrite (Aggregation_sum_fail_map_incoming_add_aggregate_eq _ _ _ _ no_dup_nodes) //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      by aac_reflexivity.
    have H_in := Aggregation_not_failed_no_fail H_step1 _ x H0.
    have H_in' := Aggregation_not_failed_no_fail H_step1 _ h H_dec.
    rewrite sum_fail_balance_incoming_active_update_not_in_eq //.
    rewrite sum_fail_balance_incoming_active_update_not_in_eq //.
    rewrite Aggregation_sum_fail_balance_incoming_active_update2_app_eq //.
    rewrite Aggregation_sum_fail_balance_incoming_active_update2_app_eq //.
    rewrite (sum_fail_map_incoming_not_in_fail_add_update2_eq _ _ _ _ _ _ _ no_dup_nodes) //.
    have H_in_x: In x (remove_all name_eq_dec failed0 nodes) by exact: in_remove_all_preserve.
    rewrite H_inn in H_in_x.
    apply in_app_or in H_in_x.
    case: H_in_x => H_in_x.
      have H_nin_x: ~ In x ns1.
        move => H_nin_x.
        apply NoDup_remove_1 in H_nd.
        contradict H_nin_x.
        move: H_in_x.
        exact: NoDup_in_not_in_right.
      have H_nd': NoDup ns0 by move: H_nd; exact: NoDup_app_left.
      rewrite (sum_aggregate_msg_incoming_active_not_in_eq ns1) //.
      rewrite (Aggregation_sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ no_dup_nodes) //.
      by aac_reflexivity.
    case: H_in_x => H_in_x //.
    have H_nin_x: ~ In x ns0.
      move => H_nin_x.
      apply NoDup_remove_1 in H_nd.
      contradict H_nin_x.
      move: H_in_x.
      exact: NoDup_in_not_in_left.
    have H_nd': NoDup ns1.
      apply NoDup_app_right in H_nd.
      by inversion H_nd.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (Aggregation_sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ no_dup_nodes) //.
    by aac_reflexivity.
  * have [m' H_snt] := Aggregation_in_set_exists_find_balance H_step1 _ H0 H.
    by rewrite H_snt in H3.
  * by rewrite update_nop update_nop_ext.
  * by rewrite update_nop update_nop_ext.
  * by rewrite update_nop update_nop_ext.
- move {H_step2}.
  have H_in_from : In h nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (remove_all name_eq_dec failed0 nodes).
    have H_inn := all_names_nodes h.
    exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  have H_nd := NoDup_remove_all name_eq_dec failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_to_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  have H_ex := remove_all_NoDup_split name_eq_dec _ _ _ _ no_dup_nodes H_inn.
  rewrite H_ex.
  rewrite H_inn.
  have H_nd': NoDup ns0 by move: H_nd; exact: NoDup_app_left.
  have H_nd'': NoDup ns1 by apply NoDup_app_right in H_nd; inversion H_nd.
  rewrite 2!Nodes_data_split /=.  
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_split /=.
  gsimpl.
  move => IH.
  rewrite filter_rel_self_eq.
  set l := collate _ _ _ _.
  rewrite sum_balance_Nodes_data_distr in IH.
  rewrite sum_balance_Nodes_data_distr.
  move: IH.
  rewrite -2!sum_aggregate_msg_incoming_active_split.
  move => IH.
  set sa := sum_aggregate_msg_incoming_active _ _ _.
  set sf1 := sum_fail_balance_incoming_active _ _ _ _.
  set sf2 := sum_fail_balance_incoming_active _ _ _ _.
  have ->: sa * sf1 * sf2 =
    sa * @sum_fail_balance_incoming_active AggregationMsg_Aggregation _ AggregationData_Data nodes (ns0 ++ ns1) l (onwState net).
    rewrite sum_fail_balance_incoming_active_split.
    by gsimpl.
  rewrite /sa /sf1 /sf2 {sa sf1 sf2}.
  move: IH.
  set saa := sum_aggregate_msg_incoming_active _ _ _.
  set sai := sum_aggregate_msg_incoming _ _ _.
  set sf1 := sum_fail_balance_incoming_active _ _ _ _.
  set sf2 := sum_fail_balance_incoming_active _ _ _ _.
  set sfm := sum_fail_map_incoming _ _ _ _ _.
  have ->: saa * sai * sf1 * sf2 * sfm = 
    saa * sai * @sum_fail_balance_incoming_active AggregationMsg_Aggregation _ AggregationData_Data nodes (ns0 ++ ns1) (onwPackets net) (onwState net) * sfm.
    rewrite sum_fail_balance_incoming_active_split.
    by gsimpl.
  rewrite /saa /sai /sf1 /sf2 /sfm {saa sai sf1 sf2 sfm}.
  set sums := sumM _ _.
  set sb := sum_balance _.
  move => IH.
  set sam := sum_aggregate_msg_incoming_active _ _ _.  
  set sfbi := sum_fail_balance_incoming_active _ _ _ _.
  suff H_suff: sb * sums * sums^-1 = sam * sfbi by move: H_suff; gsimpl.
  aac_rewrite IH.
  move {IH}.
  rewrite /sums /sb /sam /sfbi {sums sb sam sfbi}.
  rewrite /l {l}.
  have H_acs := sumM_sent_fail_active_eq_with_self H_step1 _ H0.
  have H_pmn: Permutation (h :: ns0 ++ ns1) (remove_all name_eq_dec failed0 nodes) by rewrite H_inn; exact: Permutation_middle.
  rewrite -(sumM_active_eq_sym _ _ H_pmn) /= /sum_active_fold in H_acs.
  move: H_acs {H_pmn}.
  case: ifP => H_mem; first by apply NSetFacts.mem_2 in H_mem; contradict H_mem; exact: (Aggregation_node_not_adjacent_self H_step1).
  set s1 := sum_fail_map_incoming _ _ _ _ _.
  move => H_acs {H_mem}.  
  have H_acs': 
    (sumM (adjacent (onwState net h)) (balance (onwState net h)))^-1 * s1 =
    (sumM_active (adjacent (onwState net h)) (balance (onwState net h)) (ns0 ++ ns1))^-1.
    rewrite -H_acs.
    by gsimpl; aac_reflexivity.
  aac_rewrite H_acs'.
  move {H_acs H_acs' s1}.
  apply NoDup_remove_1 in H_nd.
  move: H_nd H_nin H_ex.
  set ns := ns0 ++ ns1.
  move => H_nd H_nin H_ex.
  move {H_to_nin H_to_nin' H_nd' H_nd'' H_inn}.
  move {H_nin H_nd}.
  have H_nd := no_dup_nodes.
  move: ns H_ex => ns H_ex {ns0 ns1}.
  apply in_split in H_in_from.
  move: H_in_from => [ns0 [ns1 H_in_from]].
  rewrite H_in_from in H_ex.
  rewrite H_in_from in H_nd.
  have H_nin: ~ In h (ns0 ++ ns1) by exact: NoDup_mid_not_in.
  apply NoDup_remove_1 in H_nd.
  rewrite remove_partition in H_ex.
  have H_pm: Permutation nodes (h :: ns0 ++ ns1).
    rewrite H_in_from.
    apply Permutation_sym.
    exact: Permutation_middle.
  move {H_in_from}.
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_permutation_eq _ _ H_pm).
  rewrite (sum_fail_balance_incoming_active_permutation_eq _ _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_fail_balance_incoming_active_permutation_eq _ _ _ H_pm).
  move: H_nd H_nin ns H_ex {H_pm}.
  set ns' := ns0 ++ ns1.
  elim: ns' => /=; rewrite (Aggregation_self_channel_empty H_step1) //=; first by move => H_nd H_in ns H_eq; rewrite -H_eq remove_all_nil /=; gsimpl.
  move => n ns' IH H_nd H_in ns.
  inversion H_nd => {x H l H1}.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_in': ~ In h ns' by move => H_in'; case: H_in; right.
  move {H_in H_nd}.
  case name_eq_dec => H_dec //=.
  move => H_ex.
  have H_cn := remove_all_cons name_eq_dec failed0 n (remove name_eq_dec h ns').
  rewrite H_ex in H_cn => {H_ex}.  
  break_or_hyp; break_and.
    match goal with | H : _ = remove_all _ _ _ |- _ => symmetry in H end.
    move {H_dec}.
    have IH' := IH H3 H_in' _ H.
    move {IH}.
    move: IH'.
    move => IH.
    case in_dec => /= H_dec; case H_mem: (NSet.mem n (net.(onwState) h).(adjacent)).
    - apply NSetFacts.mem_2 in H_mem.
      rewrite sum_fail_balance_incoming_active_all_head_eq.
      rewrite sum_fail_balance_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_balance_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      aac_rewrite IH.
      move {IH}.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
      rewrite -(sum_fail_balance_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      by gsimpl; aac_reflexivity.
    - move/negP: H_mem => H_mem.
      case: H_mem.
      apply NSetFacts.mem_1.
      exact: (Aggregation_in_queue_fail_then_adjacent H_step1).
    - apply NSetFacts.mem_2 in H_mem.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H0 H_mem.
      case: H_or => H_or //.
      by move: H_or => [H_or H_f].
    - move/negP: H_mem => H_mem.
      have H_notin: forall m', ~ In (Aggregate m') (onwPackets net n h).
        move => m' H_in.
        case: H_mem.
        apply NSetFacts.mem_1.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ _ _ m').
      rewrite (Aggregation_sum_aggregate_ms_no_aggregate_1 _ H_notin).
      rewrite sum_fail_balance_incoming_active_all_head_eq.
      rewrite sum_fail_balance_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_balance_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      aac_rewrite IH.
      move {IH}.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
      rewrite -(sum_fail_balance_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      by gsimpl; aac_reflexivity.
  match goal with | H : _ = _ :: remove_all _ _ _ |- _ => symmetry in H end.
  move: H.
  move {H_dec}.
  case: ns IH H2 H3 H_in' => //.
  move => n' ns IH H_in H_nd H_nin H_ex.
  have H_ex': remove_all name_eq_dec failed0 (remove name_eq_dec h ns') = ns by inversion H_ex.
  have H_eq: n = n' by inversion H_ex.
  rewrite -H_eq {n' H_eq H_ex}.
  have IH' := IH H_nd H_nin _ H_ex'.
  move {IH}.
  rewrite /=.
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  rewrite {1 3}/sum_fail_map /=.
  rewrite /sum_active_fold.
  case (adjacent_to_dec _ _) => H_Adj; last first.
    rewrite /=.
    have H_Adj': ~ adjacent_to n h by move => H_Adj'; apply adjacent_to_symmetric in H_Adj'.
    case: ifP => H_dec.
      apply NSetFacts.mem_2 in H_dec.
      case: H_Adj'.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; rewrite collate_neq // (Aggregation_self_channel_empty H_step1).
    move {H_dec}.
    have H_ins: ~ NSet.In h (net.(onwState) n).(adjacent).
      move => H_ins.
      case: H_Adj.
      move: H_ins.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    have H_ins': ~ NSet.In n (net.(onwState) h).(adjacent).
      move => H_ins'.
      case: H_Adj'.
      move: H_ins'.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    case in_dec => /= H_dec; first by rewrite collate_map2snd_not_related // in H_dec; case: H_ins; exact: (Aggregation_in_queue_fail_then_adjacent H_step1).
    move {H_dec}.
    rewrite (collate_map2snd_not_related _ _ _ name_eq_dec _ _ _ _ _ _ H_Adj).
    rewrite (collate_neq _ _ name_eq_dec _ _ _ _ _ H_neq) //.
    rewrite (Aggregation_self_channel_empty H_step1) //=.
    rewrite {2}/sum_fail_map /=.
    have H_emp_hn: onwPackets net h n = [].
      have H_in_agg: forall m', ~ In (Aggregate m') (net.(onwPackets) h n).
        move => m' H_in_agg.
        case: H_ins.
        move: H_in_agg.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1).
      have H_in_f: ~ In Fail (net.(onwPackets) h n) by exact: (Aggregation_not_failed_no_fail H_step1).
      move: H_in_agg H_in_f.
      elim: (onwPackets net h n) => //.
      case => [m'|] l H_in_f H_in_agg H_in_m; first by case (H_in_agg m'); left.
      by case: H_in_m; left.      
    have H_emp_nh: onwPackets net n h = [].
      have H_in_agg: forall m', ~ In (Aggregate m') (net.(onwPackets) n h).
        move => m' H_in_agg.
        case: H_ins'.
        move: H_in_agg.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1).
      have H_in_f: ~ In Fail (net.(onwPackets) n h) by exact: (Aggregation_not_failed_no_fail H_step1).
      move: H_in_agg H_in_f.
      elim: (onwPackets net n h) => //.
      case => [m'|] l H_in_f H_in_agg H_in_m; first by case (H_in_agg m'); left.
      by case: H_in_m; left.
    rewrite H_emp_hn H_emp_nh /sum_fail_map /=.
    rewrite sum_fail_balance_incoming_active_all_head_eq.
    rewrite sum_fail_balance_incoming_active_all_head_eq in IH'.
    rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
    rewrite (sum_fail_balance_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_fail_balance_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
    rewrite sum_aggregate_msg_incoming_active_all_head_eq.
    rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    aac_rewrite IH'.
    move {IH'}.
    rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
    rewrite -(sum_fail_balance_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
    rewrite (sum_fail_map_incoming_not_adjacent_collate_eq _ _ _ _ _ H_Adj).
    rewrite (sum_aggregate_msg_incoming_not_adjacent_collate_eq _ _ _ H_Adj).
    by gsimpl; aac_reflexivity.
  rewrite /=.
  have H_adj': adjacent_to n h by apply adjacent_to_symmetric in H_Adj.
  have H_ins: NSet.In h (net.(onwState) n).(adjacent) by exact: (Aggregation_adjacent_to_in_adj H_step1).
  have H_ins': NSet.In n (net.(onwState) h).(adjacent) by exact: (Aggregation_adjacent_to_in_adj H_step1).
  case: ifP => H_mem; last by move/negP: H_mem => H_mem; case: H_mem; apply NSetFacts.mem_1.
  move {H_mem}.
  have H_in_f: ~ In Fail (net.(onwPackets) h n) by exact: (Aggregation_not_failed_no_fail H_step1).
  have H_in_f': ~ In Fail (net.(onwPackets) n h) by exact: (Aggregation_not_failed_no_fail H_step1).
  case in_dec => /= H_dec_f //.
  move {H_dec_f}.
  case in_dec => /= H_dec_f //.
  move {H_dec_f}.
  rewrite (collate_neq _ _ name_eq_dec _ _ _ _ _ H_neq) //.
  case in_dec => /= H_dec_f.
    contradict H_dec_f.
    rewrite /update2.
    case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
    by rewrite (Aggregation_self_channel_empty H_step1).
  move {H_dec_f}.
  have H_in_n: ~ In n ns.
    move => H_in_n.
    rewrite -H_ex' in H_in_n.
    rewrite remove_not_in // in H_in_n.
    case: H_in.
    move: H_in_n.
    exact: in_remove_all_was_in.
  case in_dec => /= H_dec_f; last first.
    case: H_dec_f.
    have H_a := collate_map2snd_related_not_in _ _ _ name_eq_dec adjacent_to_dec Fail _ _ _ _ H_Adj H_in_n.
    move: H_a.
    rewrite /=.
    case adjacent_to_dec => /= H_dec // {H_dec}.
    rewrite /=.
    move => H_a.
    by rewrite H_a; first by apply in_or_app; right; left.
  move {H_dec_f}.
  rewrite {3}/update2.
  case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  move {H_and}.
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  have [m0 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H0 H_ins'.
  rewrite /sum_fold.
  case H_bal': NMap.find => [m'0|]; last by rewrite H_bal in H_bal'.
  rewrite H_bal in H_bal'.
  injection H_bal' => H_eq_bal.
  rewrite -H_eq_bal {m'0 H_bal' H_eq_bal}.
  rewrite sum_fail_balance_incoming_active_all_head_eq.
  rewrite sum_fail_balance_incoming_active_all_head_eq in IH'.
  rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
  rewrite (sum_fail_balance_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_fail_balance_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_fail_balance_incoming_active_all_head_eq ns').
  rewrite sum_aggregate_msg_incoming_active_all_head_eq.
  rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  move: IH'.
  gsimpl.
  move => IH.
  aac_rewrite IH.
  move {IH}.
  set u2 := update2 _ _ _ _ _.
  set cl := collate _ _ _ _.
  rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
  rewrite -(sum_fail_balance_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
  rewrite /sum_fail_map.
  case in_dec => /= H_dec // {H_dec}.
  case in_dec => /= H_dec; last first.
    case: H_dec.
    rewrite /cl /u2.
    have H_a := collate_map2snd_related_not_in _ _ _ name_eq_dec adjacent_to_dec Fail _ _ _ _ H_Adj H_in_n.
    move: H_a.
    rewrite /=.
    case adjacent_to_dec => /= H_dec // {H_dec}.
    rewrite /=.
    move => H_a.
    rewrite H_a.
    by apply in_or_app; right; left.
  move {H_dec}.
  case: ifP => H_mem; last by move/negP: H_mem => H_mem; case: H_mem; exact: NSetFacts.mem_1.
  move {H_mem}.
  rewrite /sum_fold.
  have [m2 H_bal_n] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H_ins.
  case H_bal': NMap.find => [m'2|]; last by rewrite H_bal_n in H_bal'.
  rewrite H_bal_n in H_bal'.
  injection H_bal' => H_eq_bal.
  rewrite -H_eq_bal {m'2 H_bal' H_eq_bal}.
  rewrite sum_aggregate_msg_incoming_active_eq_not_in_eq //.
  rewrite {1}/cl {1}/u2.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite {1}/cl /u2.
  rewrite sum_aggregate_msg_incoming_collate_update2_notin_eq //.
  rewrite sum_aggregate_msg_incoming_collate_msg_for_notin_eq //.
  have H_sr := Aggregation_sent_received_eq H_step1 H0 H1 H_ins' H_ins H_bal_n H_bal.
  aac_rewrite <- H_sr.
  move {H_sr}.
  have H_agg: @sum_aggregate_msg AggregationMsg_Aggregation (onwPackets net h n) * (@sum_aggregate_msg AggregationMsg_Aggregation (onwPackets net h n))^-1 = 1 by gsimpl.
  aac_rewrite H_agg.
  move {H_agg}.
  rewrite {1 2}/cl /u2.
  rewrite sum_fail_map_incoming_collate_not_in_eq //.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite sum_fail_balance_incoming_active_collate_update2_eq //.
  rewrite sum_fail_balance_incoming_active_collate_update2_eq //.
  rewrite sum_fail_balance_incoming_active_not_in_eq_alt_alt //.
  rewrite /cl {u2 cl}.
  set s1 := sum_fail_map_incoming _ _ _ _ _.
  set s5 := sum_aggregate_msg_incoming_active _ _ _.
  set s6 := sum_aggregate_msg_incoming _ _ _.
  set s8 := sum_fail_balance_incoming_active _ _ _ _.
  set s10 := sum_fail_balance_incoming_active _ _ _ _.
  set s11 := sum_fail_balance_incoming_active _ _ _ _.
  set s12 := sum_aggregate_msg_incoming_active _ _ _.
  set s13 := sum_aggregate_msg_incoming_active _ _ _.
  by gsimpl; aac_reflexivity.
Qed.

End Aggregation.
