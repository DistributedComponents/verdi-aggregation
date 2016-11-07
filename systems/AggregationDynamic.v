Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.DynamicNetLemmas.
Require Import Verdi.SingleSimulations.

Require Import AggregationDefinitions.
Require Import AggregationAux.
Require Import AggregatorDynamic.
Require Import FailureRecorderDynamic.

Require Import Sumbool.
Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import AAC_tactics.AAC.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module Aggregation (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import CFG : CommutativeFinGroup) 
 (Import ANT : AdjacentNameType NT)
 (Import AD : ADefs NT NOT NSet NOTC NMap CFG).

Module AX := AAux NT NOT NSet NOTC NMap CFG ANT AD.
Import AX.

Module OA := SingleAggregator NT NOT NSet NOTC NMap CFG ANT AD.

Module FR := FailureRecorder NT NOT NSet ANT.

Import GroupScope.

Module ADCFGAACInstances := CFGAACInstances CFG.
Import ADCFGAACInstances.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Inductive Msg : Type := 
| Aggregate : m -> Msg
| Fail : Msg
| New : Msg.

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
     adjacent := NSet.empty ;
     balance := NMap.empty m |}.

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
| New =>
  put {| local := st.(local) ;
         aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
         balance := NMap.add src 1 st.(balance) |}
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
   | Some m_dst =>        
     put {| local := st.(local) ;
            aggregate := 1 ;
            adjacent := st.(adjacent) ;
            balance := NMap.add dst (m_dst * st.(aggregate)) st.(balance) |} ;; 
     send (dst, (Aggregate st.(aggregate)))
   | None => nop
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

Instance Aggregation_NewMsgParams : NewMsgParams Aggregation_MultiParams :=
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
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = st.(balance) /\
         out = [] /\ ms = []) \/
      (exists dst m', i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(balance) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = NMap.add dst (m' * st.(aggregate)) st.(balance) /\
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
     st'.(balance) = NMap.add src (m_src * (m_msg)^-1) st.(balance) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ NMap.find src st.(balance) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_bal, msg = Fail /\ NMap.find src st.(balance) = Some m_bal /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ NMap.find src st.(balance) = None /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     out = [] /\ ms = []) \/
    (msg = New /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(balance) = NMap.add src 1 st.(balance) /\
     out = [] /\ ms =[]).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg||]; monad_unfold; repeat break_let; repeat break_match; repeat find_injection.
- by left; exists m_msg, a.
- by right; left; exists m_msg.
- by right; right; left; exists a.
- by right; right; right; left.
- move => H_eq.
  find_injection.
  by right; right; right; right.
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
    pt_map_msg := fun m => 
                   match m with 
                   | Fail => Some FR.Fail 
                   | New => Some FR.New
                   | _ => None 
                   end ;
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

Instance Aggregation_FailureRecorder_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency Aggregation_NewMsgParams FR.FailureRecorder_NewMsgParams Aggregation_FailureRecorder_multi_params_pt_map := 
  {
    pt_new_msg_fst_snd := Logic.eq_refl
  }.

Theorem Aggregation_Failed_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ _ Aggregation_NewMsgParams Aggregation_FailMsgParams step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ _ FR.FailureRecorder_NewMsgParams FR.FailureRecorder_FailMsgParams step_ordered_dynamic_failure_init (failed, pt_map_odnet net) (pt_map_traces tr).
Proof.
move => onet failed tr H_st.
apply step_ordered_dynamic_failure_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 ~ In n failed ->
 forall d, odnwState net n = Some d ->
 ~ NSet.In n d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f d H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_node_not_adjacent_self _ _ _ H_st' n.
rewrite /= /id /= map_id H_eq in H_inv'.
have IH_inv'' := H_inv' H_n H_f {| FR.adjacent := d.(adjacent) |}.
rewrite /= in IH_inv''.
exact: IH_inv''.
Qed.

Lemma Aggregation_not_failed_no_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, In n (odnwNodes onet) -> ~ In n failed ->
  forall n', ~ In Fail (onet.(odnwPackets) n n').
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FR.Failure_not_failed_no_fail H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move => H_in.
case: IH'.
move: H_in.
apply: in_msg_pt_map_msgs.
exact: pt_fail_msg_fst_snd.
Qed.

Lemma Aggregation_in_after_all_fail_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), before_all New Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FR.Failure_in_after_all_fail_new H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
exact: in_all_before_pt_map_msg.
Qed.

Lemma Aggregation_pt_map_msg_injective : 
  forall m0 m1 m2 : msg,
   pt_map_msg m0 = Some m2 -> pt_map_msg m1 = Some m2 -> m0 = m1.
Proof.
by case => [m'||]; case => [m''||] => //=; case.
Qed.

Lemma Aggregation_le_one_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) New <= 1.
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FR.Failure_le_one_new H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_pt_map_msgs_eq => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_le_one_fail : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) Fail <= 1.
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FR.Failure_le_one_fail H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_pt_map_msgs_eq => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_in_new_failed_incoming_fail : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
    forall n, In n (odnwNodes onet) -> ~ In n failed ->
         forall n', In n' failed ->
               In New (onet.(odnwPackets) n' n) ->
               In Fail (onet.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_f' H_in.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_new_failed_incoming_fail H_st'.
rewrite /= map_id /id /= in H_inv'.
have IH := H_inv' _ H_n H_f _ H_f'.
move: IH.
set in_pt := In FR.Fail _.
move => IH.
suff H_suff: in_pt.
  move: H_suff.
  apply: in_pt_map_msgs_in_msg => //.
  exact: Aggregation_pt_map_msg_injective.
apply: IH.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggreation_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
          forall d, onet.(odnwState) n = Some d ->
               NSet.In n' d.(adjacent) ->
               adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_n H_f d H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_in_adj_adjacent_to _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f {| FR.adjacent := d.(adjacent) |}.
exact: H_inv''.
Qed.

Lemma Aggregation_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
       forall d, onet.(odnwState) n = Some d ->
            NSet.In n' d.(adjacent) ->
            (In n' (odnwNodes onet) /\ ~ In n' failed) \/ (In n' (odnwNodes onet) /\ In n' failed /\ In Fail (onet.(odnwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_n H_f d H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_in_adj_or_incoming_fail  _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f {| FR.adjacent := d.(adjacent) |}.
rewrite /= in H_inv''.
move => H_ins.
case (H_inv'' (Logic.eq_refl _) H_ins) => H_in.
  break_and.
  by left.
break_and.
right.
split => //.
split => //.
move: H1.
apply: in_pt_map_msgs_in_msg => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_new_incoming_not_in_adj :
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->        
        forall (n' : name), In New (net.(odnwPackets) n' n) ->
                       forall d, net.(odnwState) n = Some d ->
                            ~ NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f n' H_in d H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_new_incoming_not_in_adj _ _ _ H_st' n _ _ n' _ {| FR.adjacent := d.(adjacent) |}.
rewrite /= map_id /id /= H_eq in H_inv'.
apply: H_inv' => //.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_adjacent_to_no_incoming_new_n_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        adjacent_to n' n ->
        forall d, odnwState net n = Some d ->
         ~ In New (odnwPackets net n' n) ->
         NSet.In n' (adjacent d).
Proof.
move => net failed tr H_st n n' H_n H_f H_n' H_f' H_adj d H_eq H_in.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_adjacent_to_no_incoming_new_n_adjacent _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f H_n' H_f' H_adj {| FR.adjacent := d.(adjacent) |}.
apply: H_inv'' => //.
move => H_in'.
case: H_in.
apply: in_pt_map_msgs_in_msg => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_incoming_fail_then_incoming_new_or_in_adjacent : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
      (In New (net.(odnwPackets) n' n) /\ ~ NSet.In n' d.(adjacent)) \/ (~ In New (net.(odnwPackets) n' n) /\ NSet.In n' d.(adjacent)).
Proof.
move => net failed tr H_st n H_n H_f n' H_in d H_eq. 
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_incoming_fail_then_incoming_new_or_in_adjacent _ _ _ H_st' n.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f n' _ {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _).
move: H_inv''.
set f_in := In FR.Fail _.
move => H_inv''.
suff H_suff: f_in.
  concludes.
  case: H_inv'' => H_inv''.
    break_and.
    left.
    split => //.
    move: H.
    apply: in_pt_map_msgs_in_msg => //.
    exact: Aggregation_pt_map_msg_injective.
  break_and.
  right.
  split => //.
  move => H_in'.
  case: H.
  move: H_in'.
  exact: in_msg_pt_map_msgs.
rewrite /f_in.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_incoming_fail_then_new_or_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
       In New (net.(odnwPackets) n' n) \/ NSet.In n' (adjacent d).
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f n' H_in d H_eq.
have H_or := Aggregation_incoming_fail_then_incoming_new_or_in_adjacent H_st _ H_in_n H_in_f _ H_in H_eq.
break_or_hyp; break_and; first by left.
by right.
Qed.

Lemma Aggregation_head_fail_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', head (net.(odnwPackets) n' n) = Some Fail ->
   forall d, net.(odnwState) n = Some d -> 
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f n' H_eq d H_eq'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_head_fail_then_adjacent _ _ _ H_st' n.
rewrite /= map_id /id /= H_eq' in H_inv'.
have H_inv'' := H_inv' H_n H_f n' _ {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _).
apply: H_inv''.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Aggregation_adjacent_or_incoming_new_reciprocal :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        forall d0, odnwState net n = Some d0 ->
        forall d1, odnwState net n' = Some d1 ->
        (NSet.In n' d0.(adjacent) \/ In New (net.(odnwPackets) n' n)) ->
        NSet.In n d1.(adjacent) \/ In New (net.(odnwPackets) n n').
Proof.
move => net failed tr H_st n n' H_n H_f H_n' H_f' d H_eq d' H_eq'.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_adjacent_or_incoming_new_reciprocal _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq H_eq' in H_inv'.
have H_inv'' := H_inv' H_n H_f H_n' H_f' {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _) {| FR.adjacent := d'.(adjacent) |} (Logic.eq_refl _).
rewrite /= in H_inv''.
move => H_in.
move: H_inv''.
set inn := In FR.New _.
set inn' := In FR.New _.
move => H_inv''.
case: H_in => H_in.
  have H_or: NSet.In n' d.(adjacent) \/ inn by left.
  concludes.
  case: H_inv'' => H_inv''; first by left.
  right.
  move: H_inv''.
  apply: in_pt_map_msgs_in_msg => //.
  exact: Aggregation_pt_map_msg_injective.
suff H_suff: inn.
  have H_or: NSet.In n' (adjacent d) \/ inn by right.
  concludes.
  case: H_inv'' => H_inv''; first by left.
  right.
  move: H_inv''.
  apply: in_pt_map_msgs_in_msg => //.
  exact: Aggregation_pt_map_msg_injective.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_adjacent_then_adjacent_or_new_incoming :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n n', 
        In n net.(odnwNodes) -> ~ In n failed ->
        In n' net.(odnwNodes) -> ~ In n' failed ->
        forall d0, odnwState net n = Some d0 ->
        forall d1, odnwState net n' = Some d1 ->
        NSet.In n' d0.(adjacent) ->
        NSet.In n d1.(adjacent) \/ In New (net.(odnwPackets) n n').
Proof.
move => net failed tr H_st n n' H_n H_f H_n' H_f' d H_eq d' H_eq' H_ins.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_adjacent_then_adjacent_or_new_incoming _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq H_eq' in H_inv'.
have H_inv'' := H_inv' H_n H_f H_n' H_f' {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _) {| FR.adjacent := d'.(adjacent) |} (Logic.eq_refl _).
rewrite /= in H_inv''.
concludes.
break_or_hyp; first by left.
right.
move: H.
apply: in_pt_map_msgs_in_msg => //.
exact: Aggregation_pt_map_msg_injective.
Qed.

Lemma Aggregation_fail_head_no_new :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
        forall n', head (net.(odnwPackets) n' n) = Some Fail ->
        ~ In New (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_fail_head_no_new _ _ _ H_st' n.
rewrite /= map_id /id /= in H_inv'.
have H_inv'' := H_inv' H_n H_f n'.
move => H_in.
move: H_inv''.
set hde := hd_error _ = _.
move => H_inv''.
suff H_suff: hde.
  concludes.
  case: H_inv''.
  move: H_in.
  exact: in_msg_pt_map_msgs.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Aggregation_failed_adjacent_fail :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In n' failed ->
      forall d0, odnwState net n = Some d0 ->
      (NSet.In n' d0.(adjacent) \/ In New (net.(odnwPackets) n' n)) ->
      In Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_f' d H_eq H_or.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_failed_adjacent_fail _ _ _ H_st' n.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f _ H_f' {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _).
rewrite /= in H_inv''.
move: H_inv''.
set inn := In FR.Fail _.
move => H_inv''.
suff H_suff: inn.
  move: H_suff.
  apply: in_pt_map_msgs_in_msg => //.
  exact: Aggregation_pt_map_msg_injective.
apply: H_inv''.
case: H_or => H_or; first by left.
right.
move: H_or.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_in_new_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In New (odnwPackets net n' n) ->
            adjacent_to n' n.
Proof.
move => net failed tr H_st n H_n H_f n' H_in.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_in_new_then_adjacent _ _ _ H_st' n.
rewrite /= map_id /id /= in H_inv'.
apply: (H_inv' H_n H_f n').
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_inactive_not_in_adjacent :
forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed ->
  forall n', ~ In n' (odnwNodes net) ->
  forall d0, odnwState net n = Some d0 ->
  ~ NSet.In n' d0.(adjacent).
Proof.
move => net failed tr H_st n H_in H_f n' H_n' d0 H_eq.
have H_st' := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FR.Failure_inactive_not_in_adjacent _ _ _ H_st' n _ _ n' _ {| FR.adjacent := d0.(adjacent) |}.
rewrite /= map_id /id /= H_eq /= in H_inv'.
by repeat concludes.
Qed.

Lemma Aggregation_self_channel_empty : 
forall onet failed tr, 
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
 forall n, onet.(odnwPackets) n n = [].
Proof.
move => net failed tr H.
change net with (snd (failed, net)).
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_ordered_failure_init /=.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n.
  case (name_eq_dec h n) => H_dec; last first.
    rewrite collate_ls_neq_to //.
    by rewrite collate_neq.
  find_reverse_rewrite.
  rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
  rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
  by find_higher_order_rewrite.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  rewrite /update2 /=.
  break_if => //=.
  break_and; repeat find_rewrite.
  by have H_not := Aggregation_node_not_adjacent_self H H3 H2 H4.
- move => n.  
  case (name_eq_dec h n) => H_dec; last by rewrite collate_neq; first by find_higher_order_rewrite.
  find_reverse_rewrite.
  rewrite collate_map2snd_not_related //.
  exact: adjacent_to_irreflexive.
Qed.

Lemma Aggregation_inactive_no_incoming :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n' n = [].
Proof.
move => net failed tr H.
change net with (snd (failed, net)).
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in n'.
  have H_neq: h <> n by auto.
  have H_not_in: ~ In n net0.(odnwNodes) by auto.
  rewrite collate_ls_neq_to //.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by auto.
  rewrite collate_neq //.
  by auto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * by auto.
  * rewrite /update2 /=.
    break_if; break_and; last by auto.
    subst_max.
    have H_adj := Aggregation_in_adj_or_incoming_fail H _ H3 H2 H4 H5.
    by break_or_hyp; break_and.
  * by auto.
  * by auto.
  * by auto.
  * by auto.
- move => n H_in n'.
  have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_in.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by auto.
  rewrite collate_neq //.
  by auto.
Qed.

Lemma Aggregation_in_set_exists_find_balance : 
forall net failed tr, 
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall d, net.(odnwState) n = Some d ->
 forall n', NSet.In n' d.(adjacent) -> 
       exists m5 : m, NMap.find n' d.(balance) = Some m5.
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in H_f d.
  rewrite /update.
  break_if => H_eq.
    find_injection.
    unfold InitData in *.
    by find_apply_lem_hyp NSetFacts.empty_1.
  break_or_hyp => //.
  by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update in *; break_if; try by eauto.
  * find_injection.    
    repeat find_rewrite.
    case (name_eq_dec n' from) => H_dec.
      exists (x0 * x^-1).
      by rewrite NMapFacts.add_eq_o.
    have IH := IHrefl_trans_1n_trace1 _ H3 H7 _ H4 _ H9.  
    break_exists_name m'.
    exists m'.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff; auto.
    by apply NMapFacts.find_mapsto_iff.
  * find_injection.
    by eauto.
  * find_injection.
    have H_neq: n' <> from.
      move => H_eq.
      repeat find_rewrite.
      by find_apply_lem_hyp NSetFacts.remove_1.
    repeat find_rewrite.
    find_apply_lem_hyp NSetFacts.remove_3.
    have IH := IHrefl_trans_1n_trace1 _ H3 H7 _ H4 _ H9.
    break_exists_name m'.
    exists m'.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq.
    by apply NMapFacts.find_mapsto_iff.
  * find_injection.
    have H_neq: n' <> from.
      move => H_eq.
      repeat find_rewrite.
      by find_apply_lem_hyp NSetFacts.remove_1.
    repeat find_rewrite.
    find_apply_lem_hyp NSetFacts.remove_3.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    case (name_eq_dec n' from) => H_dec.
      exists 1.
      rewrite H_dec.
      exact: NMapFacts.add_eq_o.
    find_apply_lem_hyp NSetFacts.add_3; last by auto.
    rewrite NMapFacts.add_neq_o; last by auto.
    by eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; unfold update in *; break_if; try by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    case (name_eq_dec n' x) => H_dec.
      rewrite H_dec.
      exists (x0 * d.(aggregate)).
      by rewrite NMapFacts.add_eq_o.
    rewrite NMapFacts.add_neq_o; last by auto.
    by eauto.
  * repeat find_rewrite.
    by eauto.
  * find_injection.
    by eauto.
  * find_injection.
    by eauto.
  * find_injection.
    by eauto.
- by eauto.
Qed.

Lemma Aggregation_in_after_all_fail_aggregate : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall n', In n' net.(odnwNodes) ->
 forall m', before_all (Aggregate m') Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by rewrite (Aggregation_self_channel_empty H).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
    rewrite collate_map2snd_not_in_related //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H) //=.
    by left.
  * have H_neq: n <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming H).
    case (in_dec name_eq_dec n' failed) => H_dec'; last first.      
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
      rewrite collate_ls_live_related //.
      rewrite collate_neq //.
      rewrite (Aggregation_inactive_no_incoming H) //=.
      by left.
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Aggregation_inactive_no_incoming H).
  * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
    have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update2 in *; break_if; break_and; subst_max; try by eauto.
  * have IH := IHrefl_trans_1n_trace1 _ H6 H7 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H15 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H14 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  rewrite /update2.
  break_if; break_and; subst_max; last by eauto.
  apply: before_all_not_in_append.
  exact: (Aggregation_not_failed_no_fail H).
- move => n H_n H_f n' H_n' m'.
  have H_neq: h <> n by auto.
  have H_f': ~ In n failed by auto.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    by eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map2snd_not_related //.
    by eauto.
  rewrite collate_map2snd_not_in_related //.
    apply: before_all_neq_append => //.
    by eauto.
  exact: @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
Qed.

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
  forall net failed tr, 
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) ->
    forall m5, In (Aggregate m5) (net.(odnwPackets) n' n) ->
    forall d, net.(odnwState) n = Some d ->
     In New (net.(odnwPackets) n' n) \/ NSet.In n' d.(adjacent).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4 5 6.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m' H_in d H_eq.
  unfold update in *.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
  break_if.
    find_injection.
    move {H_n}.
    contradict H_in.
    break_or_hyp.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
      rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
      by rewrite (Aggregation_self_channel_empty H).
    have H_neq: h <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec h n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming H).
    case (in_dec name_eq_dec n' failed) => H_dec'.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_not_in.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming H).
    rewrite collate_ls_live_related //.
    rewrite collate_neq //.
    rewrite (Aggregation_inactive_no_incoming H) //=.
    move => H_or.
    by break_or_hyp.
  case: H_n => H_n; first by find_rewrite.
  move: H_in.
  rewrite collate_ls_neq_to; last by auto.
  break_or_hyp; last first.
    have H_neq: h <> n' by move => H_eq'; find_reverse_rewrite.
    rewrite collate_neq //.
    by eauto.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map2snd_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
  rewrite collate_map2snd_not_in_related //.
  rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H) //=.
  by auto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update2, update in *; simpl in *; repeat break_if; break_and; subst_max; try find_injection; try by eauto.
  * have H_in: In (Aggregate x) (odnwPackets net0 n' n) by repeat find_rewrite; left.
    have IH := IHrefl_trans_1n_trace1 _ H6 H7 _ H8 _ H_in _ H4.
    find_rewrite.
    break_or_hyp; last by right; find_reverse_rewrite.
    simpl in *.
    break_or_hyp => //.
    by left.
  * break_or_hyp => //.
    find_rewrite.
    by eauto.
  * have H_in: In (Aggregate x) (odnwPackets net0 n' to) by repeat find_rewrite; left.
    have IH := IHrefl_trans_1n_trace1 _ H0 H7 _ H8 _ H_in _ H4.
    find_rewrite.
    break_or_hyp; last by right.
    simpl in *.
    break_or_hyp => //.
    by left.
  * contradict H9.
    have H_bef := Aggregation_in_after_all_fail_aggregate H _ H6 H2 _ H8 m5.
    find_rewrite.
    simpl in *.
    break_or_hyp => //.
    by break_and.
  * break_or_hyp => //.
    find_rewrite.
    have IH := IHrefl_trans_1n_trace1 _ H6 H7 _ H8 _ H9 _ H4.
    break_or_hyp; first by left.
    right.
    exact: NSetFacts.remove_2.
  * contradict H16.
    have H_bef := Aggregation_in_after_all_fail_aggregate H _ H12 H2 _ H15 m5.
    find_rewrite.
    simpl in *.
    break_or_hyp => //.
    by break_and.
  * find_rewrite.
    break_or_hyp => //.
    have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H15 _ H16 _ H4.
    break_or_hyp; first by left.
    right.
    exact: NSetFacts.remove_2.
  * find_rewrite.
    right.
    exact: NSetFacts.add_1.
  * break_or_hyp => //.
    find_rewrite.
    have IH := IHrefl_trans_1n_trace1 _ H11 H13 _ H14 _ H15 _ H4.
    break_or_hyp; first by left.
    right.
    exact: NSetFacts.add_2.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; unfold update in *; simpl in *; break_if; break_and; subst_max; try find_injection; try by eauto.
  * find_rewrite.
    by eauto.
  * unfold update2 in *.
    by break_if; break_and; repeat find_rewrite; eauto.
  * unfold update2 in *.
    break_if; break_and; subst_max; last by eauto.
    have H_adj := Aggregation_adjacent_then_adjacent_or_new_incoming H _ H3 H2 H0 H6 H4 H9 H5.
    break_or_hyp; first by right.
    left.
    apply in_or_app.
    by left.
- move => n H_n H_f n' H_n' m' H_in d H_eq.
  have H_neq: h <> n by auto.
  have H_f': ~ In n failed by auto.
  case (name_eq_dec h n') => H_dec; last first.
    move: H_in.
    rewrite collate_neq //.
    by eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec; last first.
    move: H_in.
    rewrite collate_map2snd_not_related //.
    by eauto.
  move: H_in.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
  rewrite collate_map2snd_not_in_related //.
  move => H_in.
  find_apply_lem_hyp in_app_or.
  break_or_hyp; last by simpl in *; break_or_hyp.
  suff H_suff: In New (odnwPackets net0 n' n) \/ NSet.In n' (adjacent d); last by eauto.
  break_or_hyp; last by right.
  left.
  apply in_or_app.
  by left.
Qed.

Lemma Aggregation_in_after_all_aggregate_new : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall n', In n' net.(odnwNodes) ->
 forall m', before_all New (Aggregate m') (net.(odnwPackets) n' n).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by rewrite (Aggregation_self_channel_empty H).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
    rewrite collate_map2snd_not_in_related //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H) //=.
    by left.
  * have H_neq: n <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming H).
    case (in_dec name_eq_dec n' failed) => H_dec'; last first.      
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
      rewrite collate_ls_live_related //.
      rewrite collate_neq //.
      rewrite (Aggregation_inactive_no_incoming H) //=.
      by left.
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Aggregation_inactive_no_incoming H).
  * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
    have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update2 in *; break_if; break_and; subst_max; try find_injection; try by eauto.
  * have IH := IHrefl_trans_1n_trace1 _ H6 H7 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H15 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H14 m'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in.
    by break_and.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  rewrite /update2.
  break_if; break_and; subst_max; last by eauto.  
  apply: before_all_neq_append => //.
  by eauto.
- move => n H_n H_f n' H_n' m'.
  have H_neq: h <> n by auto.
  have H_f': ~ In n failed by auto.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    by eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map2snd_not_related //.
    by eauto.
  rewrite collate_map2snd_not_in_related //.
    apply: before_all_neq_append => //.
    by eauto.
  exact: @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
Qed.

Lemma Aggregation_aggregate_head_in_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n' m', head (net.(odnwPackets) n' n) = Some (Aggregate m') ->
   forall d, net.(odnwState) n = Some d ->
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f n' m' H_eq d H_eq'.
case (in_dec name_eq_dec n' net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H_st) in H_eq.
have H_in: In (Aggregate m') (odnwPackets net n' n).
  destruct (odnwPackets net n' n) => //.
  simpl in *.
  find_injection.
  by left.
have H_in' := Aggregation_aggregate_msg_dst_adjacent_src H_st _ H_n H_f _ H_dec _ H_in H_eq'.
break_or_hyp => //.
contradict H.
have H_bef := Aggregation_in_after_all_aggregate_new H_st _ H_n H_f _ H_dec m'.
destruct (odnwPackets net n' n) => //.
simpl in *.
find_injection.
move => H_in'.
break_or_hyp => //.
break_or_hyp => //.
by break_and.
Qed.

Instance Aggregation_Aggregator_multi_single_map : MultiSingleParamsTotalMap Aggregation_MultiParams OA.Aggregator_BaseParams := 
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
                        | New => OA.New src
                        | Aggregate m_msg => OA.Aggregate src m_msg
                        end
  }.

Instance Aggregation_Aggregator_congr (n : name) : MultiSingleParamsTotalMapCongruency OA.Aggregator_SingleParams Aggregation_Aggregator_multi_single_map n :=
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

Lemma Aggregation_step_ordered_dynamic_failure_tot_one_mapped_simulation_star_1 :
  forall n net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall d, net.(odnwState) n = Some d ->
    exists tr', @step_s_star _ OA.Aggregator_SingleParams (@init_handler _ OA.Aggregator_SingleParams) (tot_s_map_data d) tr'.
Proof.
move => n.
apply: step_ordered_dynamic_failure_tot_one_mapped_simulation_star_1.
move => net failed tr src mg ms d out st' ps out' st'' H_star H_eq H_in_f H_eq' H_hnd H_inp.
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
  case (in_dec name_eq_dec x2 net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) in H_eq.
  have H_in: In (Aggregate x1) (odnwPackets net x2 n) by find_rewrite; left.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.      
  have H_or := Aggregation_aggregate_msg_dst_adjacent_src H_star _ H_dec' H_in_f _ H_dec _ H_in H_eq'.
  break_or_hyp => //.
  have H_bef := Aggregation_in_after_all_aggregate_new H_star _ H_dec' H_in_f _ H_dec x1.
  repeat find_rewrite.
  simpl in *.
  break_or_hyp; break_or_hyp => //.
  by break_and.
* case: H0.
  have H_hd: head (odnwPackets net x0 n) = Some Fail by find_rewrite.
  apply: (Aggregation_head_fail_then_adjacent H_star _ _ _ _ H_hd) => //.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec' //.
  have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
  by congruence.
* case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  have [m' H_m] := Aggregation_in_set_exists_find_balance H_star _ H_dec' H_in_f H_eq' H.
  by congruence.
* case: H.
  have H_hd: head (odnwPackets net x n) = Some Fail by find_rewrite.
  apply: (Aggregation_head_fail_then_adjacent H_star _ _ _ _ H_hd) => //=.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec' //.
  have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
  by congruence.
* have H_in: In New (odnwPackets net x n) by find_rewrite; left.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  by have H_ins := Aggregation_new_incoming_not_in_adj H_star _ H_dec' H_in_f H_in H_eq'.
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
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n d, net.(odnwState) n = Some d ->
      conserves_node_mass d.
Proof.
move => onet failed tr H n d H_eq.
have H_st := Aggregation_step_ordered_dynamic_failure_tot_one_mapped_simulation_star_1 _ H H_eq.
move: H_st => [tr' H_st].
apply OA.Aggregator_conserves_node_mass in H_st.
by rewrite /= /conserves_node_mass /= in H_st.
Qed.

Lemma Aggregation_non_failed_or_incoming_fail : 
  forall net failed tr, 
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n' m5, In (Aggregate m5) (net.(odnwPackets) n' n) ->
    (In n' net.(odnwNodes) /\ ~ In n' failed) \/ (In Fail (net.(odnwPackets) n' n)).
Proof.
move => net failed tr H_st n H_n H_f n' m' H_in.
case (in_dec name_eq_dec n' net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H_st) in H_in.
case (in_dec name_eq_dec n' failed) => H_dec'; last by left; split.
right.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
have H_or := Aggregation_aggregate_msg_dst_adjacent_src H_st _ H_n H_f _ H_dec _ H_in H_d.
break_or_hyp; first exact: (Aggregation_in_new_failed_incoming_fail H_st).
have H_adj := Aggregation_in_adj_or_incoming_fail H_st _ H_n H_f H_d H.
by break_or_hyp; break_and.
Qed.

Section SingleNodeInvIn.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis after_init_new :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  ~ In n onet.(odnwNodes) ->
  In n' onet.(odnwNodes) ->
  ~ In n' failed ->
  adjacent_to n' n ->  
  P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  ~ In n' onet.(odnwNodes) ->  
  adjacent_to n' n ->  
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms m0,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  In n' failed ->
  n' <> n ->
  adjacent_to n' n ->
  onet.(odnwPackets) n' n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  NMap.find n' d.(balance) = Some m0 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m0 ;
       adjacent := NSet.remove n' d.(adjacent) ;
       balance := NMap.remove n' d.(balance)
    |} ms.

Hypothesis recv_fail_from_neq :
  forall onet failed tr from ms m0,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  In from failed ->
  from <> n ->
  from <> n' ->
  adjacent_to from n ->
  onet.(odnwPackets) from n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  NMap.find from d.(balance) = Some m0 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m0 ;
       adjacent := NSet.remove from d.(adjacent) ;
       balance := NMap.remove from d.(balance)
    |} (onet.(odnwPackets) n' n).

Hypothesis recv_new_from_eq :
  forall onet failed tr ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n' <> n ->
  adjacent_to n' n ->
  onet.(odnwPackets) n' n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) ;
       adjacent := NSet.add n' d.(adjacent) ;
       balance := NMap.add n' 1 d.(balance)
    |} ms.

Hypothesis recv_new_from_neq :
  forall onet failed tr from ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  from <> n ->
  from <> n' ->
  adjacent_to from n ->
  onet.(odnwPackets) from n = New :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) ;       
       adjacent := NSet.add from d.(adjacent) ;
       balance := NMap.add from 1 d.(balance)
     |} (onet.(odnwPackets) n' n).

Hypothesis recv_aggregate_eq : 
  forall onet failed tr m' m0 ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n <> n' ->
  adjacent_to n' n ->
  onet.(odnwPackets) n' n = Aggregate m' :: ms ->
  forall d, onet.(odnwState) n = Some d -> 
  NMap.find n' d.(balance) = Some m0 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m' ;
       adjacent := d.(adjacent) ;
       balance := NMap.add n' (m0 * (m')^-1) d.(balance)
    |} ms.

Hypothesis recv_aggregate_other : 
  forall onet failed tr m' from m0 ms,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  from <> n ->
  from <> n' ->
  adjacent_to from n ->
  onet.(odnwPackets) from n = Aggregate m' :: ms ->
  forall d, onet.(odnwState) n = Some d -> 
  NMap.find from d.(balance) = Some m0 ->  
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m' ;
       adjacent := d.(adjacent) ;
       balance := NMap.add from (m0 * (m')^-1) d.(balance)
    |} (onet.(odnwPackets) n' n).

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    forall d, onet.(odnwState) n = Some d -> 
    P d (onet.(odnwPackets) n' n) ->
    P {| local := m_local ;
         aggregate := d.(aggregate) * m_local * d.(local)^-1 ;
         adjacent := d.(adjacent) ;
         balance := d.(balance)
      |} (onet.(odnwPackets) n' n).

Hypothesis send_fail : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    In n' onet.(odnwNodes) ->
    ~ In n' failed ->
    adjacent_to n' n ->
    n' <> n ->    
    forall d, onet.(odnwState) n = Some d ->
     P d (onet.(odnwPackets) n' n) ->
     P d (odnwPackets onet n' n ++ [Fail]).

Hypothesis recv_send_aggregate : 
  forall onet failed tr m',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    In n' onet.(odnwNodes) ->
    n <> n' ->
    adjacent_to n' n ->
    forall d, onet.(odnwState) n = Some d ->
    NSet.In n' d.(adjacent) ->
    d.(aggregate) <> 1 ->
    NMap.find n' d.(balance) = Some m' ->
    P d (onet.(odnwPackets) n' n) ->
    P {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         balance := NMap.add n' (m' * d.(aggregate)) d.(balance)
      |} (onet.(odnwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet failed tr to m',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    to <> n ->
    to <> n' ->
    In to onet.(odnwNodes) ->
    adjacent_to to n ->
    forall d, onet.(odnwState) n = Some d ->
    NSet.In to d.(adjacent) ->
    d.(aggregate) <> 1 ->
    NMap.find to d.(balance) = Some m' ->
    P d (onet.(odnwPackets) n' n) ->
    P {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         balance := NMap.add to (m' * d.(aggregate)) d.(balance)
        |} (onet.(odnwPackets) n' n).

Hypothesis recv_send_aggregate_sender :
  forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  ~ In n' failed ->
  n <> n' ->
  adjacent_to n' n ->
  forall d, onet.(odnwState) n = Some d ->
  forall d', onet.(odnwState) n' = Some d' ->
  d'.(aggregate) <> 1 ->
  NSet.In n d'.(adjacent) ->
  P d (onet.(odnwPackets) n' n) ->
  P d (onet.(odnwPackets) n' n ++ [Aggregate d'.(aggregate)]).

Theorem P_inv_n_in : forall d, onet.(odnwState) n = Some d -> P d (onet.(odnwPackets) n' n).
Proof.
move: onet failed tr H_step active not_failed.
clear onet failed tr H_step active not_failed.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 3 4}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init /step_ordered_dynamic_failure_init /= => H_in_f.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => H_a H_f d.
  rewrite /update /=.
  case name_eq_dec => H_dec H_eq.
    repeat find_rewrite.
    find_injection.
    case (name_eq_dec h n') => H_dec.
      repeat find_reverse_rewrite.
      rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
      rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
      by rewrite (Aggregation_self_channel_empty s1).
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_ls_not_in_related; last by eauto using in_remove_all_was_in.
      rewrite collate_neq //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_ls_in_remove_all //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming s1).
    case (adjacent_to_dec h n') => H_dec'; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming s1).
    rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite collate_neq //.
    rewrite (Aggregation_inactive_no_incoming s1) //=.
    apply adjacent_to_symmetric in H_dec'.
    apply: (after_init_new s1) => //.
  have H_neq: h <> n by auto.
  rewrite collate_ls_neq_to //.
  break_or_hyp => //.
  case (name_eq_dec h n') => H_dec'; last by rewrite collate_neq //; exact: IHs1.
  rewrite -H_dec'.
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_map2snd_not_related //; rewrite H_dec'; exact: IHs1.
  rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
  have IH := IHs1 H H_f _ H_eq.
  move: IH.
  rewrite -H_dec'.
  rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) //=.
  rewrite H_dec' in H0 H_adj.
  exact: (after_adjacent s1).
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * case (in_dec name_eq_dec from (odnwNodes net)) => H_from_nodes; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
    have H_neq: from <> to by move => H_eq; rewrite H_eq (Aggregation_self_channel_empty s1) in H3.
    move: H4.
    rewrite /update.
    break_if => H_eq.
      find_injection.
      destruct d0.
      simpl in *.
      rewrite H7 H8 H9 H10.
      rewrite /update2.
      break_if.
        break_and.
        subst_max.
        apply: (recv_aggregate_eq s1) => //; try by eauto.
        have H_hd: head (odnwPackets net n' to) = Some (Aggregate x) by rewrite H3.
        have H_ins := Aggregation_aggregate_head_in_adjacent s1 _ H1 H0 _ H_hd H2.
        exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_ins).
      break_or_hyp => //.
      apply (@recv_aggregate_other _ _ _ _  _ _ ms s1) => //; try by eauto.
      have H_hd: head (odnwPackets net from to) = Some (Aggregate x) by repeat find_rewrite.        
      have H_ins := Aggregation_aggregate_head_in_adjacent s1 _ H1 H0 _ H_hd H2.
      exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_ins).
    rewrite /update2.
    break_if; first by break_and; find_rewrite.
    exact: H5.
  * have H_in: In (Aggregate x) (odnwPackets net from to) by find_rewrite; left.
    case (in_dec name_eq_dec from net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.          
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src s1 _ H1 H0 _ H_dec _ H_in H2.
    break_or_hyp; last first.
      have [m' H_rcd] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H6.
      by congruence.
    have H_bef := Aggregation_in_after_all_aggregate_new s1 _ H1 H0 _ H_dec x.
    repeat find_rewrite.
    simpl in *.
    break_or_hyp; break_or_hyp => //.
    by break_and.
  * have H_neq: from <> to.
      move => H_eq.
      find_rewrite.
      by rewrite (Aggregation_self_channel_empty s1) in H3.
    case (in_dec name_eq_dec from net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
    case (in_dec name_eq_dec from failed0) => H_dec'; last first.
      have H_in := Aggregation_not_failed_no_fail s1 _ H_dec H_dec' to.
      find_rewrite.
      by case: H_in; left.
    unfold update2, update in *.
    destruct d0.
    have H_hd: head (odnwPackets net from to) = Some Fail by repeat find_rewrite.
    repeat break_if; break_and; try find_injection; simpl in *; subst_max; try by eauto.
      apply (recv_fail_from_eq s1) => //; last by eauto.
      have H_adj := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
      exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_adj).
    break_or_hyp => //.
    apply: (@recv_fail_from_neq _ _ _ _ ms _ s1) => //; last by eauto.
    have H_adj := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_adj).
  * have H_hd: head (odnwPackets net from to) = Some Fail by find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    have [m' H_rcd] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H_ins.
    by congruence.
  * have H_neq: from <> to.
      move => H_eq.
      find_rewrite.
      by rewrite (Aggregation_self_channel_empty s1) in H3.
    case (in_dec name_eq_dec from net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
    unfold update2, update in *.
    destruct d0.
    have H_in: In New (odnwPackets net from to) by repeat find_rewrite; left.
    have H_adj := Aggregation_in_new_then_adjacent s1 _ H1 H0 _ H_in.
    repeat break_if; break_and; try find_injection; simpl in *; subst_max; try by eauto.    
    break_or_hyp => //.
    by eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * unfold update in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update2, update in *.
    destruct d0.
    repeat break_if; break_and; try find_injection; simpl in *; subst_max; try by eauto.
    + by have H_adj := Aggregation_node_not_adjacent_self s1 H1 H0 H2.
    + have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H3.
      apply adjacent_to_symmetric in H_adj.
      by eauto.
    + have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H3.
      have H_neq: x <> h by move => H_eq; find_rewrite; find_apply_lem_hyp adjacent_to_irreflexive.
      case (name_eq_dec x n') => H_dec.
        subst_max.
        case (in_dec name_eq_dec n' net.(odnwNodes)) => H_dec; last first.
          have H_or := Aggregation_in_adj_or_incoming_fail s1 _ H1 H0 H2 H3.
          by break_or_hyp; break_and.
        by eauto.
      case (in_dec name_eq_dec x net.(odnwNodes)) => H_dec'; last first.
        have H_or := Aggregation_in_adj_or_incoming_fail s1 _ H1 H0 H2 H3.
        by break_or_hyp; break_and.
      by eauto.
  * have [m' H_rcd] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H.
    by congruence.
  * unfold update in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
- move => H_n H_f d H_eq.
  have H_neq: h <> n by auto.
  have H_in: ~ In n failed0 by auto.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    by auto.
  subst_max.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ s1.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map2snd_not_related //.
    by auto.
  rewrite collate_map2snd_not_in_related //.
  by eauto.
Qed.

End SingleNodeInvIn.

Lemma Aggregation_not_adjacent_no_incoming : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
    forall n, In n (odnwNodes onet) -> ~ In n failed ->
         forall n', ~ adjacent_to n n' ->
               onet.(odnwPackets) n' n = [].
Proof.
move => net failed tr H_st.
move => n H_n H_f n'.
have [d H_d] := ordered_dynamic_initialized_state H_st _ H_n.
pose P_curr (d : Data) (l : list Msg) :=
   ~ adjacent_to n n' -> l = [].
rewrite -/(P_curr d _).
move: H_d; generalize d => {d}.
by apply: (P_inv_n_in H_st); rewrite /P_curr //= {P_curr net tr H_st H_n failed H_f}; by intuition by (find_apply_lem_hyp adjacent_to_symmetric).
Qed.

Section DualNodeInv.

Variable onet : ordered_dynamic_network.

Variable failed : list name.

Variable tr : list (name * (input + output)).

Hypothesis H_step : step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr.

Variables n n' : name.

Hypothesis active_n : In n (odnwNodes onet).

Hypothesis active_n' : In n' (odnwNodes onet).

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

Hypothesis after_init : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    n' = n ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    P (InitData n) (InitData n) [] [].

Hypothesis after_init_fst_not_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    ~ adjacent_to n n' ->
    forall d, onet.(odnwState) n' = Some d ->
    P (InitData n) d [] [].

Hypothesis after_init_snd_not_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
     In n (odnwNodes onet) -> 
     ~ In n failed ->
     ~ In n' (odnwNodes onet) ->
     ~ In n' failed ->
     n' <> n ->
     ~ adjacent_to n n' ->
     forall d, onet.(odnwState) n = Some d ->
     P d (InitData n') [] [].

Hypothesis after_init_fst_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n n' ->
    forall d, onet.(odnwState) n' = Some d ->
    P (InitData n) d [New] [New].

Hypothesis after_init_snd_adjacent :
   forall onet failed tr,
     step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
     In n (odnwNodes onet) -> 
    ~ In n failed ->
    ~ In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n n' ->
    forall d, onet.(odnwState) n = Some d ->
    P d (InitData n') [New] [New].

Hypothesis recv_fail_self :
  forall onet failed tr from ms m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    In from failed ->
    from <> n ->    
    adjacent_to from n ->
    onet.(odnwPackets) from n = Fail :: ms ->
    forall d, onet.(odnwState) n = Some d ->
    NMap.find from d.(balance) = Some m0 ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| local := d.(local) ;
         aggregate := d.(aggregate) * m0 ;
         adjacent := NSet.remove from d.(adjacent) ;
         balance := NMap.remove from d.(balance)
      |} 
      {| local := d.(local) ;
         aggregate := d.(aggregate) * m0 ;
         adjacent := NSet.remove from d.(adjacent) ;
         balance := NMap.remove from d.(balance)
      |} 
      [] [].

Hypothesis recv_fail_other_fst :
  forall onet failed tr from ms m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    from <> n ->
    from <> n' ->
    In from (odnwNodes onet) ->
    In from failed ->
    adjacent_to from n ->
    onet.(odnwPackets) from n = Fail :: ms ->    
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find from d0.(balance) = Some m0 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := d0.(local) ;
         aggregate := d0.(aggregate) * m0 ;
         adjacent := NSet.remove from d0.(adjacent) ;
         balance := NMap.remove from d0.(balance)
       |} d1
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_fail_other_snd :
  forall onet failed tr from ms m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    from <> n ->
    from <> n' ->
    In from (odnwNodes onet) ->
    In from failed ->
    adjacent_to from n' ->
    onet.(odnwPackets) from n' = Fail :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find from d1.(balance) = Some m0 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 
      {| local := d1.(local) ;
         aggregate := d1.(aggregate) * m0 ;
         adjacent := NSet.remove from d1.(adjacent) ;
         balance := NMap.remove from d1.(balance)
      |}
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_new_self :
  forall onet failed tr from ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    from <> n ->
    adjacent_to from n ->
    onet.(odnwPackets) from n = New :: ms ->
    forall d, onet.(odnwState) n = Some d ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| local := d.(local) ;
         aggregate := d.(aggregate) ;
         adjacent := NSet.add from d.(adjacent) ;
         balance := NMap.add from 1 d.(balance)
      |}
      {| local := d.(local) ;
         aggregate := d.(aggregate) ;
         adjacent := NSet.add from d.(adjacent) ;
         balance := NMap.add from 1 d.(balance)
      |}
      [] [].

Hypothesis recv_new_fst :
  forall onet failed tr ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n' n = New :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := d0.(local) ;
         aggregate := d0.(aggregate) ;
         adjacent := NSet.add n' d0.(adjacent) ;
         balance := NMap.add n' 1 d0.(balance)
      |} 
      d1
      (odnwPackets onet n n') ms.

Hypothesis recv_new_snd :
  forall onet failed tr ms,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n n' = New :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| local := d1.(local) ;
            aggregate := d1.(aggregate) ;
            adjacent := NSet.add n d1.(adjacent) ;
            balance := NMap.add n 1 d1.(balance)
         |}
      ms (odnwPackets onet n' n).

Hypothesis recv_new_fst_other :
  forall onet failed tr from ms,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n ->
   onet.(odnwPackets) from n = New :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P {| local := d0.(local) ; 
        aggregate := d0.(aggregate) ;
        adjacent := NSet.add from d0.(adjacent) ;
        balance := NMap.add from 1 d0.(balance)
     |} d1 (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_new_snd_other :
  forall onet failed tr from ms,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n' ->
   onet.(odnwPackets) from n' = New :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P d0 {| local := d1.(local) ;
           aggregate := d1.(aggregate) ;
           adjacent := NSet.add from d1.(adjacent) ;
           balance := NMap.add from 1 d1.(balance)
        |} (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_aggregate_self :
  forall onet failed tr from ms m0 m',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    from <> n ->
    adjacent_to from n ->
    onet.(odnwPackets) from n = Aggregate m' :: ms ->    
    forall d, onet.(odnwState) n = Some d ->
    NMap.find from d.(balance) = Some m0 ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| local := d.(local) ;
         aggregate := d.(aggregate) * m' ;
         adjacent := d.(adjacent) ;
         balance := NMap.add from (m0 * (m')^-1) d.(balance)
      |}
      {| local := d.(local) ;
         aggregate := d.(aggregate) * m' ;
         adjacent := d.(adjacent) ;
         balance := NMap.add from (m0 * (m')^-1) d.(balance)
      |}
      [] [].

Hypothesis recv_aggregate_fst :
  forall onet failed tr ms m0 m',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n' n = Aggregate m' :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find n' d0.(balance) = Some m0 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := d0.(local) ;
         aggregate := d0.(aggregate) * m' ;
         adjacent := d0.(adjacent) ;
         balance := NMap.add n' (m0 * (m')^-1) d0.(balance)
      |} d1 (odnwPackets onet n n') ms.

Hypothesis recv_aggregate_snd :
  forall onet failed tr ms m0 m',
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    onet.(odnwPackets) n n' = Aggregate m' :: ms ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find n d1.(balance) = Some m0 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| local := d1.(local) ;
            aggregate := d1.(aggregate) * m' ;
            adjacent := d1.(adjacent) ;
            balance := NMap.add n (m0 * (m')^-1) d1.(balance)
         |} ms (odnwPackets onet n' n).

Hypothesis recv_aggregate_fst_other :
  forall onet failed tr from ms m0 m',
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n ->
   onet.(odnwPackets) from n = Aggregate m' :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   NMap.find from d0.(balance) = Some m0 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P {| local := d0.(local) ; 
        aggregate := d0.(aggregate) * m' ;
        adjacent := d0.(adjacent) ;
        balance := NMap.add from (m0 * (m')^-1) d0.(balance)
     |} d1 (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_aggregate_snd_other :
  forall onet failed tr from ms m0 m',
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   from <> n ->
   from <> n' ->
   In from (odnwNodes onet) ->
   adjacent_to from n' ->
   onet.(odnwPackets) from n' = Aggregate m' :: ms ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   NMap.find from d1.(balance) = Some m0 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P d0 {| local := d1.(local) ;
           aggregate := d1.(aggregate) * m' ;
           adjacent := d1.(adjacent) ;
           balance := NMap.add from (m0 * (m')^-1) d1.(balance)
        |} (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_local_self : 
  forall onet failed tr m_local,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    forall d, onet.(odnwState) n = Some d ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| local := m_local ;
         aggregate := d.(aggregate) * m_local * d.(local)^-1 ;
         adjacent := d.(adjacent) ;
         balance := d.(balance)
      |}
      {| local := m_local ;
         aggregate := d.(aggregate) * m_local * d.(local)^-1 ;
         adjacent := d.(adjacent) ;
         balance := d.(balance)
      |}
      [] [].

Hypothesis recv_local_fst :
  forall onet failed tr m_local,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := m_local ;
         aggregate := d0.(aggregate) * m_local * d0.(local)^-1 ;
         adjacent := d0.(adjacent) ;
         balance := d0.(balance)
      |} d1 (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_local_snd :
  forall onet failed tr m_local,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| local := m_local ;
            aggregate := d1.(aggregate) * m_local * d1.(local)^-1 ;
            adjacent := d1.(adjacent) ;
            balance := d1.(balance)
         |} (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis send_aggregate_self :
  forall onet failed tr to m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In to onet.(odnwNodes) ->
    to <> n ->
    adjacent_to to n ->
    forall d, onet.(odnwState) n = Some d ->
    NMap.find to d.(balance) = Some m0 ->
    NSet.In to d.(adjacent) ->
    d.(aggregate) <> 1 ->
    P d d (odnwPackets onet n n) (odnwPackets onet n n) ->
    P {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         balance := NMap.add to (m0 * d.(aggregate)) d.(balance)
      |} 
      {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         balance := NMap.add to (m0 * d.(aggregate)) d.(balance)
      |} [] [].

Hypothesis send_aggregate_fst :
  forall onet failed tr m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find n' d0.(balance) = Some m0 ->
    NSet.In n' d0.(adjacent) ->
    d0.(aggregate) <> 1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := d0.(local) ;
         aggregate := 1 ;
         adjacent := d0.(adjacent) ;
         balance := NMap.add n' (m0 * d0.(aggregate)) d0.(balance)
      |} d1 (odnwPackets onet n n' ++ [Aggregate d0.(aggregate)]) (odnwPackets onet n' n).

Hypothesis send_aggregate_snd :
  forall onet failed tr m0,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n' n ->    
    forall d0, onet.(odnwState) n = Some d0 ->
    forall d1, onet.(odnwState) n' = Some d1 ->
    NMap.find n d1.(balance) = Some m0 ->
    NSet.In n d1.(adjacent) ->
    d1.(aggregate) <> 1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 {| local := d1.(local) ;
            aggregate := 1 ;
            adjacent := d1.(adjacent) ;
            balance := NMap.add n (m0 * d1.(aggregate)) d1.(balance)
         |} (odnwPackets onet n n') (odnwPackets onet n' n ++ [Aggregate d1.(aggregate)]).

Hypothesis send_aggregate_fst_other :
  forall onet failed tr to m0,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   to <> n ->
   to <> n' ->
   In to (odnwNodes onet) ->
   adjacent_to to n ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   NMap.find to d0.(balance) = Some m0 ->
   NSet.In to d0.(adjacent) ->
   d0.(aggregate) <> 1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P {| local := d0.(local) ; 
        aggregate := 1 ;
        adjacent := d0.(adjacent) ;
        balance := NMap.add to (m0 * d0.(aggregate)) d0.(balance)
     |} d1 (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis send_aggregate_snd_other :
  forall onet failed tr to m0,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
   In n (odnwNodes onet) -> 
   ~ In n failed ->
   In n' (odnwNodes onet) ->
   ~ In n' failed ->  
   n' <> n ->
   to <> n ->
   to <> n' ->
   In to (odnwNodes onet) ->
   adjacent_to to n' ->
   forall d0, onet.(odnwState) n = Some d0 ->
   forall d1, onet.(odnwState) n' = Some d1 ->
   NMap.find to d1.(balance) = Some m0 ->
   NSet.In to d1.(adjacent) ->
   d1.(aggregate) <> 1 ->
   P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
   P d0 {| local := d1.(local) ;
           aggregate := 1 ;
           adjacent := d1.(adjacent) ;
           balance := NMap.add to (m0 * d1.(aggregate)) d1.(balance)
        |} (odnwPackets onet n n') (odnwPackets onet n' n).

Theorem P_dual_inv : 
  forall d0, onet.(odnwState) n = Some d0 -> 
  forall d1, onet.(odnwState) n' = Some d1 -> 
  P d0 d1 (onet.(odnwPackets) n n') (onet.(odnwPackets) n' n).
Proof.
move: onet failed tr H_step active_n active_n' not_failed_n not_failed_n'.
clear onet failed tr H_step active_n active_n' not_failed_n not_failed_n'.
move => onet failed tr H_step.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {1 2 5 6 7 8}H_eq_o {H_eq_o}.
remember step_ordered_dynamic_failure_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => /= H_init; first by rewrite H_init.
repeat concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_n H_in_n' H_in_f H_in_f'.  
  rewrite /update.
  break_if; break_if.
  * move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    rewrite collate_ls_not_related; last exact: adjacent_to_irreflexive.
    rewrite collate_map2snd_not_related; last exact: adjacent_to_irreflexive.
    rewrite (Aggregation_self_channel_empty s1).
    exact: (after_init s1).
  * case: H_in_n' => H_in_n'; first by find_rewrite.
    move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    rewrite collate_ls_neq_to; last by auto.
    case (adjacent_to_dec h n') => H_dec.
      rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
      rewrite collate_neq //; last by auto.
      rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) //.
      rewrite (Aggregation_inactive_no_incoming s1) //=.
      exact: (after_init_fst_adjacent s1).
    rewrite collate_map2snd_not_related //.
    rewrite collate_ls_not_related //.
    rewrite collate_neq //; last by auto.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) //.
    rewrite (Aggregation_inactive_no_incoming s1) //.
    exact: (after_init_fst_not_adjacent s1).
  * move => d0 H_eq d1 H_eq'.
    repeat find_inversion.
    case: H_in_n => H_in_n; first by rewrite -H_in_n in n0.
    case (adjacent_to_dec h n) => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq; last by auto.
      rewrite collate_ls_neq_to; last by auto.
      rewrite collate_map2snd_not_related //.
      rewrite (Aggregation_inactive_no_incoming s1) //.
      rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) //.
      have H_adj: ~ adjacent_to n h.
        move => H_adj.
        case: H_dec.
        exact: adjacent_to_symmetric.
      have H_neq: h <> n by auto.
      exact: (after_init_snd_not_adjacent s1).
    rewrite collate_ls_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite collate_neq; last by auto.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_map2snd_not_in_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
    rewrite (Aggregation_inactive_no_incoming s1) //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) //=.
    apply adjacent_to_symmetric in H_dec.
    have H_neq: h <> n by auto.
    exact: (after_init_snd_adjacent s1).
  * move => d0 H_eq d1 H_eq'.
    case: H_in_n => H_in_n; first by rewrite H_in_n in n0.
    case: H_in_n' => H_in_n'; first by rewrite H_in_n' in n1.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_neq; last by auto.
    rewrite collate_ls_neq_to; last by auto.
    rewrite collate_neq; last by auto.
    exact: IHs1.
- move => H_in_n H_in_n' H_in_f H_in_f'.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases.
  * destruct_update; repeat find_injection.
    + rewrite /update2 /=.
      break_if; first by break_and; subst; find_rewrite_lem (Aggregation_self_channel_empty s1).
      break_or_hyp => //.
      case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by find_rewrite_lem (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1 _ H_from_in).
      destruct d1.
      simpl in *.
      rewrite (Aggregation_self_channel_empty s1).
      repeat find_rewrite.
      case (adjacent_to_dec n from) => H_dec; last by find_rewrite_lem (Aggregation_not_adjacent_no_incoming s1 H_in_n H_in_f H_dec).
      apply: (recv_aggregate_self s1); intuition eauto.
      exact: adjacent_to_symmetric.
    + case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by find_rewrite_lem (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1 _ H_from_in).
      have H_hd: head (odnwPackets net from n') = Some (Aggregate x) by find_rewrite.
      have H_ins := Aggregation_aggregate_head_in_adjacent s1 _ H1 H_in_f' _ H_hd H2.
      have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H_in_f' H2 H_ins.
      rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      -- destruct d1.
         simpl in *.
         repeat find_rewrite.
         apply (recv_aggregate_snd s1) => //; first by find_apply_lem_hyp adjacent_to_symmetric.
         rewrite H3.
         exact: H5.
      -- have H_neq: from <> n by intuition eauto.
         have H_neq': from <> n' by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d1.
         simpl in *.
         repeat find_rewrite.
         by eapply (recv_aggregate_snd_other s1); eauto.
    + case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by find_rewrite_lem (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1 _ H_from_in).
      have H_hd: head (odnwPackets net from n) = Some (Aggregate x) by find_rewrite.
      have H_ins := Aggregation_aggregate_head_in_adjacent s1 _ H1 H_in_f _ H_hd H2.
      have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H_in_f H2 H_ins.
      rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      -- destruct d0.
         simpl in *.
         repeat find_rewrite.
         apply (recv_aggregate_fst s1); auto.
         rewrite H3.
         exact: H5.
      -- have H_neq: from <> n' by intuition eauto.
         have H_neq': from <> n by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d0.
         simpl in *.
         repeat find_rewrite.
         by eapply (recv_aggregate_fst_other s1); eauto.
    + rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      exact: H5.
  * have H_hd: head (odnwPackets net from to) = Some (Aggregate x) by find_rewrite.
    have H_ins := Aggregation_aggregate_head_in_adjacent s1 _ H1 H0 _ H_hd H2.
    have [m' H_bal] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H_ins.
    by find_rewrite.
  * destruct_update; repeat find_injection.
    + rewrite /update2 /=.
      break_if; first by break_and; subst; find_rewrite_lem (Aggregation_self_channel_empty s1).
      break_or_hyp => //.
      case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by find_rewrite_lem (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1 _ H_from_in).
      case (In_dec name_eq_dec from failed0) => H_from_f; last first.
        have H_f := Aggregation_not_failed_no_fail s1 _ H_from_in H_from_f n.
        rewrite H3 in H_f.
        by case: H_f; left.
      destruct d1.
      simpl in *.
      rewrite (Aggregation_self_channel_empty s1).
      repeat find_rewrite.
      case (adjacent_to_dec n from) => H_dec; last by find_rewrite_lem (Aggregation_not_adjacent_no_incoming s1 H_in_n H_in_f H_dec).
      apply: (recv_fail_self s1); intuition eauto.
      exact: adjacent_to_symmetric.
    + rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      -- have H_f := Aggregation_not_failed_no_fail s1 _ H_in_n H_in_f n'.
         rewrite H3 in H_f.
         by case: H_f; left.
      -- have H_neq: from <> n by intuition eauto.
         have H_neq': from <> n' by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d1.
         simpl in *.
         repeat find_rewrite.
         case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
         case (In_dec name_eq_dec from failed0) => H_from_f; last first.
           have H_f := Aggregation_not_failed_no_fail s1 _ H_from_in H_from_f n'.
           rewrite H3 in H_f.
           by case: H_f; left.
         case (adjacent_to_dec from n') => H_dec; last first.
           rewrite (Aggregation_not_adjacent_no_incoming s1) // in H3.
           move => H_adj.
           case: H_dec.
           exact: adjacent_to_symmetric.
         by apply: (recv_fail_other_snd s1); eauto.
    + rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      -- have H_f := Aggregation_not_failed_no_fail s1 _ H_in_n' H_in_f' n.
         rewrite H3 in H_f.
         by case: H_f; left.
      -- have H_neq: from <> n' by intuition eauto.
         have H_neq': from <> n by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d0.
         simpl in *.
         repeat find_rewrite.
         case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
         case (In_dec name_eq_dec from failed0) => H_from_f; last first.
           have H_f := Aggregation_not_failed_no_fail s1 _ H_from_in H_from_f n.
           rewrite H3 in H_f.
           by case: H_f; left.
         case (adjacent_to_dec from n) => H_dec; last first.
           rewrite (Aggregation_not_adjacent_no_incoming s1) // in H3.
           move => H_adj.
           case: H_dec.
           exact: adjacent_to_symmetric.
         by apply: (recv_fail_other_fst s1); eauto.
    + rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      exact: H5.
  * have H_hd: head (odnwPackets net from to) = Some Fail by find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    have [m' H_bal] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H_ins.
    by find_rewrite.
  * destruct_update; repeat find_injection.
    + rewrite /update2 /=.
      break_if; first by break_and; subst; find_rewrite_lem (Aggregation_self_channel_empty s1).
      break_or_hyp => //.
      case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by find_rewrite_lem (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1 _ H_from_in).     
      destruct d1.
      simpl in *.
      rewrite (Aggregation_self_channel_empty s1).
      repeat find_rewrite.
      case (adjacent_to_dec n from) => H_dec; last by find_rewrite_lem (Aggregation_not_adjacent_no_incoming s1 H_in_n H_in_f H_dec).
      apply: (recv_new_self s1); intuition eauto.
      exact: adjacent_to_symmetric.
    + have H_adj: adjacent_to n' from.
        apply adjacent_to_symmetric.
        apply: (Aggregation_in_new_then_adjacent s1 _ H1 H0 from).
        by rewrite H3; left.        
      rewrite /update2 /=.      
      repeat break_if; repeat break_and; subst => //.
      -- destruct d1.
         simpl in *.
         repeat find_rewrite.
         apply: (recv_new_snd s1) => //.
         rewrite H3.
         exact: H11.
      -- have H_neq: from <> n by intuition eauto.
         have H_neq': from <> n' by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d1.
         simpl in *.
         repeat find_rewrite.
         case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
         by apply: (recv_new_snd_other s1); eauto => //; first by apply adjacent_to_symmetric in H_adj.
    + have H_adj: adjacent_to from n.
        apply: (Aggregation_in_new_then_adjacent s1 _ H1 H0 from).
        by rewrite H3; left.
      rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      -- destruct d0.
         simpl in *.
         repeat find_rewrite.
         apply: (recv_new_fst s1); eauto.
         rewrite H3.
         exact: H11.
      -- have H_neq: from <> n' by intuition eauto.
         have H_neq': from <> n by move => H_neq'; rewrite H_neq' (Aggregation_self_channel_empty s1) in H3.
         destruct d0.
         simpl in *.
         repeat find_rewrite.
         case (In_dec name_eq_dec from net.(odnwNodes)) => H_from_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
         by apply: (recv_new_fst_other s1); eauto.
    + rewrite /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      exact: H11.      
- move => H_in_n H_in_n' H_in_f H_in_f'.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * destruct_update; repeat find_injection.
    + rewrite /= (Aggregation_self_channel_empty s1).
      destruct d1.
      simpl in *.
      repeat find_rewrite.      
      by apply: (recv_local_self _ s1); eauto.
    + rewrite /=.
      destruct d1.
      simpl in *.
      repeat find_rewrite.
      by apply: (recv_local_snd _ s1); eauto.
    + rewrite /=.
      destruct d0.
      simpl in *.
      repeat find_rewrite.
      by apply: (recv_local_fst _ s1); eauto.
    + by eauto.
  * destruct_update; repeat find_injection.
    + rewrite /= /update2 /=.
      repeat break_if; repeat break_and; subst => //; first by have H_ins := Aggregation_node_not_adjacent_self s1 H1 H0 H2.
      break_or_hyp => //.
      rewrite (Aggregation_self_channel_empty s1).
      have H_adj := Aggreation_in_adj_adjacent_to s1 _ H_in_n H_in_f H2 H3.
      have H_x_in: In x net.(odnwNodes).
        have H_or := Aggregation_in_adj_or_incoming_fail s1 _ H_in_n H_in_f H2 H3.
        by break_or_hyp; break_and.
      destruct d1.
      simpl in *.
      repeat find_rewrite.
      apply: (send_aggregate_self s1) => //.
      by eauto.
    + rewrite /= /update2 /=.
      have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H3.
      have H_x_in: In x net.(odnwNodes).
        have H_or := Aggregation_in_adj_or_incoming_fail s1 _ H_in_n' H_in_f' H2 H3.
        by break_or_hyp; break_and.
      repeat break_if; repeat break_and; subst => //.
      -- destruct d1.
         simpl in *.
         repeat find_rewrite.
         apply: (send_aggregate_snd s1) => //; first by apply adjacent_to_symmetric.
         by eauto.
      -- have H_neq: x <> n by intuition eauto.
         have H_neq': x <> n'. 
           move => H_neq'.
           rewrite H_neq' in H3.
           contradict H3.
           exact: (Aggregation_node_not_adjacent_self s1).
         destruct d1.
         simpl in *.
         repeat find_rewrite.
         apply: (send_aggregate_snd_other s1) => //.
         by eauto.
    + rewrite /= /update2 /=.
      have H_adj := Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H3.
       have H_x_in: In x net.(odnwNodes).
         have H_or := Aggregation_in_adj_or_incoming_fail s1 _ H_in_n H_in_f H2 H3.
         by break_or_hyp; break_and.
      repeat break_if; repeat break_and; subst => //.
      -- destruct d0.
         simpl in *.
         repeat find_rewrite.
         by apply: (send_aggregate_fst s1); eauto.
      -- have H_neq: x <> n' by intuition eauto.
         have H_neq': x <> n. 
           move => H_neq'.
           rewrite H_neq' in H3.
           contradict H3.
           exact: (Aggregation_node_not_adjacent_self s1).
         destruct d0.
         simpl in *.
         repeat find_rewrite.
         by apply: (send_aggregate_fst_other s1); eauto.
    + rewrite /= /update2 /=.
      repeat break_if; repeat break_and; subst => //.
      by eauto.
  * have [m' H_bal] := Aggregation_in_set_exists_find_balance s1 _ H1 H0 H2 H.
    by congruence.
  * by destruct_update; repeat find_injection; eauto.
  * by destruct_update; repeat find_injection; eauto.
  * by destruct_update; repeat find_injection; eauto.
- move => H_in_n H_in_n' H_in_f H_in_f'.
  move => d0 H_eq d1 H_eq'.
  have H_neq: h <> n by auto.
  have H_neq': h <> n' by auto.
  have H_in'_f: ~ In n failed0 by auto.
  have H_in'_f': ~ In n' failed0 by auto.
  rewrite collate_neq //.
  rewrite collate_neq //.
  exact: IHs1.
Qed.

End DualNodeInv.

Lemma Aggregation_send_aggregate_in : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
   forall m', In (Aggregate m') (net.(odnwPackets) n n') ->
   forall d, net.(odnwState) n = Some d ->
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st.
move => n H_in_n H_f n' H_in_n' H_f'.
move => m' H_in d0 H_eq.
have [d1 H_eq'] := ordered_dynamic_initialized_state H_st _ H_in_n'.
move: m' H_in.
pose P_curr (d : Data) (d' : Data) (l : list Msg) (l' : list Msg) :=
forall m' : m, In (Aggregate m') l -> NSet.In n' d.(adjacent).
rewrite -/(P_curr _ d1 _ (odnwPackets net n' n)).
move: H_eq'; generalize d1 => {d1}.
move: H_eq; generalize d0 => {d0}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' net}.
- move => net failed tr H_st H_in_n H_f H_in_n' H_f' H_neq H_adj d H_eq m' H_in.
  by break_or_hyp.
- move => net failed tr H_st H_in_n H_f H_in_n' H_f' H_neq H_adj d H_eq m' H_in.
  by break_or_hyp.
- by eauto with set.
- by eauto with set.
- move => net failed tr ms H_st H_in_n H_f H_in_n' H_f' H_neq H_adj H_eq d0 H_eq_d0 d1 H_eq_d1 IH m' H_in.
  apply: (IH m').
  rewrite H_eq.
  by right.
- by eauto with set.
- move => net failed tr ms m0 m' H_st H_in_n H_f H_in_n' H_f' H_neq H_adj H_eq d0 H_eq_d0 d1 H_eq_d1 H_find IH m1 H_in.
  apply: (IH m1).
  rewrite H_eq.
  by right.
Qed.

Lemma not_adjacent_sum_aggregate_msg_1 : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
   forall d, net.(odnwState) n = Some d ->
   ~ NSet.In n' d.(adjacent) ->
   sum_aggregate_msg (net.(odnwPackets) n n') = 1.
Proof.
move => net failed tr H_st.
move => n H_in_n H_f n' H_in_n' H_f'.
move => d0 H_eq H_ins.
have [d1 H_eq'] := ordered_dynamic_initialized_state H_st _ H_in_n'.
move: H_ins.
pose P_curr (d : Data) (d' : Data) (l : list Msg) (l' : list Msg) :=
~ NSet.In n' d.(adjacent) -> @sum_aggregate_msg AggregationMsg_Aggregation l = 1.
rewrite -/(P_curr _ d1 _ (odnwPackets net n' n)).
move: H_eq'; generalize d1 => {d1}.
move: H_eq; generalize d0 => {d0}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' net}.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins.
  rewrite /aggregate_sum_fold /=.
  by gsimpl.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins.
  rewrite /aggregate_sum_fold /=.
  by gsimpl.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_n H_neq_n' H_in_from H_in_from' H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins.
  apply: IH.
  move => H_ins'.
  case: H_ins.
  by auto with set.
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins.
  case: H_ins.
  by auto with set.
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins.
  concludes.
  find_rewrite.
  simpl in *.
  unfold aggregate_sum_fold in *.
  simpl in *.
  move: IH.
  by gsimpl.
- move => net failed tr from ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins.
  rewrite IH //.
  move => H_ins'.
  case: H_ins.
  by auto with set.
- move => net failed tr ms m0 m' H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins.
  have H_in: In (Aggregate m') (odnwPackets net n n') by rewrite H_eq; left.
  by have H_ins' := Aggregation_send_aggregate_in H_st _ H_in_n H_in_f _ H_in_n' H_in_f' _ H_in H_eq_d0.
Qed.

Lemma sent_received_one_not_in : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
   forall d0, net.(odnwState) n = Some d0 ->
   forall d1, net.(odnwState) n' = Some d1 ->
   NSet.In n' d0.(adjacent) ->
   ~ NSet.In n d1.(adjacent) ->
   forall m', NMap.find n' d0.(balance) = Some m' ->
   sum_aggregate_msg (net.(odnwPackets) n n') = m'.
Proof.
move => net failed tr H_st.
move => n H_in_n H_f n' H_in_n' H_f'.
move => d0 H_eq d1 H_eq'.
pose P_curr (d : Data) (d' : Data) (l : list Msg) (l' : list Msg) :=
  NSet.In n' d.(adjacent) ->
  ~ NSet.In n d'.(adjacent) -> 
  forall m', NMap.find n' d.(balance) = Some m' -> 
  @sum_aggregate_msg AggregationMsg_Aggregation l = m'.
rewrite -/(P_curr _ _ _ (odnwPackets net n' n)).
move: H_eq'; generalize d1 => {d1}.
move: H_eq; generalize d0 => {d0}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' net}.
- move => onet failed tr H_st H_eq H_in_n H_in_f H_ins H_ins' H_find.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins H_ins' H_find.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins H_ins' H_find.
  have H_adj' := Aggreation_in_adj_adjacent_to H_st _ H_in_n H_in_f H_eq H_ins.
  by find_apply_lem_hyp adjacent_to_symmetric.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj d H_eq H_ins H_ins' H_find.
  by have H_adj' := Aggregation_inactive_not_in_adjacent H_st _ H_in_n H_in_f H_in_n' H_eq.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_eq H_from H_from' H_neq H_adj H_eq'.
  move => d H_eq_d H_find IH H_ins H_ins' H_find'.
  by repeat find_rewrite.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq_n H_neq H_neq' H_from H_from' H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m' H_find'.
  find_apply_lem_hyp NSetFacts.remove_3 => //.
  rewrite NMapFacts.remove_neq_o // in H_find'.
  repeat concludes.
  exact: IH.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_in_from' H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m' H_find'.
  have H_ins_n: ~ NSet.In n d1.(adjacent).
    move => H_ins_n.
    case: H_ins'.
    by apply NSetFacts.remove_2.
  repeat concludes.
  exact: IH.
- move => net failed tr from ms H_st H_in_n H_in_f H_eq H_in_from H_neq H_adj H_eq'.
  move => d H_eq_d IH H_ins H_ins' m' H_find.
  subst.  
  have H_ins_n: ~ NSet.In n d.(adjacent).
    move => H_ins_n.
    case: H_ins'.
    by apply NSetFacts.add_2.
  by find_apply_lem_hyp NSetFacts.add_3.
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m' H_find.
  move {IH H_ins}.
  rewrite NMapFacts.add_eq_o // in H_find.
  find_injection.
  have H_in_new: In New (odnwPackets net n' n) by find_rewrite; left.
  have H_ins_n := Aggregation_new_incoming_not_in_adj H_st _ H_in_n H_in_f H_in_new H_eq_d0.
  exact: (not_adjacent_sum_aggregate_msg_1 H_st _ H_in_n H_in_f H_in_n' H_in_f' H_eq_d0 H_ins_n).
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m' H_find.
  case: H_ins'.
  by auto with set.
- move => net failed tr from ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m' H_find.
  find_apply_lem_hyp NSetFacts.add_3 => //.
  rewrite NMapFacts.add_neq_o // in H_find.
  repeat concludes.
  exact: IH.
- move => net failed tr from ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m' H_find.
  have H_ins_n: ~ NSet.In n d1.(adjacent).
    move => H_ins_n.
    case: H_ins'.
    by auto with set.
  repeat concludes.
  exact: IH.
- move => net failed tr from ms m0 m1 H_st H_in_n H_in_f H_eq H_in_from H_neq H_adj H_eq'.
  move => d0 H_eq_d0 d1 IH H_ins H_ins' m' H_find.
  by subst.
- move => net failed tr ms m0 m1 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m' H_find'.
  have H_in: In (Aggregate m1) (odnwPackets net n' n) by rewrite H_eq; left.
  by have H_agg := Aggregation_send_aggregate_in H_st _ H_in_n' H_in_f' _ H_in_n H_in_f _ H_in H_eq_d1.
- move => net failed tr ms m0 m1 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m' H_find'.
  have H_hd: head (odnwPackets net n n') = Some (Aggregate m1) by rewrite H_eq.
  by have H_ins_n := Aggregation_aggregate_head_in_adjacent H_st _ H_in_n' H_in_f' _ H_hd H_eq_d1.
- move => net failed tr from ms m0 m1 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m' H_find'.  
  rewrite NMapFacts.add_neq_o // in H_find'.
  repeat concludes.
  exact: IH.
- move => net failed tr m0 H_st H_in_n H_in_f H_eq d H_eq_d IH H_ins H_ins' H_find.
  by subst.
- move => net failed tr to m0 H_st H_in_n H_in_f H_eq H_in_to H_neq H_adj.
  move => d H_eq_d H_find H_ins H_neq' IH H_ins' H_ins'' m' H_find'.
  subst.
  contradict H_ins'.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq' IH H_ins' H_ins'' m' H_find'.
  rewrite NMapFacts.add_eq_o // in H_find'.
  find_injection.
  repeat concludes.
  rewrite sum_aggregate_msg_split.
  rewrite (IH _ H_find).
  rewrite /sum_aggregate_msg /= /aggregate_sum_fold /=.
  by gsimpl.
- move => net failed tr to m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq_n H_neq_to H_neq_to' H_in_to H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq IH H_ins' H_ins'' m' H_find'.
  rewrite NMapFacts.add_neq_o // in H_find'.
  exact: IH.
Qed.

Lemma Aggregation_sent_received_eq: 
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->    
    NSet.In n' d.(adjacent) ->
    NSet.In n d'.(adjacent) ->
    forall m0, NMap.find n d'.(balance) = Some m0 ->
    forall m1, NMap.find n' d.(balance) = Some m1 ->
    m0 * (sum_aggregate_msg (net.(odnwPackets) n n'))^-1 = (m1)^-1 * sum_aggregate_msg (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st.
move => n H_in_n H_f n' H_in_n' H_f'.
move => d0 H_eq d1 H_eq'.
pose P_curr (d : Data) (d' : Data) (l : list Msg) (l' : list Msg) :=
  NSet.In n' d.(adjacent) ->
  NSet.In n d'.(adjacent) ->
  forall m0 : m, NMap.find n d'.(balance) = Some m0 ->
  forall m1 : m, NMap.find n' d.(balance) = Some m1 ->
  m0 * (@sum_aggregate_msg AggregationMsg_Aggregation l)^-1 = m1^-1 * @sum_aggregate_msg AggregationMsg_Aggregation l'.
rewrite -/(P_curr _ _ _ _).
move: H_eq'; generalize d1 => {d1}.
move: H_eq; generalize d0 => {d0}.
apply: (P_dual_inv H_st); rewrite /P_curr //= {P_curr tr H_st failed H_f H_f' H_in_n H_in_n' net}.
- move => net failed tr H_st H_eq H_in_n H_in_f H_ins H_ins' m0 H_find m1 H_find'.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq_d H_ins H_ins' m0 H_find m1 H_find'.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_t H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq_d H_ins H_ins' m0 H_find m1 H_find'.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq_d H_ins H_ins' m0 H_find m1 H_find'.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d H_eq_d H_ins H_ins' m0 H_find m1 H_find'.
  by find_apply_lem_hyp NSetFacts.empty_1.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_eq H_in_from H_in_from' H_neq H_adj H_eq'. 
  move => d H_eq_d H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  subst.
  find_apply_lem_hyp NSetFacts.remove_3.
  contradict H_ins.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_from_neq H_from_neq' H_in_from H_in_from' H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.remove_neq_o // in H_find_m2.
  find_apply_lem_hyp NSetFacts.remove_3.
  exact: IH.
- move => net failed tr from ms m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_in_from' H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.remove_neq_o // in H_find_m1.
  find_apply_lem_hyp NSetFacts.remove_3.
  exact: IH.
- move => net faild tr from ms H_st H_in_n H_in_f H_eq H_in_from H_neq_from H_adj H_eq'.
  move => d H_eq_d IH H_ins H_ins' m0 H_find_m0 m1 H_find_m1.
  subst.
  find_apply_lem_hyp NSetFacts.add_3 => //.
  contradict H_ins.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m0 H_find_m0 m1 H_find_m1.
  rewrite NMapFacts.add_eq_o // in H_find_m1.
  find_injection.
  gsimpl.
  have H_in: In New (odnwPackets net n' n) by rewrite H_eq; left.
  have H_ins_n := Aggregation_new_incoming_not_in_adj H_st _ H_in_n H_in_f H_in H_eq_d0.
  have H_eq_n := sent_received_one_not_in H_st H_in_n' H_in_f' H_in_n H_in_f H_eq_d1 H_eq_d0 H_ins' H_ins_n H_find_m0.
  rewrite H_eq /= /aggregate_sum_fold /= in H_eq_n.
  move: H_eq_n.
  gsimpl.
  move => H_eq_n.
  rewrite H_eq_n.
  rewrite (not_adjacent_sum_aggregate_msg_1 H_st _ H_in_n H_in_f H_in_n' H_in_f' H_eq_d0 H_ins_n).
  by gsimpl.
- move => net failed tr ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m0 H_find m1 H_find'.
  rewrite NMapFacts.add_eq_o // in H_find.
  find_injection.
  gsimpl.
  have H_in: In New (odnwPackets net n n') by rewrite H_eq; left.
  have H_ins_n' := Aggregation_new_incoming_not_in_adj H_st _ H_in_n' H_in_f' H_in H_eq_d1.
  have H_eq_n' := sent_received_one_not_in H_st H_in_n H_in_f H_in_n' H_in_f' H_eq_d0 H_eq_d1 H_ins H_ins_n' H_find'.  
  rewrite H_eq /= /aggregate_sum_fold /= in H_eq_n'.
  move: H_eq_n'.
  gsimpl.
  move => H_eq_n'.
  rewrite H_eq_n'.
  rewrite (not_adjacent_sum_aggregate_msg_1 H_st _ H_in_n' H_in_f' H_in_n H_in_f H_eq_d1 H_ins_n').
  by gsimpl.
- move => net failed tr from ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m0 H_find_m0 m1 H_find_m1.
  find_apply_lem_hyp NSetFacts.add_3 => //.
  rewrite NMapFacts.add_neq_o // in H_find_m1.
  exact: IH.
- move => net failed tr from ms H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 IH H_ins H_ins' m0 H_find_m0 m1 H_find_m1.
  find_apply_lem_hyp NSetFacts.add_3 => //.
  rewrite NMapFacts.add_neq_o // in H_find_m0.
  exact: IH.
- move => net failed tr from ms m0 m' H_st H_in_n H_in_f H_eq H_in_from H_neq H_adj H_eq'.
  move => d H_eq_d H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  subst.
  contradict H_ins.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr ms m0 m' H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_eq_o // in H_find_m2.
  find_injection.
  gsimpl.
  repeat concludes.
  have IH' := IH _ H_find_m1 _ H_find.
  rewrite H_eq /= /aggregate_sum_fold /= in IH'.
  rewrite IH'.
  gsimpl.
  by aac_reflexivity.
- move => net failed tr ms m0 m' H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_eq_o // in H_find_m1.
  find_injection.
  repeat concludes.
  have IH' := IH _ H_find _ H_find_m2.
  rewrite H_eq /= /aggregate_sum_fold /= in IH'.
  rewrite -IH'.
  by gsimpl.
- move => net failed tr from ms m0 m' H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_neq_o // in H_find_m2.
  exact: IH.
- move => net failed tr from ms m0 m' H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_from H_neq_from' H_in_from H_adj H_eq.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find IH H_ins H_ins' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_neq_o // in H_find_m1.
  exact: IH.
- move => net failed tr m' H_st H_in_n H_in_f H_eq d H_eq_d IH H_ins H_ins' m0 H_find_m0 m1 H_find_m1.
  subst.
  contradict H_ins.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr to m0 H_st H_in_n H_in_f H_eq H_in_to H_neq H_adj.
  move => d H_eq_d H_find H_ins H_neq_agg IH H_ins' H_ins'' m1 H_find_m1 m2 H_find_m2.
  subst.
  contradict H_ins'.
  by eapply Aggregation_node_not_adjacent_self; eauto.
- move => net failed tr m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq' IH H_ins' H_ins'' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_eq_o // in H_find_m2.
  find_injection.
  rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
  gsimpl.
  repeat concludes.
  have IH' := IH _ H_find_m1 _ H_find.
  aac_rewrite IH'.
  by aac_reflexivity.
- move => net failed tr m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq_agg IH H_ins' H_ins'' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_eq_o // in H_find_m1.
  find_injection.
  rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
  gsimpl.
  repeat concludes.
  have IH' := IH _ H_find _ H_find_m2.
  rewrite -IH'.
  by aac_reflexivity.
- move => net failed tr to m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_to H_neq_to' H_in_to H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq_agg IH H_ins' H_ins'' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_neq_o // in H_find_m2.
  exact: IH.
- move => net failed tr to m0 H_st H_in_n H_in_f H_in_n' H_in_f' H_neq H_neq_to H_neq_to' H_in_to H_adj.
  move => d0 H_eq_d0 d1 H_eq_d1 H_find H_ins H_neq_agg IH H_ins' H_ins'' m1 H_find_m1 m2 H_find_m2.
  rewrite NMapFacts.add_neq_o // in H_find_m1.
  exact: IH.
Qed.

Lemma sumM_balance_fail_active_eq_with_self : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall d, net.(odnwState) n = Some d ->
   sumM d.(adjacent) d.(balance) * (sum_fail_map_incoming net.(odnwNodes) net.(odnwPackets) n d.(adjacent) d.(balance))^-1 =
   sumM_active d.(adjacent) d.(balance) (remove_all name_eq_dec failed net.(odnwNodes)).
Proof.
move => net failed tr H_st n H_n H_f d H_eq_d.
have H_ex_map := Aggregation_in_set_exists_find_balance H_st _ H_n H_f H_eq_d.
have H_ex_nd := Aggregation_in_adj_or_incoming_fail H_st _ H_n H_f H_eq_d.
assert (H_adj_in: forall (n' : name), NSet.In n' d.(adjacent) -> In n' net.(odnwNodes)).
  move => n' H_ins.
  have H_agg := Aggregation_in_adj_or_incoming_fail H_st _ H_n H_f H_eq_d H_ins.
  by break_or_hyp; break_and.
have H_n_nd := ordered_dynamic_nodes_no_dup H_st.
have H := @sumM_remove_fail_ex_eq AggregationMsg_Aggregation _ net.(odnwPackets) _ _ n _ H_adj_in H_ex_map.
have [adj' [H_eq [H_and H_or]]] := H H_n_nd.
rewrite H_eq.
have H_nd: NoDup (remove_all name_eq_dec failed net.(odnwNodes)) by apply NoDup_remove_all; apply H_n_nd.
have H_eq' := sumM_sumM_active_eq _ _ H_nd _ H_and H_or H_ex_map.
rewrite H_eq' //.
  move => n' H_f' H_in.
  contradict H_f'.
  apply: (Aggregation_not_failed_no_fail H_st); first by eapply in_remove_all_was_in; eauto.
  move => H_in'.
  contradict H_in.
  by eauto using in_remove_all_not_in.
move => n' H_ins.
apply H_or in H_ins.
case: H_ins => H_ins; last by right.
apply H_and in H_ins.
move: H_ins => [H_ins H_f'].
left.
apply: in_remove_all_preserve; last exact: H_adj_in.
apply H_ex_nd in H_ins.
by case: H_ins => H_ins; break_and.
Qed.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed -> 
        sum_aggregate_msg (net.(odnwPackets) n n) = 1.
Proof.
move => net failed tr H_st n H_in_n H_in_f.
by rewrite (Aggregation_self_channel_empty H_st).
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

Lemma Aggregation_conserves_node_mass_all : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 conserves_node_mass_all (Nodes_data_opt (remove_all name_eq_dec failed net.(odnwNodes)) net.(odnwState)).
Proof.
move => onet failed tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data_opt.
elim: (odnwNodes onet) => /=; first by rewrite remove_all_nil.
move => n l IH d.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
move => H_or.
simpl in *.
break_match; last exact: IH.
case: H_or => H_or; last exact: IH.
rewrite -H_or.
by apply: (Aggregation_conserves_node_mass H_st); eauto.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr ->
 conserves_mass_globally (Nodes_data_opt (remove_all name_eq_dec failed onet.(odnwNodes)) onet.(odnwState)).
Proof.
move => onet failed tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

Lemma Nodes_data_opt_not_in_eq :
  forall ns (state : name -> option data) to d,
    ~ In to ns ->
    Nodes_data_opt ns (update name_eq_dec state to (Some d)) =
    Nodes_data_opt ns state.
Proof.
elim => //.
move => n ns IH state to d H_in.
rewrite /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite {1}/update.
case name_eq_dec => H_dec //.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma sum_fail_balance_incoming_active_opt_split :
  forall ns0 ns1 ns2 packets state,
    sum_fail_balance_incoming_active_opt ns0 (ns1 ++ ns2) packets state = 
    sum_fail_balance_incoming_active_opt ns0 ns1 packets state *
    sum_fail_balance_incoming_active_opt ns0 ns2 packets state.
Proof.
move => ns0 ns1 ns2 packets state.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by break_match; aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_balance_neq_eq :
  forall ns packets from to ms n adj map,
  n <> to ->
  sum_fail_map_incoming ns (update2 name_eq_dec packets from to ms) n adj map =
  sum_fail_map_incoming ns packets n adj map.
Proof.
elim => //=.
move => n ns IH packets from to ms n0 adj map H_neq.
rewrite IH //.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_balance_incoming_active_opt_not_in_eq :
  forall ns0 ns1 packets state from to ms d,
    ~ In to ns0 ->
    sum_fail_balance_incoming_active_opt ns1 ns0 
      (update2 name_eq_dec packets from to ms)
      (update name_eq_dec state to (Some d)) =
    sum_fail_balance_incoming_active_opt ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms d H_in.
rewrite /sum_fail_balance_incoming_active_opt /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite /update /=.
case name_eq_dec => H_dec //.
have H_in': ~ In to ns.
  move => H_in'.
  case: H_in.
  by right.
break_match.
- have IH' := IH ns1 packets state from to ms d H_in'.
  rewrite /update /= /sum_fail_balance_incoming_active_opt in IH'.
  by rewrite IH' /= sum_fail_map_incoming_balance_neq_eq.
- have IH' := IH ns1 packets state from to ms d H_in'.
  rewrite /update /= /sum_fail_balance_incoming_active_opt in IH'.
  by rewrite IH'.
Qed.

Lemma sum_aggregate_msg_incoming_new_update2_eq : 
  forall ns f from to ms,
  f from to = New :: ms ->
    sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
elim => //=.
move => n ns IH f from to ms H_eq.
case in_dec => /= H_dec; case in_dec => /= H_dec'.
- by rewrite IH.
- contradict H_dec.
  rewrite /update2 /=.
  break_if => //; break_and.
  subst.
  move => H_in.
  case: H_dec'.
  find_rewrite.
  by right.
- case: H_dec.
  rewrite /update2 /=.
  break_if => //; break_and.
  subst.
  find_rewrite.
  by case: H_dec'.
- rewrite IH //.
  rewrite /update2 /=.
  break_if => //.
  break_and; subst.
  rewrite H_eq /= /aggregate_sum_fold /=.
  by gsimpl.
Qed.

Lemma sum_fail_map_incoming_new_eq :
  forall ns f from to ms adj map,
    ~ NSet.In from adj ->
    f from to = New :: ms ->
    sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) to (NSet.add from adj) (NMap.add from 1 map) =
    sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms adj map H_ins H_eq.
rewrite {2}/update2 /=.
break_if.
- break_and; subst.
  rewrite /sum_fail_map H_eq.
  case in_dec => /= H_dec; case in_dec => /= H_dec' //.
  * repeat break_if => //.
    + case: H_ins.
      by auto with set.
    + rewrite IH //.
      rewrite /sum_fold /= NMapFacts.add_eq_o //.
      by gsimpl.
    + case: H_ins.
      by auto with set.
    + have H_ins': NSet.In n (NSet.add n adj) by auto with set.
      find_apply_lem_hyp NSetFacts.mem_1.
      by congruence.
  * by rewrite IH; gsimpl.
- break_or_hyp => //.
  rewrite IH // /sum_fail_map.
  case in_dec => /= H_dec //.
  repeat break_if => //.
  * by rewrite {1}/sum_fold NMapFacts.add_neq_o.
  * find_apply_lem_hyp NSetFacts.mem_2.
    find_apply_lem_hyp NSetFacts.add_3 => //.
    find_apply_lem_hyp NSetFacts.mem_1.
    by congruence.
  * find_apply_lem_hyp NSetFacts.mem_2.
    have H_ins': NSet.In n (NSet.add from adj) by auto with set.    
    find_apply_lem_hyp NSetFacts.mem_1.
    by congruence.
Qed.

Lemma sum_fail_balance_incoming_active_opt_not_in_eq_alt :
forall ns1 ns0 packets state h d,
  ~ In h ns1 ->
  sum_fail_balance_incoming_active_opt ns0 ns1 packets (update name_eq_dec state h d) =
  sum_fail_balance_incoming_active_opt ns0 ns1 packets state.
Proof.
elim => //=.
move => n ns1 IH ns0 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns1 by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_balance_incoming_active_opt_not_in_eq_alt2 :
  forall ns0 ns1 packets state from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_balance_incoming_active_opt ns1 ns0 (update2 name_eq_dec packets from to ms) (update name_eq_dec state h (Some d)) =
    sum_fail_balance_incoming_active_opt ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms h d H_in H_in'.
rewrite /sum_fail_balance_incoming_active_opt /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
destruct_update => //.
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
break_match.
- have IH' := IH ns1 packets state from to ms _ d H_inn H_inn'.
  rewrite /sum_fail_balance_incoming_active_opt /= in IH'.
  by rewrite IH' sum_fail_map_incoming_balance_neq_eq.
- have IH' := IH ns1 packets state from to ms _ d H_inn H_inn'.
  rewrite /sum_fail_balance_incoming_active_opt /= in IH'.
  by rewrite IH'.
Qed.

Lemma sum_fail_balance_incoming_active_opt_update_not_in_eq :
  forall ns0 ns1 packets state h d,
    ~ In h ns0 ->
    sum_fail_balance_incoming_active_opt ns1 ns0 packets (update name_eq_dec state h d) =
    sum_fail_balance_incoming_active_opt ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_balance_incoming_active_opt_update2_app_eq :
  forall ns0 ns1 packets state h x mg,
    mg <> Fail ->
    sum_fail_balance_incoming_active_opt ns1 ns0 (update2 name_eq_dec packets h x (packets h x ++ [mg])) state =
    sum_fail_balance_incoming_active_opt ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH H_neq ns1 packets state h x m'.
rewrite IH //.
break_match => //.
by rewrite sum_fail_map_incoming_update2_app_eq.
Qed.

Lemma Aggregation_sum_fail_balance_incoming_active_opt_update2_app_eq :
  forall ns0 ns1 packets state h x m',
    sum_fail_balance_incoming_active_opt ns1 ns0 (update2 name_eq_dec packets h x (packets h x ++ [Aggregate m'])) state =
    sum_fail_balance_incoming_active_opt ns1 ns0 packets state.
Proof.
move => ns0 ns1 packets state h x m'.
by apply: sum_fail_balance_incoming_active_opt_update2_app_eq.
Qed.

Lemma sum_fail_balance_incoming_active_opt_permutation_eq :
  forall ns1 ns1' ns packets state,
  Permutation ns1 ns1' ->
  sum_fail_balance_incoming_active_opt ns1 ns packets state =
  sum_fail_balance_incoming_active_opt ns1' ns packets state.
Proof.
move => ns1 ns1' ns.
elim: ns ns1 ns1' => [|n ns IH] ns1 ns1' packets state H_pm //=.
rewrite (IH _ _ _ _ H_pm).
break_match => //.
by rewrite (sum_fail_map_incoming_permutation_eq _ _ _ _ H_pm).
Qed.

Lemma sum_fail_balance_incoming_active_opt_all_head_eq : 
  forall ns ns' packets state n,
  sum_fail_balance_incoming_active_opt (n :: ns) ns' packets state = 
  sum_fail_balance_incoming_active_opt [n] ns' packets state * sum_fail_balance_incoming_active_opt ns ns' packets state.
Proof.
move => ns ns'.
elim: ns' ns => /=.
  move => ns packets state.
  by gsimpl.
move => n ns IH ns' packets state n'.
rewrite IH.
break_match => //.
gsimpl.
by aac_reflexivity.
Qed.

Lemma sum_fail_balance_incoming_active_opt_singleton_neq_update2_eq :
  forall ns f g h n n' ms,
    h <> n ->
    sum_fail_balance_incoming_active_opt [n] ns f g =
    sum_fail_balance_incoming_active_opt [n] ns (update2 name_eq_dec f h n' ms) g.
Proof.
elim => //=.
move => n0 ns IH f g h n n' ms H_neq.
gsimpl.
rewrite -IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq :
  forall ns f g h n,
  h <> n ->
  sum_fail_balance_incoming_active_opt [n] ns f g = 
  sum_fail_balance_incoming_active_opt [n] ns (collate name_eq_dec h f (map2snd Fail (filter_rel adjacent_to_dec h ns))) g.
Proof.
elim => //=.
move => n' ns IH f g h n H_neq.
case adjacent_to_dec => H_dec.
  rewrite -IH //.
  rewrite collate_neq //.
  by break_match; gsimpl; rewrite -sum_fail_balance_incoming_active_opt_singleton_neq_update2_eq.
break_match; gsimpl.
  rewrite -IH //.
  by rewrite collate_neq.
by rewrite -IH.
Qed.

Lemma sum_fail_balance_incoming_active_opt_collate_update2_eq :
  forall ns ns' h n f g l ms,
  ~ In n ns ->
  sum_fail_balance_incoming_active_opt ns' ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) g =
  sum_fail_balance_incoming_active_opt ns' ns (collate name_eq_dec h f l) g.
Proof.
elim => //=.
move => n' ns IH ns' h n f g l ms H_in.
have H_neq: n' <> n by move => H_in'; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
rewrite IH //.
break_match => //.
by rewrite sum_fail_map_incoming_collate_update2_eq.
Qed.

Lemma sum_fail_balance_incoming_active_opt_not_in_eq_alt_alt :
  forall ns0 ns1 from to ms f g,
  ~ In to ns0 ->
  sum_fail_balance_incoming_active_opt ns1 ns0 (update2 name_eq_dec f from to ms) g =
  sum_fail_balance_incoming_active_opt ns1 ns0 f g.
Proof.
elim => //.
move => n ns IH ns1 from to ms f g H_in.
have H_neq: to <> n by move => H_eq; case: H_in; left.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
rewrite /= IH //.
break_match => //.
by rewrite sum_fail_map_incoming_update2_not_eq_alt.
Qed.

Lemma Aggregation_adjacent_no_fail_not_in_adjacent_empty :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n (odnwNodes net) -> ~ In n failed ->
    forall n', In n' (odnwNodes net) -> In n' failed ->
    adjacent_to n n' ->
    forall d, net.(odnwState) n = Some d ->
         ~ In Fail (net.(odnwPackets) n' n) ->
        ~ NSet.In n' (adjacent d) ->
        net.(odnwPackets) n' n = [].
Proof.
move => net failed tr H_st.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 5 6 7.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in_n H_in_f n' H_in_n' H_in_f' H_adj d H_eq_d H_in H_ins.
  have H_neq: n <> n' by move => H_eq; rewrite -H_eq in H_in_f'.
  break_or_hyp; break_or_hyp => //.
  * by case: H0; apply: ordered_dynamic_failed_then_initialized; eauto.
  * rewrite collate_ls_not_in; last by apply not_in_not_in_filter_rel; eauto using in_remove_all_not_in.
    rewrite collate_neq //.    
    by apply: Aggregation_inactive_no_incoming; eauto.
  * have H_neq_n: h <> n by move => H_eq; rewrite H_eq in H0.
    have H_neq_n': h <> n' by move => H_eq; rewrite H_eq in H0.
    rewrite collate_ls_not_in; last by apply not_in_not_in_filter_rel; eauto using in_remove_all_not_in.
    rewrite collate_neq //.
    destruct_update => //.
    apply: IHH_st1; eauto.
    move => H_in'.
    case: H_in.
    rewrite collate_ls_not_in; last by apply not_in_not_in_filter_rel; eauto using in_remove_all_not_in.
    by rewrite collate_neq.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * have H_hd: head (odnwPackets net0 from to) = Some (Aggregate x) by find_rewrite.
    destruct_update; first find_injection.
    + have H_adj := Aggregation_aggregate_head_in_adjacent H_st1 _ H4 H5 _ H_hd H2.
      move: H10 {H_st2}.
      rewrite /= /update2.
      break_if; break_and; subst; repeat find_rewrite => //.
      break_or_hyp => //.
      move => H_in.
      by apply: IHH_st1; eauto.
    + move: H10 {H_st2}.
      rewrite /= /update2.
      break_if; break_and => //.
      move => H_in.
      by apply: IHH_st1; eauto.
  * have H_hd: head (odnwPackets net0 from to) = Some (Aggregate x) by find_rewrite.
    destruct_update; first find_injection.
    + have H_adj := Aggregation_aggregate_head_in_adjacent H_st1 _ H1 H0 _ H_hd H2.
      have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H_adj.
      by congruence.
    + have H_adj := Aggregation_aggregate_head_in_adjacent H_st1 _ H1 H0 _ H_hd H2.
      have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H_adj.
      by congruence.
  * have H_hd: head (odnwPackets net0 from to) = Some Fail by find_rewrite.
    destruct_update; first find_injection.
    + have H_adj := Aggregation_head_fail_then_adjacent H_st1 _ H4 H5 _ H_hd H2.
      move: H10 {H_st2}.
      rewrite /= /update2.
      break_if; break_and; subst; repeat find_rewrite => // H_in.
      -- have H_bef_new := Aggregation_in_after_all_fail_new H_st1 _ H1 H0 n'.
         find_rewrite.
         simpl in *.
         break_or_hyp; last by break_and.
         have H_bef_agg := Aggregation_in_after_all_fail_aggregate H_st1 _ H1 H0 _ H6.
         find_rewrite.
         simpl in *.
         destruct ms => //.
         destruct m0.
         ** have H_bef := H_bef_agg a.
            break_or_hyp; last by break_and.
            by case: H12; left.
         ** by case: H_in; left.
         ** by case: H9; left.
      -- break_or_hyp => //.
         repeat find_rewrite.         
         apply: IHH_st1; eauto.
         move => H_ins.
         case: H11.
         by auto with set.
    + have H_adj := Aggregation_head_fail_then_adjacent H_st1 _ H1 H0 _ H_hd H2.
      move: H10 {H_st2}.
      rewrite /= /update2.
      break_if; break_and; subst; repeat find_rewrite => // H_in.
      by apply: IHH_st1; eauto.
  * have H_hd: head (odnwPackets net0 from to) = Some Fail by find_rewrite.
    destruct_update; first find_injection.
    + have H_adj := Aggregation_head_fail_then_adjacent H_st1 _ H1 H0 _ H_hd H2.
      have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H_adj.
      by congruence.
    + have H_adj := Aggregation_head_fail_then_adjacent H_st1 _ H1 H0 _ H_hd H2.
      have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H_adj.
      by congruence.
  * have H_in: In New (odnwPackets net0 from to) by find_rewrite; left.
    destruct_update; first find_injection.
    + move: H16 {H_st2}.      
      rewrite /= /update2.
      break_if; break_and; subst; repeat find_rewrite => // H_in.
      -- have H_in' := Aggregation_in_new_failed_incoming_fail H_st1 _ H9 H11 _ H13 H_in.
         find_rewrite.
         simpl in *.
         by break_or_hyp.
      -- break_or_hyp => //.
         move => H_in'.
         apply: IHH_st1; eauto.
         move => H_ins.
         repeat find_rewrite.
         by auto with set.
    + move: H16 {H_st2}.      
      rewrite /= /update2.
      break_if; break_and; subst; repeat find_rewrite => // H_in.
      move => H_in'.
      by apply: IHH_st1; eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * destruct_update; first find_injection.
    + repeat find_rewrite.
      by apply: IHH_st1; eauto.
    + by apply: IHH_st1; eauto.
  * destruct_update; first find_injection.
    + repeat find_rewrite.
      move: H9.
      rewrite /= /update2 /=.
      break_if; break_and; subst => // H_in.
      by apply: IHH_st1; eauto.
    + move: H9.
      rewrite /= /update2 /=.
      break_if; break_and; subst => // H_in.
      by apply: IHH_st1; eauto.
  * destruct_update; first find_injection.
    + have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H.
      by congruence.
    + have [m' H_bal] := Aggregation_in_set_exists_find_balance H_st1 _ H1 H0 H2 H.
      by congruence.
  * destruct_update; first find_injection.
    + by apply: IHH_st1; eauto.
    + by apply: IHH_st1; eauto.
  * destruct_update; first find_injection.
    + by apply: IHH_st1; eauto.
    + by apply: IHH_st1; eauto.
  * destruct_update; first find_injection.
    + by apply: IHH_st1; eauto.
    + by apply: IHH_st1; eauto.
- move => n H_in_n H_in_f n' H_in_n' H_in_f' H_adj d H_eq_d H_in H_ins.
  have H_neq: h <> n by auto.
  have H_in_n_f: ~ In n failed by auto.
  break_or_hyp.
  * case: H_in.    
    apply adjacent_to_symmetric in H_adj.
    rewrite collate_map2snd_not_in_related //; last by apply: ordered_dynamic_nodes_no_dup; eauto.
    apply in_or_app.
    by right; left.
  * have H_neq': h <> n' by move => H_eq; rewrite -H_eq in H.
    rewrite collate_neq //.
    apply: IHH_st1; eauto.
    move => H_in'.
    case: H_in.
    by rewrite collate_neq.
Qed.

Require Import FunctionalExtensionality.

Lemma sum_fail_map_incoming_collate_ls_filter_rel_not_in_eq :
  forall l ns h f adj map,
  ~ In h ns ->
  NoDup l ->
  sum_fail_map_incoming ns (collate_ls name_eq_dec l f h New) h adj map =
  sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n l IH ns h f adj map H_in H_nd.
invc_NoDup.
destruct ns => //=.
rewrite IH; intuition.
rewrite sum_fail_map_incoming_update2_app_eq //.
rewrite /sum_fail_map /=.
case in_dec => /= H_dec.
  case (in_dec name_eq_dec n0 l) => H_dec'.
    rewrite collate_ls_NoDup_in // in H_dec.
    have H_neq: h <> n0.
      move => H_in'.
      rewrite H_in' in H_in.
      case: H_in.
      by left.
    rewrite /update2 /= in H_dec.
    move: H_dec.
    break_if; break_and; subst => //.
    break_or_hyp => //.
    move => H_in'.
    case in_dec => //= H_dec.
    apply in_app_or in H_in'; break_or_hyp => //.
    by simpl in *; break_or_hyp.
  rewrite collate_ls_not_in // in H_dec.
  rewrite /update2 /= in H_dec.
  move: H_dec.
  break_if; break_and; subst => //.
    move => H_in'.
    case in_dec => //= H_dec.
    case: H_dec.
    apply in_app_or in H_in'.
    case: H_in' => H_in' //.
    by case: H_in' => H_in'.
  break_or_hyp => //.
  move => H_in'.
  by case in_dec.
case (in_dec name_eq_dec n0 l) => H_dec'.
  rewrite collate_ls_NoDup_in // in H_dec.
  rewrite /update2 /= in H_dec.
  move: H_dec.
  break_if; break_and; subst => //.
  move => H_dec.
  case in_dec => //= H_dec''.
  case: H_dec.
  apply in_or_app.
  by left.
rewrite collate_ls_not_in // in H_dec.
rewrite /update2 /= in H_dec.
move: H_dec.
break_if; break_and; subst => //.  
  move => H_in'.
  case in_dec => /= H_dec'' //.
  case: H_in'.
  apply in_or_app.
  by left.
break_or_hyp => //.
move => H_dec.
by case in_dec.
Qed.

Lemma sum_fail_map_incoming_empty :
  forall ns f h map,
    sum_fail_map_incoming ns f h NSet.empty map = 1.
Proof.
elim => //=.
move => n ns IH f h map.
rewrite IH /sum_fail_map /=.
case in_dec => /= H_dec; last by gsimpl.
break_if; last by gsimpl.
find_apply_lem_hyp NSetFacts.mem_2.
by find_apply_lem_hyp NSetFacts.empty_1.
Qed.

Lemma sum_aggregate_msg_incoming_update2_new_eq :
  forall ns f h x,
  sum_aggregate_msg_incoming ns (update2 name_eq_dec f h x (f h x ++ [New])) x =
  sum_aggregate_msg_incoming ns f x.
Proof.
elim => //=.
move => n ns IH f h x.
rewrite IH.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- case: H_dec'.
  rewrite /update2 in H_dec.
  break_if; break_and; subst => //.
  find_apply_lem_hyp in_app_or.
  break_or_hyp => //.
  simpl in *.
  by break_or_hyp.
- case: H_dec.
  rewrite /update2 /=.
  break_if; break_and; subst => //.
  by apply in_or_app; left.
- rewrite /update2 /=.
  break_if; break_and; subst => //.
  rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
  by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_collate_ls_eq :
  forall l ns h f,
  sum_aggregate_msg_incoming ns (collate_ls name_eq_dec l f h New) h =
  sum_aggregate_msg_incoming ns f h.
Proof.
elim => //=.
move => n l IH ns h f.
rewrite IH //.
destruct ns => //=.
rewrite sum_aggregate_msg_incoming_update2_new_eq.
case in_dec => /= H_dec'.
  rewrite /update2 /= in H_dec'.
  move: H_dec'.
  break_if; break_and; subst => H_in' //=; last by case in_dec => /= H_dec''.
  apply in_app_or in H_in'.
  case: H_in' => H_in'; last by case: H_in'.
  by case: in_dec => /= H_dec'.
rewrite /update2 /= in H_dec'.
move: H_dec'.
break_if; break_and; subst => H_in' //=.
  have H_in'': ~ In Fail (f n0 h).
    move => H_in''.
    case: H_in'.
    apply in_or_app.
    by left.
  case in_dec => /= H_dec' //.
  rewrite /update2 /=.
  break_if; break_and; subst => //=.
  rewrite sum_aggregate_msg_split /= /aggregate_sum_fold /=.
  by gsimpl.
break_or_hyp => //.
case in_dec => /= H_dec' //.
rewrite /update2 /=.
by break_if; break_and.
Qed.

Lemma sum_aggregate_msg_collate_neq_eq :
  forall l f h n n',
    sum_aggregate_msg (collate name_eq_dec h f (map2snd New l) n' n) =
    sum_aggregate_msg (f n' n).
Proof.
elim => //=.
move => n0 l IH f h n n'.
rewrite IH.
rewrite /update2.
case sumbool_and => H_and //.
move: H_and => [H_eq' H_eq''].
rewrite H_eq' H_eq'' sum_aggregate_msg_split /= /aggregate_sum_fold /=.
by gsimpl.
Qed.

Lemma collate_map2snd_new_not_in :
  forall n h ns f,
    ~ In n ns ->
    collate name_eq_dec h f (map2snd New ns) h n = f h n.
Proof.
move => n h ns f.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
have H_neq: n <> n'.
  move => H_eq.
  rewrite H_eq in H_in.
  case: H_in.
  by left.
have H_in': ~ In n ns.
  move => H_in'.
  case: H_in.
  by right.
rewrite IH //.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
rewrite H_and' in H_in.
by case: H_in; left.
Qed.

Lemma collate_map2snd_new_cons_related_not_in :
  forall n h ns f,
    ~ In n ns ->
    collate name_eq_dec h f (map2snd New (n :: ns)) h n = f h n ++ [New].
Proof.
move => n h ns f H_in /=.
move: f n h H_in.
elim: ns  => //=.
  move => f n h H_in.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and //.
  by case: H_and => H_and.
move => n' ns IH f n h H_in.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
have H_neq: n <> n' by move => H_eq; case: H_in; left.
rewrite {3}/update2.
case sumbool_and => H_and; first by move: H_and => [H_and H_and'].
have IH' := IH f.
rewrite collate_map2snd_new_not_in //.
rewrite /update2.
case sumbool_and => H_and'; first by move: H_and' => [H_and' H_and'']; rewrite H_and'' in H_neq.
case sumbool_and => H_and'' //.
by case: H_and''.
Qed.

Lemma sum_aggregate_msg_incoming_collate_eq :
  forall ns l f h,
   NoDup l ->
   sum_aggregate_msg_incoming ns (collate name_eq_dec h f (map2snd New l)) h =
   sum_aggregate_msg_incoming ns f h.
Proof.
elim => //=.
move => n ns IH l f h H_nd.
rewrite IH // sum_aggregate_msg_collate_neq_eq.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- case: H_dec'.
  move: H_dec.
  elim: l H_nd => //.
  move => n' l IH' H_nd H_in.
  invc_NoDup.
  concludes.
  apply: IH' => //.
  case (name_eq_dec h n) => H_dec; last first.
    rewrite /= collate_neq // in H_in.
    rewrite /= /update2 in H_in.
    break_if; break_and; subst => //.
    exact: collate_in_in.
  subst.
  case (name_eq_dec n' n) => H_dec'; last by rewrite /= collate_neq_update2 // in H_in.
  subst.
  rewrite collate_map2snd_new_cons_related_not_in // in H_in.
  apply: collate_in_in.
  apply in_app_or in H_in.
  case: H_in => H_in //.
  simpl in *.
  by break_or_hyp.
- case: H_dec.
  exact: collate_in_in.
Qed.

Lemma sum_aggregate_msg_incoming_emp_1 :
  forall ns f h,
  (forall n, In n ns -> f n h = []) ->
  sum_aggregate_msg_incoming ns f h = 1.
Proof.
elim => //=.
move => n ns IH f h H_eq.
rewrite H_eq /=; last by left.
rewrite IH; first by gsimpl.
move => n' H_in'.
apply: H_eq.
by right.
Qed.

Lemma sum_aggregate_msg_incoming_active_collate_ls_singleton_eq :
  forall ns l h f,
  ~ In h ns ->
  ~ In h l ->
  sum_aggregate_msg_incoming_active [h] ns (collate_ls name_eq_dec l f h New) =
  sum_aggregate_msg_incoming_active [h] ns f.
Proof.
elim => //=.
move => n ns IH l h f H_in H_in'.
have H_neq: n <> h by auto.
have H_in'': ~ In h ns by auto.
case in_dec => /= H_dec; case in_dec => /= H_dec'.
- by rewrite IH.
- case: H_dec'.
  by rewrite collate_ls_neq_to in H_dec; last by auto.
- case: H_dec.
  by rewrite collate_ls_neq_to; last by auto.
- rewrite IH //.
  by rewrite collate_ls_neq_to; last by auto.
Qed.

Lemma sum_aggregate_msg_incoming_active_singleton_new_eq :
  forall ns l f h,
    NoDup l ->
    sum_aggregate_msg_incoming_active [h] ns (collate name_eq_dec h f (map2snd New l)) =
    sum_aggregate_msg_incoming_active [h] ns f.
Proof.
elim => //=.
move => n ns IH l f h H_nd.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- gsimpl.
  by rewrite IH.
- case: H_dec'.
  move: H_dec.
  elim: l H_nd => //.
  move => n' l IH' H_nd H_in.
  invc_NoDup.
  concludes.
  apply: IH' => //.
  case (name_eq_dec n' n) => H_dec'; last by rewrite /= collate_neq_update2 // in H_in.
  subst.
  rewrite collate_map2snd_new_cons_related_not_in // in H_in.
  rewrite collate_map2snd_new_not_in //.
  apply in_app_or in H_in.
  simpl in *.
  by break_or_hyp => //; break_or_hyp.
- case: H_dec.
  move: H_dec'.
  elim: l H_nd => //.
  move => n' l IH' H_nd H_in.
  invc_NoDup.
  concludes.
  concludes.
  case (name_eq_dec n' n) => H_dec'; last by rewrite /= collate_neq_update2.
  subst. 
  rewrite collate_map2snd_new_cons_related_not_in //.
  apply in_or_app.
  by left.
- gsimpl.
  rewrite IH //.
  by rewrite sum_aggregate_msg_collate_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_active_all_empty_1 :
  forall ns h f,
  (forall n, In n ns -> f h n = []) ->
  sum_aggregate_msg_incoming_active [h] ns f = 1.
Proof.
elim => //=.
move => n ns IH h f H_emp.
case in_dec => /= H_dec.
- by rewrite H_emp in H_dec; last by left.
- rewrite IH.
  * rewrite H_emp; last by left.
    by gsimpl.
  * move => n0 H_in.
    apply: H_emp.
    by right.
Qed.

Lemma sum_fail_balance_incoming_active_opt_collate_ls_not_in_eq : 
  forall ns l f st h,
  ~ In h ns ->
  sum_fail_balance_incoming_active_opt [h] ns (collate_ls name_eq_dec l f h New) st =
  sum_fail_balance_incoming_active_opt [h] ns f st.
Proof.
elim => //=.
move => n ns IH l f st h H_in.
have H_neq: h <> n by auto.
have H_in': ~ In h ns by auto.
break_match; last by rewrite IH.
gsimpl.
rewrite IH //.
rewrite /sum_fail_map /=.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- case: H_dec'.
  by rewrite collate_ls_neq_to // in H_dec.
- case: H_dec.
  by rewrite collate_ls_neq_to.
Qed.

Lemma sum_fail_balance_incoming_active_opt_collate_neq_eq :
  forall ns l h f st,
    NoDup l ->
    sum_fail_balance_incoming_active_opt [h] ns (collate name_eq_dec h f (map2snd New l)) st = 
    sum_fail_balance_incoming_active_opt [h] ns f st.
Proof.
elim => //=.
move => n ns IH l h f st H_nd.
break_match; last by rewrite IH.
gsimpl.
rewrite IH //.
rewrite /sum_fail_map /=.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- case: H_dec'.
  move: H_dec.
  elim: l H_nd => //.
  move => n' l IH' H_nd H_in.
  invc_NoDup.
  concludes.
  apply: IH' => //.
  case (name_eq_dec n' n) => H_dec'; last by rewrite /= collate_neq_update2 // in H_in.
  subst.
  rewrite collate_map2snd_new_cons_related_not_in // in H_in.
  rewrite collate_map2snd_new_not_in //.
  apply in_app_or in H_in.
  simpl in *.
  by break_or_hyp => //; break_or_hyp.  
- case: H_dec.
  exact: collate_in_in.
Qed.

Lemma sum_fail_balance_incoming_active_opt_emp_eq :  
  forall ns h f st,
  (forall n, In n ns -> f h n = []) ->
  sum_fail_balance_incoming_active_opt [h] ns f st = 1.
Proof.
elim => //=.
move => n ns IH h f st H_emp.
break_match; last first.
  rewrite IH //.
  move => n0 H_in.
  apply: H_emp.
  by right.
gsimpl.
rewrite IH; last by move => n0 H_in; apply: H_emp; right.
rewrite H_emp; last by left.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_collate_ls_neq_eq :
  forall l ns h n f,
  n <> h ->
  sum_aggregate_msg_incoming ns (collate_ls name_eq_dec l f h New) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n l IH ns h n' f H_neq.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_active_collate_ls_not_in_eq :
  forall ns ns' l f h,
  ~ In h ns ->
  sum_aggregate_msg_incoming_active ns' ns (collate_ls name_eq_dec l f h New) = 
  sum_aggregate_msg_incoming_active ns' ns f.
Proof.
elim => //=.
move => n ns IH ns' l f h H_in.
have H_neq: n <> h by auto.
have H_in'': ~ In h ns by auto.
by rewrite IH //= sum_aggregate_msg_incoming_collate_ls_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_collate_neq_not_in_eq :
 forall ns f h n ms,
   ~ In h ns ->
   sum_aggregate_msg_incoming ns (collate name_eq_dec h f ms) n = 
   sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n ns IH f h n' ms H_in.
have H_neq': h <> n by auto.
have H_in': ~ In h ns by auto.
rewrite IH //.
case in_dec => /= H_dec; case in_dec => /= H_dec' //.
- case: H_dec'.
  by rewrite collate_neq // in H_dec.
- case: H_dec.
  by rewrite collate_neq.
- by rewrite collate_neq.
Qed.

Lemma sum_aggregate_msg_incoming_active_collate_not_in_allns_eq :
  forall ns ns' f h ms,
  ~ In h ns' ->
  sum_aggregate_msg_incoming_active ns' ns (collate name_eq_dec h f ms) =
  sum_aggregate_msg_incoming_active ns' ns f.
Proof.
elim => //=.
move => n ns IH ns' f h ms H_in.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_collate_neq_not_in_eq.
Qed.

Lemma sum_fail_map_incoming_collate_ls_neq_eq :
  forall ns l f h n adj map,
    h <> n ->
    sum_fail_map_incoming ns (collate_ls name_eq_dec l f h New) n adj map = 
    sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n ns IH l f h n' adj map H_neq.
rewrite IH //.
rewrite /sum_fail_map.
by rewrite collate_ls_neq_to.
Qed.

Lemma sum_fail_balance_incoming_active_collate_ls_not_in_eq :
  forall ns ns' l f h st,
    ~ In h ns ->
    sum_fail_balance_incoming_active_opt ns' ns (collate_ls name_eq_dec l f h New) st =
    sum_fail_balance_incoming_active_opt ns' ns f st.
Proof.
elim => //=.
move => n ns IH ns' l f h st H_in.
have H_neq: h <> n by auto.
have H_in'': ~ In h ns by auto.
break_match; rewrite IH //=.
by rewrite sum_fail_map_incoming_collate_ls_neq_eq.
Qed.

Lemma sum_fail_balance_incoming_active_opt_not_in_allns_eq :
  forall ns ns' f st h ms,
  ~ In h ns' ->
  sum_fail_balance_incoming_active_opt ns' ns (collate name_eq_dec h f ms) st =
  sum_fail_balance_incoming_active_opt ns' ns f st.
Proof.
elim => //=.
move => n ns IH ns' f st h ms H_in.
rewrite IH //.
break_match => //.
by rewrite sum_fail_map_incoming_collate_not_in_eq.
Qed.

Lemma sum_fail_balance_incoming_active_opt_update_not_in :
  forall ns ns' f st h d,
    ~ In h ns ->
    sum_fail_balance_incoming_active_opt ns' ns f (update name_eq_dec st h (Some d)) = 
    sum_fail_balance_incoming_active_opt ns' ns f st.
Proof.
elim => //=.
move => n ns IH ns' f st h d H_in.
have H_neq: n <> h by auto.
have H_in': ~ In h ns by auto.
rewrite IH //.
by destruct_update.
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
  conserves_network_mass_opt (remove_all name_eq_dec failed net.(odnwNodes)) net.(odnwNodes) net.(odnwPackets) net.(odnwState).
Proof.
move => net failed tr H_step.
rewrite /conserves_network_mass_opt.
have H_cons := Aggregation_conserves_node_mass_all H_step.
apply global_conservation in H_cons.
rewrite /conserves_mass_globally in H_cons.
rewrite H_cons {H_cons}.
set sb := sum_balance _.
set saa := sum_aggregate_msg_incoming_active _ _ _.
set sfb := sum_fail_balance_incoming_active_opt _ _ _ _.
suff H_suff: sb = saa * sfb by aac_rewrite H_suff; rewrite /Nodes_data /=; aac_reflexivity.
rewrite /sb /saa /sfb {sb saa sfb}.
remember step_ordered_dynamic_failure_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {2 3 4 6 7 8 10 11 12} H_eq_o {H_eq_o}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init {H_init} /=; gsimpl.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move {H_step2}.
  have H_f: ~ In h failed0.
    move => H_f.
    case: H0.
    by apply: ordered_dynamic_failed_then_initialized; eauto.
  have H_cn := remove_all_cons name_eq_dec failed0 h (odnwNodes net0).
  break_or_hyp; break_and => //.
  find_rewrite.
  rewrite /=.
  destruct_update => //.
  have H_inn : ~ In h (remove_all name_eq_dec failed0 net0.(odnwNodes)) by move => H_in; eauto using in_remove_all_was_in.
  rewrite Nodes_data_opt_not_in_eq //.
  rewrite /InitData /= sumM_empty; last by auto with set.
  gsimpl.
  rewrite IHH_step1 {IHH_step1}.
  case in_dec => /= H_dec.
    contradict H_dec.
    rewrite collate_ls_not_in; last exact: not_in_not_in_filter_rel.
    rewrite collate_map2snd_not_in //.
    by rewrite (Aggregation_inactive_no_incoming H_step1).
  move {H_dec}.  
  rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
  rewrite sum_aggregate_msg_incoming_active_all_head_eq.
  rewrite collate_ls_not_in; last exact: not_in_not_in_filter_rel.
  rewrite collate_map2snd_not_in //.
  rewrite (Aggregation_inactive_no_incoming H_step1) //=.
  gsimpl.
  rewrite sum_fail_map_incoming_collate_ls_filter_rel_not_in_eq //; last by apply: NoDup_filter_rel; apply: NoDup_remove_all; apply: ordered_dynamic_nodes_no_dup; eauto.
  rewrite sum_fail_map_incoming_collate_not_in_eq //.
  rewrite sum_fail_map_incoming_empty.
  rewrite sum_aggregate_msg_incoming_collate_ls_eq.
  rewrite sum_aggregate_msg_incoming_collate_eq; last by apply: NoDup_filter_rel; apply: NoDup_remove_all; apply: ordered_dynamic_nodes_no_dup; eauto.
  rewrite sum_aggregate_msg_incoming_emp_1; last by move => n H_in; apply: Aggregation_inactive_no_incoming; eauto.
  gsimpl.
  have H_not_in: ~ In h (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed0 (odnwNodes net0))).
    move => H_in.
    find_apply_lem_hyp filter_rel_related.
    break_and.
    by find_apply_lem_hyp adjacent_to_irreflexive.
  rewrite sum_aggregate_msg_incoming_active_collate_ls_singleton_eq //.
  rewrite sum_aggregate_msg_incoming_active_singleton_new_eq; last by apply: NoDup_filter_rel; apply: NoDup_remove_all; apply: ordered_dynamic_nodes_no_dup; eauto.
  rewrite sum_aggregate_msg_incoming_active_all_empty_1; last by move => n H_in; apply: ordered_dynamic_no_outgoing_uninitialized; eauto.
  gsimpl.
  rewrite sum_fail_balance_incoming_active_opt_collate_ls_not_in_eq //.
  rewrite sum_fail_balance_incoming_active_opt_collate_neq_eq; last by apply: NoDup_filter_rel; apply: NoDup_remove_all; apply: ordered_dynamic_nodes_no_dup; eauto.
  rewrite sum_fail_balance_incoming_active_opt_emp_eq; last by move => n H_in; apply: ordered_dynamic_no_outgoing_uninitialized; eauto.
  gsimpl.
  rewrite sum_aggregate_msg_incoming_active_collate_ls_not_in_eq //.
  rewrite sum_aggregate_msg_incoming_active_collate_not_in_allns_eq //.
  rewrite sum_fail_balance_incoming_active_collate_ls_not_in_eq //.
  rewrite sum_fail_balance_incoming_active_opt_not_in_allns_eq //.
  by rewrite sum_fail_balance_incoming_active_opt_update_not_in.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H_step2}.
  rewrite /= in IHH_step1.
  have H_inn : In to (remove_all name_eq_dec failed0 net0.(odnwNodes)) by exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  move: H_step1 => H_step1'.  
  have H_step1: @step_ordered_dynamic_failure_star _ _ _ _ Aggregation_FailMsgParams step_ordered_dynamic_failure_init (failed0, net0) tr1 by auto.
  move {H_step1'}.
  have H_nd := NoDup_remove_all name_eq_dec failed0 (ordered_dynamic_nodes_no_dup H_step1).
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_to_nin: ~ In to ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In to ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_opt_split /=.
  rewrite {2}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  find_rewrite.
  rewrite Nodes_data_opt_not_in_eq //.
  rewrite Nodes_data_opt_not_in_eq //.  
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_opt_split /=.
  find_rewrite.
  rewrite {2}/update.
  case name_eq_dec => H_dec {H_dec} //.
  gsimpl.
  move => IH.
  case (in_dec name_eq_dec from net0.(odnwNodes)) => H_in_from; last by find_rewrite_lem (ordered_dynamic_no_outgoing_uninitialized H_step1 _ H_in_from).
  net_handler_cases => //=.
  * have H_hd: head (odnwPackets net0 from to) = Some (Aggregate x) by repeat find_rewrite.
    have H_ins := Aggregation_aggregate_head_in_adjacent H_step1 _ H1 H0 _ H_hd H2.
    rewrite sumM_add_map //.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    case (In_dec Msg_eq_dec Fail (net0.(odnwPackets) from to)) => H_in_fail.
      rewrite (Aggregation_sum_aggregate_msg_incoming_update2_fail_eq _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1) _ H3) //.
      rewrite (Aggregation_sum_aggregate_msg_incoming_update2_aggregate_in_fail_add _ _ _ H_ins _ (ordered_dynamic_nodes_no_dup H_step1) _ H3) //.
      by gsimpl.
    rewrite (Aggregation_sum_aggregate_msg_incoming_update2_aggregate _ _ _ H_in_from (ordered_dynamic_nodes_no_dup H_step1) H_in_fail H3).
    rewrite (@no_fail_sum_fail_map_incoming_add_eq AggregationMsg_Aggregation _ _ _ _ _ _ _ _ _ H_in_from (ordered_dynamic_nodes_no_dup H_step1) H3 H_in_fail).
    by aac_reflexivity.
  * have H_hd: head (odnwPackets net0 from to) = Some (Aggregate x) by repeat find_rewrite.
    have H_ins := Aggregation_aggregate_head_in_adjacent H_step1 _ H1 H0 _ H_hd H2.
    have [m5 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H0 H2 H_ins.
    by congruence.
  * have H_in: In Fail (odnwPackets net0 from to) by find_rewrite; left.
    have H_in': ~ In Fail ms.
      have H_le := Aggregation_le_one_fail H_step1 _ H1 H0 from.
      find_rewrite.
      move: H_le.
      rewrite /=.
      case H_cnt: (count_occ _ _ _) => H_le; last by omega.
      by apply count_occ_not_In in H_cnt.
    have H_hd: head (odnwPackets net0 from to) = Some Fail by repeat find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent H_step1 _ H1 H0 _ H_hd H2.
    rewrite (sumM_remove_remove H_ins H).
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    have H_bef := Aggregation_in_after_all_fail_aggregate H_step1 _ H1 H0 from H_in_from.
    rewrite (Aggregation_sum_aggregate_msg_incoming_fail_update2_eq _ _ _ H_bef _ (ordered_dynamic_nodes_no_dup H_step1)) //.
    rewrite (@sum_fail_map_incoming_fail_remove_eq AggregationMsg_Aggregation _ _ _ _ _ _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1) H_ins _ H_in' H) //.
    by gsimpl.
  * have H_hd: head (odnwPackets net0 from to) = Some Fail by repeat find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent H_step1 _ H1 H0 _ H_hd H2.
    have [m5 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H0 H2 H_ins.
    by congruence.
  * have H_in: In New (odnwPackets net0 from to) by find_rewrite; left.
    have H_ins := Aggregation_new_incoming_not_in_adj H_step1 _ H1 H0 H_in H2.
    rewrite (sumM_add_add _ _ H_ins).
    gsimpl.
    rewrite IH {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_balance_incoming_active_opt_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    rewrite sum_aggregate_msg_incoming_new_update2_eq //.
    by rewrite sum_fail_map_incoming_new_eq.
- find_apply_lem_hyp input_handlers_IOHandler.
  move {H_step2}.
  rewrite /= in IHH_step1.
  have H_inn : In h (remove_all name_eq_dec failed0 net0.(odnwNodes)) by exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  move: H_step1 => H_step1'.  
  have H_step1: @step_ordered_dynamic_failure_star _ _ _ _ Aggregation_FailMsgParams step_ordered_dynamic_failure_init (failed0, net0) tr1 by auto.
  move {H_step1'}.
  have H_nd := NoDup_remove_all name_eq_dec failed0 (ordered_dynamic_nodes_no_dup H_step1).
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_h_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_h_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_opt_split /=.
  rewrite {2}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  find_rewrite.
  rewrite Nodes_data_opt_not_in_eq //.
  rewrite Nodes_data_opt_not_in_eq //.  
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_opt_split /=.
  find_rewrite.
  rewrite {2}/update.
  case name_eq_dec => H_dec {H_dec} //.
  gsimpl.
  move => IH.
  io_handler_cases => //=.
  * rewrite sum_fail_balance_incoming_active_opt_not_in_eq_alt //.
    by rewrite sum_fail_balance_incoming_active_opt_not_in_eq_alt.
  * have H_x_nodes: In x net0.(odnwNodes).
      have H_and := Aggregation_in_adj_or_incoming_fail H_step1 _ H1 H0 H2 H.
      by break_or_hyp; break_and.    
    have H_neq: h <> x.
      move => H_eq.
      have H_self := Aggregation_node_not_adjacent_self H_step1 H1 H0 H2.
      by rewrite {1}H_eq in H_self.
    rewrite (sumM_add_map _ H H5).
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_neq_eq //.
    case (In_dec name_eq_dec x failed0) => H_dec.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H1 H0 H2 H.
      case: H_or => H_or; first by break_and.
      move: H_or => [H_dec' [H_n H_in]] {H_dec'}.
      have H_x_ex: ~ In x (remove_all name_eq_dec failed0 net0.(odnwNodes)) by eauto using in_remove_all_not_in.
      rewrite H_inn in H_x_ex.
      have H_x_nin: ~ In x ns0 by move => H_x_in; case: H_x_ex; apply in_or_app; left.
      have H_x_nin': ~ In x ns1 by move => H_x_in; case: H_x_ex; apply in_or_app; right; right.
      rewrite sum_fail_balance_incoming_active_opt_not_in_eq_alt2 //.
      rewrite sum_fail_balance_incoming_active_opt_not_in_eq_alt2 //.
      rewrite (Aggregation_sum_fail_map_incoming_add_aggregate_eq _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1)) //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      by aac_reflexivity.
    have H_in := Aggregation_not_failed_no_fail H_step1 _ H_x_nodes H_dec h.
    have H_in' := Aggregation_not_failed_no_fail H_step1 _ H1 H0 x.
    rewrite sum_fail_balance_incoming_active_opt_update_not_in_eq //.
    rewrite sum_fail_balance_incoming_active_opt_update_not_in_eq //.    
    rewrite Aggregation_sum_fail_balance_incoming_active_opt_update2_app_eq //.
    rewrite Aggregation_sum_fail_balance_incoming_active_opt_update2_app_eq //.
    rewrite (sum_fail_map_incoming_not_in_fail_add_update2_eq _ _ _ _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1)) //.
    have H_in_x: In x (remove_all name_eq_dec failed0 net0.(odnwNodes)) by exact: in_remove_all_preserve.
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
      rewrite (Aggregation_sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1)) //.
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
    rewrite (Aggregation_sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1)) //.
    by aac_reflexivity.
  * have [m' H_snt] := Aggregation_in_set_exists_find_balance H_step1 _ H1 H0 H2 H.
    by congruence.
  * have H_eq: update name_eq_dec (odnwState net0) h (Some d) = odnwState net0.
      apply functional_extensionality.
      move => x0.
      by destruct_update.
    by rewrite H_eq.    
  * have H_eq: update name_eq_dec (odnwState net0) h (Some d) = odnwState net0.
      apply functional_extensionality.
      move => x0.
      by destruct_update.
    by rewrite H_eq.
  * have H_eq: update name_eq_dec (odnwState net0) h (Some d) = odnwState net0.
      apply functional_extensionality.
      move => x0.
      by destruct_update.
    by rewrite H_eq.
- move {H_step2}.
  rewrite /= in IHH_step1.
  have H_inn : In h (remove_all name_eq_dec failed0 net0.(odnwNodes)) by exact: in_remove_all_preserve.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  move: H_step1 => H_step1'.  
  have H_step1: @step_ordered_dynamic_failure_star _ _ _ _ Aggregation_FailMsgParams step_ordered_dynamic_failure_init (failed0, net0) tr1 by auto.
  move {H_step1'}.
  have H_nd := NoDup_remove_all name_eq_dec failed0 (ordered_dynamic_nodes_no_dup H_step1).
  rewrite H_inn in H_nd.
  have H_nin := NoDup_mid_not_in _ _ _ H_nd.
  have H_to_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.    
  move: IHH_step1.
  have H_ex := remove_all_NoDup_split name_eq_dec _ _ _ _ (ordered_dynamic_nodes_no_dup H_step1) H_inn.
  rewrite H_ex.  
  rewrite H_inn.
  have H_nd': NoDup ns0 by move: H_nd; exact: NoDup_app_left.
  have H_nd'': NoDup ns1 by apply NoDup_app_right in H_nd; inversion H_nd.
  have [d H_eq] := ordered_dynamic_initialized_state H_step1 _ H1.
  rewrite 2!Nodes_data_opt_split /= H_eq.
  rewrite 2!sum_balance_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_balance_incoming_active_opt_split /= H_eq.
  gsimpl.
  move => IH.
  rewrite filter_rel_self_eq.
  set l := collate _ _ _ _.
  rewrite sum_balance_Nodes_data_opt_distr in IH.
  rewrite sum_balance_Nodes_data_opt_distr.
  move: IH.
  rewrite -2!sum_aggregate_msg_incoming_active_split.
  move => IH.
  set sa := sum_aggregate_msg_incoming_active _ _ _.
  set sf1 := sum_fail_balance_incoming_active_opt _ _ _ _.
  set sf2 := sum_fail_balance_incoming_active_opt _ _ _ _.
  have ->: sa * sf1 * sf2 =
    sa * @sum_fail_balance_incoming_active_opt AggregationMsg_Aggregation _ AggregationData_Data net0.(odnwNodes) (ns0 ++ ns1) l (odnwState net0).
    rewrite sum_fail_balance_incoming_active_opt_split.
    by gsimpl.
  rewrite /sa /sf1 /sf2 {sa sf1 sf2}.
  move: IH.
  set saa := sum_aggregate_msg_incoming_active _ _ _.
  set sai := sum_aggregate_msg_incoming _ _ _.
  set sf1 := sum_fail_balance_incoming_active_opt _ _ _ _.
  set sf2 := sum_fail_balance_incoming_active_opt _ _ _ _.
  set sfm := sum_fail_map_incoming _ _ _ _ _.
  have ->: saa * sai * sf1 * sf2 * sfm = 
    saa * sai * @sum_fail_balance_incoming_active_opt AggregationMsg_Aggregation _ AggregationData_Data net0.(odnwNodes) (ns0 ++ ns1) (odnwPackets net0) (odnwState net0) * sfm.
    rewrite sum_fail_balance_incoming_active_opt_split.
    by gsimpl.
  rewrite /saa /sai /sf1 /sf2 /sfm {saa sai sf1 sf2 sfm}.
  set sums := sumM _ _.
  set sb := sum_balance _.
  move => IH.
  set sam := sum_aggregate_msg_incoming_active _ _ _.  
  set sfbi := sum_fail_balance_incoming_active_opt _ _ _ _.
  suff H_suff: sb * sums * sums^-1 = sam * sfbi by move: H_suff; gsimpl.
  aac_rewrite IH.
  move {IH}.
  rewrite /sums /sb /sam /sfbi {sums sb sam sfbi}.
  rewrite /l {l}.
  have H_acs := sumM_balance_fail_active_eq_with_self H_step1 _ H1 H0 H_eq.
  have H_pmn: Permutation (h :: ns0 ++ ns1) (remove_all name_eq_dec failed0 net0.(odnwNodes)) by rewrite H_inn; exact: Permutation_middle.
  rewrite -(sumM_active_eq_sym _ _ H_pmn) /= /sum_active_fold in H_acs.
  move: H_acs {H_pmn}.
  case: ifP => H_mem; first by apply NSetFacts.mem_2 in H_mem; contradict H_mem; exact: (Aggregation_node_not_adjacent_self H_step1).
  set s1 := sum_fail_map_incoming _ _ _ _ _.
  move => H_acs {H_mem}.  
  have H_acs': 
    (sumM (adjacent d) (balance d))^-1 * s1 =
    (sumM_active (adjacent d) (balance d) (ns0 ++ ns1))^-1.
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
  have H_nd := ordered_dynamic_nodes_no_dup H_step1.
  move: ns H_ex => ns H_ex {ns0 ns1}.
  have H_in_nodes := H1.
  apply in_split in H1.
  move: H1 => [ns0 [ns1 H_in_from]].
  have H_in_nd: forall n, In n (ns0 ++ ns1) -> In n net0.(odnwNodes).
    move => n H_in.
    rewrite H_in_from.
    find_apply_lem_hyp in_app_or.
    break_or_hyp; first by apply in_or_app; left.
    apply in_or_app.
    by right; right.
  rewrite H_in_from in H_ex.
  rewrite H_in_from in H_nd.
  have H_nin: ~ In h (ns0 ++ ns1) by exact: NoDup_mid_not_in.
  apply NoDup_remove_1 in H_nd.
  rewrite remove_partition in H_ex.
  have H_pm: Permutation net0.(odnwNodes) (h :: ns0 ++ ns1).
    rewrite H_in_from.
    apply Permutation_sym.
    exact: Permutation_middle.
  move {H_in_from}.
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_permutation_eq _ _ H_pm).
  rewrite (sum_fail_balance_incoming_active_opt_permutation_eq _ _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_fail_balance_incoming_active_opt_permutation_eq _ _ _ H_pm).
  move: H_nd H_nin H_in_nd ns H_ex {H_pm}.
  set ns' := ns0 ++ ns1.
  move: H_eq => H_eq_d.
  elim: ns' => /=; rewrite (Aggregation_self_channel_empty H_step1) //=; first by move => H_nd H_in H_in_nd ns H_eq; rewrite -H_eq remove_all_nil /=; gsimpl.
  move => n ns' IH H_nd H_in H_in_nd ns.
  inversion H_nd => {x H l H1}.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_in': ~ In h ns' by move => H_in'; case: H_in; right.
  have H_in_n_nd: In n net0.(odnwNodes) by auto.
  have H_in_nd': forall n0, In n0 ns' -> In n0 net0.(odnwNodes) by auto.
  move {H_in H_nd H_in_nd}.
  case name_eq_dec => H_dec //=.
  move => H_ex.
  have H_cn := remove_all_cons name_eq_dec failed0 n (remove name_eq_dec h ns').
  rewrite H_ex in H_cn => {H_ex}.
  break_or_hyp; break_and.
    match goal with | H : _ = remove_all _ _ _ |- _ => symmetry in H end.
    move {H_dec}.
    have IH' := IH H3 H_in' H_in_nd' _ H.
    move {IH}.
    move: IH'.
    move => IH.
    case in_dec => /= H_dec; case H_mem: (NSet.mem n d.(adjacent)).
    - apply NSetFacts.mem_2 in H_mem.      
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns') in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq (n :: ns')).
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      aac_rewrite IH.
      move {IH}.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).      
      rewrite -(sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq _ _ _ H_neq).
      by gsimpl; aac_reflexivity.
    - move/negP: H_mem => H_mem.
      have H_ins: ~ NSet.In n (adjacent d).
        move => H_ins.
        find_apply_lem_hyp NSetFacts.mem_1.
        by congruence.
      (*
      have H_new := Aggregation_incoming_fail_then_incoming_new_or_in_adjacent H_step1 _ H_in_nodes H0 _ H_dec H_eq_d.
      break_or_hyp; break_and => //.
      *)
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns') in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq (n :: ns')).
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      aac_rewrite IH.
      move {IH}.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq). 
      rewrite -(sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq _ _ _ H_neq).
      by gsimpl; aac_reflexivity.
    - apply NSetFacts.mem_2 in H_mem.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H_in_nodes H0 H_eq_d H_mem.
      by case: H_or => H_or; break_and.
    - move/negP: H_mem => H_mem.
      have H_ins: ~ NSet.In n (adjacent d).
        move => H_ins.
        find_apply_lem_hyp NSetFacts.mem_1.
        by congruence.
      have H_eq_emp: odnwPackets net0 n h = [].
        case (adjacent_to_dec h n) => H_adj; last by rewrite (Aggregation_not_adjacent_no_incoming H_step1).
        by apply: (Aggregation_adjacent_no_fail_not_in_adjacent_empty H_step1); eauto.
      have H_notin: forall m', ~ In (Aggregate m') (odnwPackets net0 n h) by rewrite H_eq_emp; auto.
      rewrite (Aggregation_sum_aggregate_ms_no_aggregate_1 _ H_notin).
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
      rewrite sum_fail_balance_incoming_active_opt_all_head_eq in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns') in IH.
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq (n :: ns')).
      rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      aac_rewrite IH.
      move {IH}.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
      rewrite -(sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq _ _ _ H_neq).
      by gsimpl; aac_reflexivity.
  match goal with | H : _ = _ :: remove_all _ _ _ |- _ => symmetry in H end.
  move: H.
  move {H_dec}.
  case: ns IH H2 H3 H_in' => //.
  move => n' ns IH H_in H_nd H_nin H_ex.
  have H_ex': remove_all name_eq_dec failed0 (remove name_eq_dec h ns') = ns by inversion H_ex.
  have H_eq: n = n' by inversion H_ex.
  rewrite -H_eq {n' H_eq H_ex}.
  have IH' := IH H_nd H_nin H_in_nd' _ H_ex'.
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
      by apply: (Aggreation_in_adj_adjacent_to H_step1); eauto.
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; rewrite collate_neq // (Aggregation_self_channel_empty H_step1).
    move {H_dec}.
    have [d' H_d'] := ordered_dynamic_initialized_state H_step1 _ H_in_n_nd.
    rewrite H_d'.
    have H_ins: ~ NSet.In h d'.(adjacent).
      move => H_ins.
      case: H_Adj.
      move: H_ins.
      exact: (Aggreation_in_adj_adjacent_to H_step1).
    have H_ins': ~ NSet.In n d.(adjacent).
      move => H_ins'.
      case: H_Adj'.
      move: H_ins'.
      exact: (Aggreation_in_adj_adjacent_to H_step1).
    case in_dec => /= H_dec.
      rewrite collate_map2snd_not_related // in H_dec. 
      by rewrite (Aggregation_not_adjacent_no_incoming H_step1) in H_dec.
    move {H_dec}.
    rewrite (collate_map2snd_not_related _ _ _ name_eq_dec _ _ _ _ _ _ H_Adj).
    rewrite (collate_neq _ _ name_eq_dec _ _ _ _ _ H_neq) //.
    rewrite (Aggregation_self_channel_empty H_step1) //=.
    rewrite {2}/sum_fail_map /=.
    have H_emp_hn: odnwPackets net0 h n = [] by rewrite (Aggregation_not_adjacent_no_incoming H_step1).
    have H_emp_nh: odnwPackets net0 n h = [] by rewrite (Aggregation_not_adjacent_no_incoming H_step1).
    rewrite H_emp_hn H_emp_nh /sum_fail_map /=.
    rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
    rewrite sum_fail_balance_incoming_active_opt_all_head_eq in IH'.
    rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
    rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns') in IH'.
    rewrite (sum_fail_balance_incoming_active_opt_all_head_eq (n :: ns')).
    rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
    rewrite sum_aggregate_msg_incoming_active_all_head_eq.
    rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    aac_rewrite IH'.
    move {IH'}.
    rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
    rewrite -(sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq _ _ _ H_neq).
    rewrite (sum_fail_map_incoming_not_adjacent_collate_eq _ _ _ _ _ H_Adj).
    rewrite (sum_aggregate_msg_incoming_not_adjacent_collate_eq _ _ _ H_Adj).
    by gsimpl; aac_reflexivity.
  rewrite /=.
  have [d' H_d'] := ordered_dynamic_initialized_state H_step1 _ H_in_n_nd.
  rewrite H_d'.
  have H_adj': adjacent_to n h by apply adjacent_to_symmetric in H_Adj.
  have H_in_f: ~ In Fail (net0.(odnwPackets) h n) by exact: (Aggregation_not_failed_no_fail H_step1).
  have H_in_f': ~ In Fail (net0.(odnwPackets) n h) by exact: (Aggregation_not_failed_no_fail H_step1).
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
  gsimpl.
  rewrite sum_fail_balance_incoming_active_opt_all_head_eq.
  rewrite sum_fail_balance_incoming_active_opt_all_head_eq in IH'.
  rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
  rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns') in IH'.
  rewrite (sum_fail_balance_incoming_active_opt_all_head_eq (n :: ns')).
  rewrite (sum_fail_balance_incoming_active_opt_all_head_eq ns').
  rewrite sum_aggregate_msg_incoming_active_all_head_eq.
  rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  move: IH'.
  gsimpl.
  move => IH.
  set u2 := update2 _ _ _ _ _.
  set cl := collate _ _ _ _.
  rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
  rewrite -(sum_fail_balance_incoming_active_opt_singleton_neq_collate_eq _ _ _ H_neq).
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
  rewrite sum_aggregate_msg_incoming_active_eq_not_in_eq //.
  rewrite {1}/cl {1}/u2.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite {1}/cl /u2.
  rewrite sum_aggregate_msg_incoming_collate_update2_notin_eq //.
  rewrite sum_aggregate_msg_incoming_collate_msg_for_notin_eq //.
  rewrite {1 2}/cl /u2.
  rewrite sum_fail_map_incoming_collate_not_in_eq //.
  rewrite sum_fail_map_incoming_not_in_eq //. 
  rewrite sum_fail_balance_incoming_active_opt_collate_update2_eq //.
  rewrite sum_fail_balance_incoming_active_opt_collate_update2_eq //.  
  rewrite sum_fail_balance_incoming_active_opt_not_in_eq_alt_alt //.
  rewrite /cl {u2 cl}.
  repeat break_if.
  * find_apply_lem_hyp NSetFacts.mem_2.
    find_apply_lem_hyp NSetFacts.mem_2.
    have [m0 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H_in_nodes H0 H_eq_d Heqb.
    have [m1 H_bal_n] := Aggregation_in_set_exists_find_balance H_step1 _ H_in_n_nd H1 H_d' Heqb0.
    rewrite /sum_fold H_bal H_bal_n.    
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    gsimpl.
    have H_eq := Aggregation_sent_received_eq H_step1 H_in_nodes H0 H_in_n_nd H1 H_eq_d H_d' Heqb Heqb0 H_bal_n H_bal.
    aac_rewrite <- H_eq.
    have H_agg: @sum_aggregate_msg AggregationMsg_Aggregation (odnwPackets net0 h n) * (@sum_aggregate_msg AggregationMsg_Aggregation (odnwPackets net0 h n))^-1 = 1 by gsimpl.
    aac_rewrite H_agg.
    move {H_agg}.
    gsimpl.
    set s1 := sum_fail_map_incoming _ _ _ _ _.
    set s5 := sum_aggregate_msg_incoming_active _ _ _.
    set s6 := sum_aggregate_msg_incoming _ _ _.
    set s8 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s10 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s11 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s12 := sum_aggregate_msg_incoming_active _ _ _.
    set s13 := sum_aggregate_msg_incoming_active _ _ _.
    by aac_reflexivity.
  * find_apply_lem_hyp NSetFacts.mem_2.
    have H_ins: ~ NSet.In h d'.(adjacent).
      move => H_ins.
      find_apply_lem_hyp NSetFacts.mem_1.
      by congruence.
    have [m0 H_bal] := Aggregation_in_set_exists_find_balance H_step1 _ H_in_nodes H0 H_eq_d Heqb.
    rewrite /sum_fold H_bal.
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    gsimpl.
    have H_eq := sent_received_one_not_in H_step1 H_in_nodes H0 H_in_n_nd H1 H_eq_d H_d' Heqb H_ins H_bal.
    rewrite H_eq.
    gsimpl.
    have H_eq' := not_adjacent_sum_aggregate_msg_1 H_step1 _ H_in_n_nd H1 H_in_nodes H0 H_d' H_ins.
    rewrite H_eq'.
    gsimpl.
    set s1 := sum_fail_map_incoming _ _ _ _ _.
    set s5 := sum_aggregate_msg_incoming_active _ _ _.
    set s6 := sum_aggregate_msg_incoming _ _ _.
    set s8 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s10 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s11 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s12 := sum_aggregate_msg_incoming_active _ _ _.
    set s13 := sum_aggregate_msg_incoming_active _ _ _.
    by aac_reflexivity.
  * find_apply_lem_hyp NSetFacts.mem_2.
    have H_ins: ~ NSet.In n d.(adjacent).
      move => H_ins.
      find_apply_lem_hyp NSetFacts.mem_1.
      by congruence.
    have [m1 H_bal_n] := Aggregation_in_set_exists_find_balance H_step1 _ H_in_n_nd H1 H_d' Heqb0.
    rewrite /sum_fold H_bal_n.
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    gsimpl.
    have H_eq := sent_received_one_not_in H_step1 H_in_n_nd H1 H_in_nodes H0 H_d' H_eq_d Heqb0 H_ins H_bal_n.
    rewrite H_eq.
    gsimpl.
    have H_eq' := not_adjacent_sum_aggregate_msg_1 H_step1 _ H_in_nodes H0 H_in_n_nd H1 H_eq_d H_ins.
    rewrite H_eq'.
    gsimpl.
    set s1 := sum_fail_map_incoming _ _ _ _ _.
    set s5 := sum_aggregate_msg_incoming_active _ _ _.
    set s6 := sum_aggregate_msg_incoming _ _ _.
    set s8 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s10 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s11 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s12 := sum_aggregate_msg_incoming_active _ _ _.
    set s13 := sum_aggregate_msg_incoming_active _ _ _.
    by aac_reflexivity.
  * have H_ins: ~ NSet.In h d'.(adjacent).
      move => H_ins.
      find_apply_lem_hyp NSetFacts.mem_1.
      by congruence.
    have H_ins': ~ NSet.In n d.(adjacent).
      move => H_ins'.
      find_apply_lem_hyp NSetFacts.mem_1.
      by congruence.
    aac_rewrite IH.
    move {IH}.
    have H_eq := not_adjacent_sum_aggregate_msg_1 H_step1 _ H_in_n_nd H1 H_in_nodes H0 H_d' H_ins.
    rewrite H_eq.
    have H_eq' := not_adjacent_sum_aggregate_msg_1 H_step1 _ H_in_nodes H0 H_in_n_nd H1 H_eq_d H_ins'.
    rewrite H_eq'.
    gsimpl.
    set s1 := sum_fail_map_incoming _ _ _ _ _.
    set s5 := sum_aggregate_msg_incoming_active _ _ _.
    set s6 := sum_aggregate_msg_incoming _ _ _.
    set s8 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s10 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s11 := sum_fail_balance_incoming_active_opt _ _ _ _.
    set s12 := sum_aggregate_msg_incoming_active _ _ _.
    set s13 := sum_aggregate_msg_incoming_active _ _ _.
    by aac_reflexivity.
Qed.

End Aggregation.
