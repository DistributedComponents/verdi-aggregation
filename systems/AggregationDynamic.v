Require Import Verdi.
Require Import HandlerMonad.
Require Import NameOverlay.

Require Import TotalMapSimulations.
Require Import PartialMapSimulations.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

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

Require Import OrderedLemmas.
Require Import AggregationDefinitions.
Require Import AggregatorDynamic.
Require Import FailureRecorderDynamic.

Set Implicit Arguments.

Module Aggregation (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import CFG : CommutativeFinGroup) (Import ANT : AdjacentNameType NT).

Module OA := SingleAggregator NT NOT NSet NOTC NMap CFG ANT.

(* FIXME *)
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
  sent : NM ; 
  received : NM 
}.

Definition InitData (n : name) := 
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := NSet.empty ;
     sent := NMap.empty m ;
     received := NMap.empty m |}.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match NMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := NMap.add src (m_src * m_msg) st.(received) |}                                                           
  end
| Fail => 
  match NMap.find src st.(sent), NMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>    
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 ;
           adjacent := NSet.remove src st.(adjacent) ;
           sent := NMap.remove src st.(sent) ;
           received := NMap.remove src st.(received) |}           
  | _, _ => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := NSet.remove src st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) |}
  end
| New =>
  put {| local := st.(local) ;
         aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
         sent := NMap.add src 1 st.(sent) ;
         received := NMap.add src 1 st.(received)      
      |}
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg ;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1 ;
         adjacent := st.(adjacent) ;
         sent := st.(sent) ;
         received := st.(received) |}
| AggregateRequest =>
  write_output (AggregateResponse st.(aggregate))
| SendAggregate dst => 
  when (NSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match NMap.find dst st.(sent) with
   | None => nop
   | Some m_dst =>        
     put {| local := st.(local) ;
            aggregate := 1 ;
            adjacent := st.(adjacent) ;
            sent := NMap.add dst (m_dst * st.(aggregate)) st.(sent) ;
            received := st.(received) |} ;; 
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
         st'.(sent) = st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = []) \/
      (exists dst m', i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(sent) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = NMap.add dst (m' * st.(aggregate)) st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(sent) = None /\
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
    (exists m_msg m_src, msg = Aggregate m_msg /\ NMap.find src st.(received) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\     
     st'.(received) = NMap.add src (m_src * m_msg) st.(received) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ NMap.find src st.(received) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_snt m_rcd, msg = Fail /\ NMap.find src st.(sent) = Some m_snt /\ NMap.find src st.(received) = Some m_rcd /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(sent) = NMap.remove src st.(sent) /\
     st'.(received) = NMap.remove src st.(received) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (NMap.find src st.(sent) = None \/ NMap.find src st.(received) = None) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     out = [] /\ ms = []) \/
    (msg = New /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(sent) = NMap.add src 1 st.(sent) /\
     st'.(received) = NMap.add src 1 st.(received) /\
     out = [] /\ ms =[]).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg||]; monad_unfold.
  case H_find: (NMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=; first by left; exists m_msg; exists  m_src.
  by right; left; exists m_msg.
- case H_find: (NMap.find _ _) => [m_snt|]; case H_find': (NMap.find _ _) => [m_rcd|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
  * right; right; left.
    by exists m_snt; exists m_rcd.
  * right; right; right; left.
    split => //.
    split => //.
    by right.
  * right; right; right; left.
    split => //.
    split => //.
    by left.
  * right; right; right; left.
    split => //.
    split => //.
    by left.
- right; right; right; right.
  by find_inversion.
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
    @step_o_d_f_star _ _ _ Aggregation_NewMsgParams Aggregation_FailMsgParams step_o_d_f_init (failed, net) tr ->
    @step_o_d_f_star _ _ _ FR.FailureRecorder_NewMsgParams FR.FailureRecorder_FailMsgParams step_o_d_f_init (failed, pt_map_odnet net) (pt_map_traces tr).
Proof.
move => onet failed tr H_st.
apply step_o_d_f_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), In_all_before New Fail (net.(odnwPackets) n' n).
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
    step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
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
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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

Lemma Aggregation_self_channel_empty : 
forall onet failed tr, 
 step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
 forall n, onet.(odnwPackets) n n = [].
Proof.
move => net failed tr H.
change net with (snd (failed, net)).
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n.
  case (name_eq_dec h n) => H_dec; last first.
    rewrite collate_ls_neq_to //.
    by rewrite collate_neq.
  find_reverse_rewrite.
  rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
  rewrite collate_map_pair_notin; last exact: not_in_exclude.
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
  rewrite collate_map_pair_not_related //.
  exact: adjacent_to_irreflexive.
Qed.

Lemma Aggregation_inactive_no_incoming :
forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
  forall n, ~ In n (odnwNodes onet) ->
  forall n', onet.(odnwPackets) n' n = [].
Proof.
move => net failed tr H.
change net with (snd (failed, net)).
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- move => n H_in n'.
  have H_neq: h <> n by auto.
  have H_not_in: ~ In n net0.(odnwNodes) by auto.
  rewrite collate_ls_neq_to //.
  case (name_eq_dec h n') => H_dec.
    rewrite -H_dec.
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
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
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
    by auto.
  rewrite collate_neq //.
  by auto.
Qed.

Lemma Aggregation_in_set_exists_find_sent : 
forall net failed tr, 
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall d, net.(odnwState) n = Some d ->
 forall n', NSet.In n' d.(adjacent) -> 
       exists m5 : m, NMap.find n' d.(sent) = Some m5.
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in H_f d.
  rewrite /update_opt.
  break_if => H_eq.
    find_injection.
    unfold InitData in *.
    by find_apply_lem_hyp NSetFacts.empty_1.
  break_or_hyp => //.
  by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update_opt in *; break_if; try by eauto.
  * find_injection.    
    repeat find_rewrite.
    by eauto.
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
    break_exists.
    exists x1.
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
  io_handler_cases => //=; unfold update_opt in *; break_if; try by eauto.
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

Lemma Aggregation_in_set_exists_find_received : 
forall net failed tr, 
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall d, net.(odnwState) n = Some d ->
 forall n', NSet.In n' d.(adjacent) -> 
       exists m5 : m, NMap.find n' d.(received) = Some m5.
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_in H_f d.
  rewrite /update_opt.
  break_if => H_eq.
    find_injection.
    unfold InitData in *.
    by find_apply_lem_hyp NSetFacts.empty_1.
  break_or_hyp => //.
  by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update_opt in *; break_if; try by eauto.
  * find_injection.
    repeat find_rewrite.
    case (name_eq_dec n' from) => H_dec.
      exists (x0 * x).
      rewrite H_dec.
      exact: NMapFacts.add_eq_o.
    rewrite NMapFacts.add_neq_o; last by auto.
    by eauto.
  * find_injection.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    have H_neq: n' <> from.
      move => H_eq.
      find_rewrite.
      by find_apply_lem_hyp NSetFacts.remove_1.
    find_apply_lem_hyp NSetFacts.remove_3.
    have IH := IHrefl_trans_1n_trace1 _ H6 H7 _ H4 _ H9.
    break_exists.
    exists x1.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq.
    by apply NMapFacts.find_mapsto_iff.
  * find_injection.
    repeat find_rewrite.
    find_apply_lem_hyp NSetFacts.remove_3.
    by eauto.
  * find_injection.
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
  io_handler_cases => //=; unfold update_opt in *; break_if; try by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
  * find_injection.
    repeat find_rewrite.
    by eauto.
- by eauto.
Qed.

Lemma Aggregation_in_after_all_fail_aggregate : 
forall net failed tr,
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall n', In n' net.(odnwNodes) ->
 forall m', In_all_before (Aggregate m') Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
    by rewrite (Aggregation_self_channel_empty H).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map_pair_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
    rewrite collate_map_pair_live_related //.
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
    rewrite collate_ls_in_excluded //.
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
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H16 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H16 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H15 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  rewrite /update2.
  break_if; break_and; subst_max; last by eauto.
  apply: append_before_all_not_in.
  exact: (Aggregation_not_failed_no_fail H).
- move => n H_n H_f n' H_n' m'.
  have H_neq: h <> n by auto.
  have H_f': ~ In n failed by auto.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    by eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map_pair_not_related //.
    by eauto.
  rewrite collate_map_pair_live_related //.
    apply: append_neq_before_all => //.
    by eauto.
  exact: @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
Qed.

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
  forall net failed tr, 
    step_o_d_f_star step_o_d_f_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) ->
    forall m5, In (Aggregate m5) (net.(odnwPackets) n' n) ->
    forall d, net.(odnwState) n = Some d ->
     In New (net.(odnwPackets) n' n) \/ NSet.In n' d.(adjacent).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4 5 6.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m' H_in d H_eq.
  unfold update_opt in *.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
  break_if.
    find_injection.
    move {H_n}.
    contradict H_in.
    break_or_hyp.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
      rewrite collate_map_pair_notin; last exact: not_in_exclude.
      by rewrite (Aggregation_self_channel_empty H).
    have H_neq: h <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec h n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Aggregation_inactive_no_incoming H).
    case (in_dec name_eq_dec n' failed) => H_dec'.
      rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: in_not_in_exclude.
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
    rewrite collate_map_pair_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
  rewrite collate_map_pair_live_related //.
  rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H) //=.
  by auto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update2, update_opt in *; simpl in *; repeat break_if; break_and; subst_max; try find_injection; try by eauto.
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
  * contradict H17.
    have H_bef := Aggregation_in_after_all_fail_aggregate H _ H6 H2 _ H16 m5.
    find_rewrite.
    simpl in *.
    break_or_hyp => //.
    by break_and.
  * find_rewrite.
    break_or_hyp => //.
    have IH := IHrefl_trans_1n_trace1 _ H6 H15 _ H16 _ H17 _ H4.
    break_or_hyp; first by left.
    right.
    exact: NSetFacts.remove_2.
  * contradict H17.
    have H_bef := Aggregation_in_after_all_fail_aggregate H _ H6 H2 _ H16 m5.
    find_rewrite.
    simpl in *.
    break_or_hyp => //.
    by break_and.
  * break_or_hyp => //.
    have IH := IHrefl_trans_1n_trace1 _ H6 H15 _ H16 _ H17 _ H4.
    break_or_hyp; first by left.
    right.
    find_rewrite.
    exact: NSetFacts.remove_2.
  * find_rewrite.
    right.
    exact: NSetFacts.add_1.
  * break_or_hyp => //.
    find_rewrite.
    have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 _ H16 _ H4.
    break_or_hyp; first by left.
    right.
    exact: NSetFacts.add_2.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; unfold update_opt in *; simpl in *; break_if; break_and; subst_max; try find_injection; try by eauto.
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
    rewrite collate_map_pair_not_related //.
    by eauto.
  move: H_in.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
  rewrite collate_map_pair_live_related //.
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
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, In n net.(odnwNodes) -> ~ In n failed ->
 forall n', In n' net.(odnwNodes) ->
 forall m', In_all_before New (Aggregate m') (net.(odnwPackets) n' n).
Proof.
move => net failed tr H.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4.
remember step_o_d_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_d_f _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' m'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
    rewrite collate_map_pair_notin; last exact: not_in_exclude.
    by rewrite (Aggregation_self_channel_empty H).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; apply: not_in_exclude.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map_pair_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ H).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
    rewrite collate_map_pair_live_related //.
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
    rewrite collate_ls_in_excluded //.
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
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H8 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H16 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H16 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H3 H2 _ H15 m'.
    find_rewrite.
    case: IH => IH; first exact: not_in_all_before.
    by break_and.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  rewrite /update2.
  break_if; break_and; subst_max; last by eauto.  
  apply: append_neq_before_all => //.
  by eauto.
- move => n H_n H_f n' H_n' m'.
  have H_neq: h <> n by auto.
  have H_f': ~ In n failed by auto.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    by eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec; last first.
    rewrite collate_map_pair_not_related //.
    by eauto.
  rewrite collate_map_pair_live_related //.
    apply: append_neq_before_all => //.
    by eauto.
  exact: @ordered_dynamic_nodes_no_dup _ _ _ _ Aggregation_FailMsgParams _ _ _ H.
Qed.

Lemma Aggregation_aggregate_head_in_adjacent :
  forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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

Instance Aggregation_Aggregator_multi_single_map : MultiSingleNodeParamsTotalMap Aggregation_MultiParams OA.Aggregator_BaseParams := 
  {
    tot_s_map_data := fun d => OA.mkData d.(local) d.(aggregate) d.(adjacent) d.(sent) d.(received) ;
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

Instance Aggregation_Aggregator_congr (n : name) : MultiParamsSingleTotalMapCongruency OA.Aggregator_SingleNodeParams Aggregation_Aggregator_multi_single_map n :=
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

Lemma Aggregation_step_o_d_f_tot_one_mapped_simulation_star_1 :
  forall n net failed tr,
    step_o_d_f_star step_o_d_f_init (failed, net) tr ->
    forall d, net.(odnwState) n = Some d ->
    exists tr', @step_s_star _ OA.Aggregator_SingleNodeParams (@init_handler _ OA.Aggregator_SingleNodeParams) (tot_s_map_data d) tr'.
Proof.
move => n.
apply: Aggregation_step_o_d_f_tot_one_mapped_simulation_star_1.
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
  have H_hd: head (odnwPackets net x1 n) = Some Fail by find_rewrite.
  apply: (Aggregation_head_fail_then_adjacent H_star _ _ _ _ H_hd) => //.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec' //.
  have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
  by congruence.      
* case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  have [m' H_m] := Aggregation_in_set_exists_find_sent H_star _ H_dec' H_in_f H_eq' H.
  by congruence.
* case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  have [m' H_m] := Aggregation_in_set_exists_find_sent H_star _ H_dec' H_in_f H_eq' H.
  by congruence.
* case: H.
  have H_hd: head (odnwPackets net x n) = Some Fail by find_rewrite.
  apply: (Aggregation_head_fail_then_adjacent H_star _ _ _ _ H_hd) => //=.
  case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec' //.
  have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
  by congruence.
* case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  have [m' H_m] := Aggregation_in_set_exists_find_received H_star _ H_dec' H_in_f H_eq' H.
  by congruence.
* case (in_dec name_eq_dec n net.(odnwNodes)) => H_dec'; last first.
    have H_st := (@ordered_dynamic_uninitialized_state _ _ _ _ Aggregation_FailMsgParams _ _ _ H_star) _ H_dec'.
    by congruence.
  have [m' H_m] := Aggregation_in_set_exists_find_received H_star _ H_dec' H_in_f H_eq' H.
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
    aggr_sent := sent ;
    aggr_received := received
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
 step_o_d_f_star step_o_d_f_init (failed, net) tr ->
 forall n, ~ In n failed -> 
 forall d, net.(odnwState) n = Some d ->
      conserves_node_mass d.
Proof.
move => onet failed tr H n H_f d H_eq.
have H_st := Aggregation_step_o_d_f_tot_one_mapped_simulation_star_1 _ H H_eq.
move: H_st => [tr' H_st].
apply OA.Aggregator_conserves_node_mass in H_st.
by rewrite /= /conserves_node_mass /= in H_st.
Qed.

Lemma Aggregation_non_failed_or_incoming_fail : 
  forall net failed tr, 
    step_o_d_f_star step_o_d_f_init (failed, net) tr ->
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

Hypothesis H_step : step_o_d_f_star step_o_d_f_init (failed, onet) tr.

Variable n n' : name.

Hypothesis active : In n (odnwNodes onet).

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis after_init_new :
  forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  ~ In n onet.(odnwNodes) ->
  In n' onet.(odnwNodes) ->
  ~ In n' failed ->
  adjacent_to n' n ->  
  P (InitData n) [New].

Hypothesis after_adjacent :
  forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  ~ In n' onet.(odnwNodes) ->  
  adjacent_to n' n ->  
  forall d, onet.(odnwState) n = Some d ->
  P d [] ->
  P d [New].

Hypothesis recv_fail_from_eq :
  forall onet failed tr ms m0 m1,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  In n' failed ->
  n' <> n ->
  adjacent_to n' n ->
  onet.(odnwPackets) n' n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  NMap.find n' d.(sent) = Some m0 ->
  NMap.find n' d.(received) = Some m1 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m0 * m1^-1 ;
       adjacent := NSet.remove n' d.(adjacent) ;
       sent := NMap.remove n' d.(sent) ;
       received := NMap.remove n' d.(received)     
    |} ms.

Hypothesis recv_fail_from_neq :
  forall onet failed tr from ms m0 m1,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  In from failed ->
  from <> n ->
  from <> n' ->
  adjacent_to from n ->
  onet.(odnwPackets) from n = Fail :: ms ->
  forall d, onet.(odnwState) n = Some d ->
  NMap.find from d.(sent) = Some m0 ->
  NMap.find from d.(received) = Some m1 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m0 * m1^-1 ;
       adjacent := NSet.remove from d.(adjacent) ;
       sent := NMap.remove from d.(sent) ;
       received := NMap.remove from d.(received)
    |} (onet.(odnwPackets) n' n).

Hypothesis recv_new_from_eq :
  forall onet failed tr ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
       sent := NMap.add n' 1 d.(sent) ;
       received := NMap.add n' 1 d.(received)
    |} ms.

Hypothesis recv_new_from_neq :
  forall onet failed tr from ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
       sent := NMap.add from 1 d.(sent) ;
       received := NMap.add from 1 d.(received)
     |} (onet.(odnwPackets) n' n).

Hypothesis recv_aggregate_eq : 
  forall onet failed tr m' m0 ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In n' onet.(odnwNodes) ->
  n <> n' ->
  adjacent_to n' n ->
  onet.(odnwPackets) n' n = Aggregate m' :: ms ->
  forall d, onet.(odnwState) n = Some d -> 
  NMap.find n' d.(received) = Some m0 ->
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m' ;
       adjacent := d.(adjacent) ;
       sent := d.(sent) ;
       received := NMap.add n' (m0 * m') d.(received)
    |} ms.

Hypothesis recv_aggregate_other : 
  forall onet failed tr m' from m0 ms,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
  In n onet.(odnwNodes) ->
  ~ In n failed ->
  In from onet.(odnwNodes) ->
  from <> n ->
  from <> n' ->
  adjacent_to from n ->
  onet.(odnwPackets) from n = Aggregate m' :: ms ->
  forall d, onet.(odnwState) n = Some d -> 
  NMap.find from d.(received) = Some m0 ->  
  P d (onet.(odnwPackets) n' n) ->
  P {| local := d.(local) ;
       aggregate := d.(aggregate) * m' ;
       adjacent := d.(adjacent) ;
       sent := d.(sent) ;
       received := NMap.add from (m0 * m') d.(received)
    |} (onet.(odnwPackets) n' n).

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    forall d, onet.(odnwState) n = Some d -> 
    P d (onet.(odnwPackets) n' n) ->
    P {| local := m_local ;
         aggregate := d.(aggregate) * m_local * d.(local)^-1 ;
         adjacent := d.(adjacent) ;
         sent := d.(sent) ;
         received := d.(received)
      |} (onet.(odnwPackets) n' n).

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

Hypothesis recv_send_aggregate : 
  forall onet failed tr m',
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    In n' onet.(odnwNodes) ->
    n <> n' ->
    adjacent_to n' n ->
    forall d, onet.(odnwState) n = Some d ->
    NSet.In n' d.(adjacent) ->
    d.(aggregate) <> 1 ->
    NMap.find n' d.(sent) = Some m' ->
    P d (onet.(odnwPackets) n' n) ->
    P {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         sent := NMap.add n' (m' * d.(aggregate)) d.(sent) ;
         received := d.(received) 
      |} (onet.(odnwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet failed tr to m',
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    In n onet.(odnwNodes) ->
    ~ In n failed ->
    to <> n ->
    to <> n' ->
    In to onet.(odnwNodes) ->
    adjacent_to to n ->
    forall d, onet.(odnwState) n = Some d ->
    NSet.In to d.(adjacent) ->
    d.(aggregate) <> 1 ->
    NMap.find to d.(sent) = Some m' ->
    P d (onet.(odnwPackets) n' n) ->
    P {| local := d.(local) ;
         aggregate := 1 ;
         adjacent := d.(adjacent) ;
         sent := NMap.add to (m' * d.(aggregate)) d.(sent) ;
         received := d.(received) 
        |} (onet.(odnwPackets) n' n).

Hypothesis recv_send_aggregate_sender :
  forall onet failed tr,
  step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
      by rewrite (Aggregation_self_channel_empty s1).
    case (In_dec name_eq_dec n' (odnwNodes net)) => H_a'; last first.
      rewrite collate_ls_not_in_related; last exact: not_in_exclude.
      rewrite collate_neq //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1).
    case (In_dec name_eq_dec n' failed0) => H_f'.
      rewrite collate_ls_in_excluded //.
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
  case (adjacent_to_dec h n) => H_adj; last by rewrite collate_map_pair_not_related //; rewrite H_dec'; exact: IHs1.
  rewrite collate_map_pair_live_related //; last exact: (ordered_dynamic_nodes_no_dup s1).
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
    rewrite /update_opt.
    break_if => H_eq.
      find_injection.
      destruct d0.
      simpl in *.
      rewrite H7 H8 H9 H10 H11.
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
      have [m' H_rcd] := Aggregation_in_set_exists_find_received s1 _ H1 H0 H2 H6.
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
    unfold update2, update_opt in *.
    destruct d0.
    have H_hd: head (odnwPackets net from to) = Some Fail by repeat find_rewrite.
    repeat break_if; break_and; try find_injection; simpl in *; subst_max; try by eauto.
      apply (recv_fail_from_eq s1) => //; last by eauto.
      have H_adj := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
      exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_adj).
    break_or_hyp => //.
    apply: (@recv_fail_from_neq _ _ _ _ ms _ _ s1) => //; last by eauto.
    have H_adj := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    exact: (Aggreation_in_adj_adjacent_to s1 _ H1 H0 H2 H_adj).
  * have H_hd: head (odnwPackets net from to) = Some Fail by find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    have [m' H_rcd] := Aggregation_in_set_exists_find_sent s1 _ H1 H0 H2 H_ins.
    by congruence.
  * have H_hd: head (odnwPackets net from to) = Some Fail by find_rewrite.
    have H_ins := Aggregation_head_fail_then_adjacent s1 _ H1 H0 _ H_hd H2.
    have [m' H_rcd] := Aggregation_in_set_exists_find_received s1 _ H1 H0 H2 H_ins.
    by congruence.
  * have H_neq: from <> to.
      move => H_eq.
      find_rewrite.
      by rewrite (Aggregation_self_channel_empty s1) in H3.
    case (in_dec name_eq_dec from net.(odnwNodes)) => H_dec; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Aggregation_FailMsgParams _ _ _ s1) in H3.
    unfold update2, update_opt in *.
    destruct d0.
    have H_in: In New (odnwPackets net from to) by repeat find_rewrite; left.
    have H_adj := Aggregation_in_new_then_adjacent s1 _ H1 H0 _ H_in.
    repeat break_if; break_and; try find_injection; simpl in *; subst_max; try by eauto.    
    break_or_hyp => //.
    by eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * unfold update_opt in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update2, update_opt in *.
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
  * have [m' H_rcd] := Aggregation_in_set_exists_find_sent s1 _ H1 H0 H2 H.
    by congruence.
  * unfold update_opt in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update_opt in *.
    destruct d0.
    by break_if; break_and; try find_injection; simpl in *; subst_max; eauto.
  * unfold update_opt in *.
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
    rewrite collate_map_pair_not_related //.
    by auto.
  rewrite collate_map_pair_live_related //.
  by eauto.
Qed.

End SingleNodeInvIn.

Lemma Aggregation_not_adjacent_no_incoming : 
  forall onet failed tr,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr -> 
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

Hypothesis H_step : step_o_d_f_star step_o_d_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis active_n : In n (odnwNodes onet).

Hypothesis active_n' : In n' (odnwNodes onet).

Hypothesis not_failed_n : ~ In n failed.

Hypothesis not_failed_n' : ~ In n' failed.

Variable P : Data -> Data -> list msg -> list msg -> Prop.

Hypothesis after_init : 
  forall onet failed tr,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    n' = n ->
    ~ In n (odnwNodes onet) -> 
    ~ In n failed ->
    P (InitData n) (InitData n) [] [].

Hypothesis after_init_fst_not_adjacent :
   forall onet failed tr,
     step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
     step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
     step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
     step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
     In n (odnwNodes onet) -> 
    ~ In n failed ->
    ~ In n' (odnwNodes onet) ->
    ~ In n' failed ->
    n' <> n ->
    adjacent_to n n' ->
    forall d, onet.(odnwState) n = Some d ->
    P d (InitData n') [New] [New].

Hypothesis recv_fail_self :
  forall onet failed tr from ms m0 m1,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
    In n (odnwNodes onet) -> 
    ~ In n failed ->
    n' = n ->
    In from onet.(odnwNodes) ->
    In from failed ->
    from <> n ->    
    adjacent_to from n ->
    onet.(odnwPackets) from n = Fail :: ms ->
    forall d, onet.(odnwState) n = Some d ->
    NMap.find from d.(sent) = Some m0 ->
    NMap.find from d.(received) = Some m1 ->
    P d d (onet.(odnwPackets) n n) (onet.(odnwPackets) n n) ->
    P {| local := d.(local) ;
         aggregate := d.(aggregate) * m0 * m1^-1 ;
         adjacent := NSet.remove from d.(adjacent) ;
         sent := NMap.remove from d.(sent) ;
         received := NMap.remove from d.(received)
      |} 
      {| local := d.(local) ;
         aggregate := d.(aggregate) * m0 * m1^-1 ;
         adjacent := NSet.remove from d.(adjacent) ;
         sent := NMap.remove from d.(sent) ;
         received := NMap.remove from d.(received)
      |} 
      [] [].

Hypothesis recv_fail_other_fst :
  forall onet failed tr from ms m0 m1,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
    NMap.find from d0.(sent) = Some m0 ->
    NMap.find from d0.(received) = Some m1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P {| local := d0.(local) ;
         aggregate := d0.(aggregate) * m0 * m1^-1 ;
         adjacent := NSet.remove from d0.(adjacent) ;
         sent := NMap.remove from d0.(sent) ;
         received := NMap.remove from d0.(received)
       |} d1
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_fail_other_snd :
  forall onet failed tr from ms m0 m1,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
    NMap.find from d1.(sent) = Some m0 ->
    NMap.find from d1.(received) = Some m1 ->
    P d0 d1 (odnwPackets onet n n') (odnwPackets onet n' n) ->
    P d0 
      {| local := d1.(local) ;
         aggregate := d1.(aggregate) * m0 * m1^-1 ;
         adjacent := NSet.remove from d1.(adjacent) ;
         sent := NMap.remove from d1.(sent) ;
         received := NMap.remove from d1.(received)
      |}
      (odnwPackets onet n n') (odnwPackets onet n' n).

Hypothesis recv_new_self :
  forall onet failed tr from ms,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
         sent := NMap.add from 1 d.(sent) ;
         received := NMap.add from 1 d.(received)
      |}
      {| local := d.(local) ;
         aggregate := d.(aggregate) ;
         adjacent := NSet.add from d.(adjacent) ;
         sent := NMap.add from 1 d.(sent) ;
         received := NMap.add from 1 d.(received)
      |}
      [] [].

Hypothesis recv_new_fst :
  forall onet failed tr ms,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
         sent := NMap.add n' 1 d0.(sent) ;
         received := NMap.add n' 1 d0.(received)
      |} 
      d1
      (odnwPackets onet n n') ms.

Hypothesis recv_new_snd :
  forall onet failed tr ms,
    step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
            sent := NMap.add n 1 d1.(sent) ;
            received := NMap.add n 1 d1.(received)
         |}
      ms (odnwPackets onet n' n).

(* BLAAAA *)

(*
Hypothesis recv_new_fst_other :
  forall onet failed tr from ms,
   step_o_d_f_star step_o_d_f_init (failed, onet) tr ->
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
        

        adjacent := NSet.add from (adjacent d0) 

     |} d1
     (odnwPackets onet n n') (odnwPackets onet n' n).
*)


End DualNodeInv.

Lemma Aggregation_send_aggregate_in : 
  forall net failed tr,
   step_o_d_f_star step_o_d_f_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
   forall m', In (Aggregate m') (net.(odnwPackets) n n') ->
   forall d, net.(odnwState) n = Some d ->
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st.
Admitted.

(*
Lemma not_in_aggregate_queue_ident : forall (V5 : V), ext_net_ok V5 ->
  forall (v5 v' : v), In v5 V5 -> In v' V5 ->
  ~ ISet.In (ext_ident v') (ext_adj v5) ->
  sum_aggregate_queue_ident (ext_mbox v') (ext_ident v5) = 1.
Proof.
*)

(* 
Lemma sent_received_one_not_in : forall (V5 : V), ext_net_ok V5 ->
  forall (v5 v' : v), In v5 V5 -> In v' V5 ->
  forall (m5 : m), ISet.In (ext_ident v') (ext_adj v5) ->
  ~ ISet.In (ext_ident v5) (ext_adj v') ->
  IMap.find (ext_ident v') (ext_map_sent v5) = Some m5 ->
  m5 * (sum_drop_queue_ident (ext_mbox v5) (ext_ident v'))^-1 = sum_aggregate_queue_ident (ext_mbox v') (ext_ident v5).
*)

(*
Lemma sent_received_other_not_in : forall (V5 : V), ext_net_ok V5 ->
  forall (v5 v' : v), In v5 V5 -> In v' V5 ->
  forall (m5 : m),
  ISet.In (ext_ident v') (ext_adj v5) ->
  ~ ISet.In (ext_ident v5) (ext_adj v') ->
  IMap.find (ext_ident v') (ext_map_received v5) = Some m5 ->
  (sum_drop_queue_ident (ext_mbox v') (ext_ident v5))^-1 = (sum_aggregate_queue_ident (ext_mbox v5) (ext_ident v')) * m5.
Proof.
*)

Lemma Aggregation_sent_received_eq : 
  forall net failed tr,
    step_o_d_f_star step_o_d_f_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->
    forall m0 m1,
    NSet.In n' d.(adjacent) ->
    NSet.In n d'.(adjacent) ->
    NMap.find n d'.(sent) = Some m0 ->
    NMap.find n' d.(received) = Some m1 ->
    m0 = sum_aggregate_msg (net.(odnwPackets) n' n) * m1.
Proof.
Admitted.

(*
Lemma sumM_sent_fail_active_eq_with_self : 
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed ->
   sumM (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) * 
     (sum_fail_map_incoming nodes onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent))^-1 =
   sumM_active (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (exclude failed nodes).
Proof.
*)

(*
Lemma sumM_received_fail_active_eq_with_self : 
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed ->
   sumM (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received) * 
     (sum_fail_map_incoming nodes onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received))^-1 =
   sumM_active (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received) (exclude failed nodes).
Proof.
*)

End Aggregation.
