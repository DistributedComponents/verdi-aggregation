Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.PartialExtendedMapSimulations.

Require Import NameAdjacency.
Require Import AggregationDefinitions.
Require Import AggregationAux.
Require Import AggregationStaticCorrect.
Require Import TreeAux.
Require Import TreeStaticCorrect.
Require Import TreeAggregationStatic.

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

Module TreeAggregationCorrect (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) (Import CFG : CommutativeFinGroup) 
 (Import ANT : AdjacentNameType NT) (Import A : Adjacency NT NOT NSet ANT)
 (Import TA : TAux NT NOT NSet NOTC NMap)
 (Import AD : ADefs NT NOT NSet NOTC NMap CFG).

Module AGC := AggregationCorrect NT NOT NSet NOTC NMap CFG ANT A AD.
Module AG := AGC.AG.

Module TRC := TreeCorrect NT NOT NSet NOTC NMap RNT ANT A TA.
Module TR := TRC.TR.

Module AX := AAux NT NOT NSet NOTC NMap CFG ANT AD.
Import AX.

Module TG := TreeAggregation NT NOT NSet NOTC NMap RNT CFG ANT A TA AD.
Import TG.

Import GroupScope.

Module ADCFGAACInstances := CFGAACInstances CFG.
Import ADCFGAACInstances.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Instance TreeAggregation_Aggregation_name_tot_map : MultiParamsNameTotalMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance TreeAggregation_Aggregation_name_tot_map_bijective : MultiParamsNameTotalMapBijective TreeAggregation_Aggregation_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance TreeAggregation_Aggregation_params_pt_msg_map : MultiParamsMsgPartialMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    pt_map_msg := fun m => 
      match m with 
      | Aggregate m' => Some (AG.Aggregate m')
      | Fail => Some AG.Fail      
      | Level _ => None 
      end   
  }.


Instance TreeAggregation_Aggregation_params_pt_ext_map : MultiParamsPartialExtendedMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    pt_ext_map_data := fun d _ => 
      AG.mkData d.(local) d.(aggregate) d.(adjacent) d.(balance) ;
    pt_ext_map_input := fun i n d =>
      match i with 
      | Local m => Some (AG.Local m)
      | SendAggregate => 
        if root_dec n then None else
          match parent d.(adjacent) d.(levels) with
          | Some p => Some (AG.SendAggregate p)
          | None => None
          end
      | AggregateRequest client_id => Some (AG.AggregateRequest client_id)
      | _ => None
      end
  }.

Lemma pt_ext_map_name_msgs_level_adjacent_empty : 
  forall fs lvo,
  filterMap pt_map_name_msg (level_adjacent lvo fs) = [].
Proof.
move => fs lvo.
rewrite /level_adjacent NSet.fold_spec.
elim: NSet.elements => //=.
move => n ns IH.
rewrite {2}/level_fold /=.
rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) /=.
by rewrite filterMap_app /= -app_nil_end IH.
Qed.

Instance TreeAggregation_Aggregation_multi_params_pt_ext_map_congruency : MultiParamsPartialExtendedMapCongruency TreeAggregation_Aggregation_name_tot_map TreeAggregation_Aggregation_params_pt_msg_map TreeAggregation_Aggregation_params_pt_ext_map :=
  {
    pt_ext_init_handlers_eq := _ ;
    pt_ext_net_handlers_some := _ ;
    pt_ext_net_handlers_none := _ ;
    pt_ext_input_handlers_some := _ ;
    pt_ext_input_handlers_none := _ 
  }.
Proof.
- by move => n; rewrite /= /InitData /=; break_if.
- move => me src mg st mg' out st' ps H_eq H_eq'.
  rewrite /pt_ext_mapped_net_handlers.
  repeat break_let.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  rewrite /= /runGenHandler_ignore /= in Heqp.
  repeat break_let.
  repeat tuple_inversion.
  destruct u, u0.
  unfold id in *.
  destruct st'.
  by net_handler_cases; AG.net_handler_cases; simpl in *; congruence.
- move => me src mg st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct u.
  destruct st'.
  by net_handler_cases; simpl in *; congruence.
- move => me inp st inp' out st' ps H_eq H_eq'.
  rewrite /pt_ext_mapped_input_handlers.
  repeat break_let.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  rewrite /= /runGenHandler_ignore /= in Heqp.
  repeat break_let.
  repeat tuple_inversion.
  destruct u, u0.
  unfold id in *.
  have H_eq_inp: inp = SendAggregate \/ inp <> SendAggregate by destruct inp; (try by right); left.
  case: H_eq_inp => H_eq_inp.
    subst_max.
    rewrite /= in H_eq.
    move: H_eq.
    case H_p: (parent st.(adjacent) st.(levels)) => [dst|].
      have H_p' := H_p.
      rewrite /parent in H_p'.
      break_match_hyp => //.
      destruct s.
      simpl in *.
      find_injection.
      inversion m0.
      inversion H.
      destruct st'.
      io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; unfold id in *; try congruence.
      move: Heqb.
      by case root_dec.
    by io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; congruence.
  destruct st'.
  simpl in *.
  by io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; congruence.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct u.
  destruct st'.
  io_handler_cases; simpl in *; unfold is_left in *; repeat break_if; try break_match; try congruence.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
Qed.
  
Instance TreeAggregation_Aggregation_fail_msg_params_pt_ext_map_congruency : FailMsgParamsPartialMapCongruency TreeAggregation_FailMsgParams AG.Aggregation_FailMsgParams TreeAggregation_Aggregation_params_pt_msg_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance TreeAggregation_Aggregation_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency TreeAggregation_NameOverlayParams AG.Aggregation_NameOverlayParams TreeAggregation_Aggregation_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem TreeAggregation_Aggregation_pt_ext_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_failure_star _ _ TreeAggregation_NameOverlayParams TreeAggregation_FailMsgParams step_ordered_failure_init (failed, net) tr ->
    exists tr', @step_ordered_failure_star _ _ AG.Aggregation_NameOverlayParams AG.Aggregation_FailMsgParams step_ordered_failure_init (failed, pt_ext_map_onet net) tr'.
Proof.
move => onet failed tr H_st.
apply step_ordered_failure_pt_ext_mapped_simulation_star_1 in H_st.
move: H_st => [tr' H_st].
rewrite map_id in H_st.
by exists tr'.
Qed.

Instance TreeAggregation_Tree_base_params_pt_map : BaseParamsPartialMap TreeAggregation_BaseParams TR.Tree_BaseParams :=
  {
    pt_map_data := fun d => TR.mkData d.(adjacent) d.(broadcast) d.(levels) ;
    pt_map_input := fun i =>
                   match i with
                   | LevelRequest client_id => Some (TR.LevelRequest client_id)
                   | Broadcast => Some TR.Broadcast
                   | _ => None
                   end ;
    pt_map_output := fun o => 
                    match o with
                    | LevelResponse client_id olv => Some (TR.LevelResponse client_id olv)
                    | _ => None
                    end
  }.

Instance TreeAggregation_Tree_name_tot_map : MultiParamsNameTotalMap TreeAggregation_MultiParams TR.Tree_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance TreeAggregation_Tree_name_tot_map_bijective : MultiParamsNameTotalMapBijective TreeAggregation_Tree_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance TreeAggregation_Tree_multi_params_pt_map : MultiParamsMsgPartialMap TreeAggregation_MultiParams TR.Tree_MultiParams :=
  {
    pt_map_msg := fun m => match m with 
                        | Fail => Some TR.Fail 
                        | Level lvo => Some (TR.Level lvo)
                        | _ => None 
                        end ;
  }.

Instance TreeAggregation_Tree_multi_params_pt_map_congruency : MultiParamsPartialMapCongruency TreeAggregation_Tree_base_params_pt_map TreeAggregation_Tree_name_tot_map TreeAggregation_Tree_multi_params_pt_map :=
  {
    pt_init_handlers_eq := _ ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
- by move => n; rewrite /= /InitData /= /TR.InitData /= /id /=; break_if.
- move => me src mg st mg' H_eq.  
  rewrite /pt_mapped_net_handlers.
  repeat break_let.
  case H_n: net_handlers => [[out st'] ps].
  rewrite /= /runGenHandler_ignore /= in Heqp H_n.
  repeat break_let.
  repeat tuple_inversion.
  unfold id in *.
  destruct u, u0.
  destruct st'.
  by net_handler_cases; TR.net_handler_cases; simpl in *; congruence.
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
  unfold id in *.
  destruct u, u0, st, st'.
  io_handler_cases; TR.io_handler_cases; simpl in *; try congruence.
    set ptl := filterMap _ _.
    set ptl' := level_adjacent _ _.
    suff H_suff: ptl = ptl' by repeat find_rewrite.
    rewrite /ptl /ptl' /level_adjacent 2!NSet.fold_spec.
    elim: NSet.elements => //=.
    move => n ns IH.
    rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) filterMap_app /= /id /=.
    by rewrite (@fold_left_level_fold_eq TR.Tree_TreeMsg) /= IH.
  set ptl := filterMap _ _.
  set ptl' := level_adjacent _ _.
  suff H_suff: ptl = ptl' by repeat find_rewrite.
  rewrite /ptl /ptl' /level_adjacent 2!NSet.fold_spec.
  elim: NSet.elements => //=.
  move => n ns IH.
  rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) filterMap_app /= /id /=.
  by rewrite (@fold_left_level_fold_eq TR.Tree_TreeMsg) /= IH.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= in H_eq'.
  repeat break_let.  
  repeat tuple_inversion.
  destruct u, st'.
  by io_handler_cases; simpl in *; congruence.
Qed.

Instance TreeAggregation_Tree_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency TreeAggregation_FailMsgParams TR.Tree_FailMsgParams TreeAggregation_Tree_multi_params_pt_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance TreeAggregation_Tree_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency TreeAggregation_NameOverlayParams TR.Tree_NameOverlayParams TreeAggregation_Tree_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem TreeAggregation_Tree_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_failure_star _ _ TreeAggregation_NameOverlayParams TreeAggregation_FailMsgParams step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ TR.Tree_NameOverlayParams TR.Tree_FailMsgParams step_ordered_failure_init (failed, pt_map_onet net) (filterMap pt_map_trace_ev tr).
Proof.
move => onet failed tr H_st.
apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Instance AggregationData_Data : AggregationData Data :=
  {
    aggr_local := local ;
    aggr_aggregate := aggregate ;
    aggr_adjacent := adjacent ;
    aggr_balance := balance
  }.

Instance AggregationMsg_TreeAggregation : AggregationMsg :=
  {
    aggr_msg := msg ;
    aggr_msg_eq_dec := msg_eq_dec ;
    aggr_fail := Fail ;
    aggr_of := fun mg => match mg with | Aggregate m' => m' | _ => 1 end
  }.

Instance AggregationMsgMap_Aggregation_TreeAggregation : AggregationMsgMap AggregationMsg_TreeAggregation AGC.AggregationMsg_Aggregation :=
  {
    map_msgs := filterMap pt_map_msg ;    
  }.
Proof.
- elim => //=.
  case => [m'||olv] ms IH /=.
  * by rewrite /aggregate_sum_fold /= IH.
  * by rewrite /aggregate_sum_fold /= IH.
  * by rewrite /aggregate_sum_fold /= IH; gsimpl.
- elim => //=.
  case => [m'||olv] ms IH /=.
  * by split => H_in; case: H_in => H_in //; right; apply IH.
  * by split => H_in; left.
  * split => H_in; last by right; apply IH.
    case: H_in => H_in //.
    by apply IH.
Defined.

Lemma TreeAggregation_conserves_network_mass : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  conserves_network_mass (remove_all name_eq_dec failed nodes) nodes onet.(onwPackets) onet.(onwState).
Proof.
move => onet failed tr H_st.
have [tr' H_st'] := TreeAggregation_Aggregation_pt_ext_mapped_simulation_star_1 H_st.
have H_inv := AGC.Aggregation_conserves_network_mass H_st'.
rewrite /= /id /= /conserves_network_mass in H_inv.
rewrite /conserves_network_mass.
move: H_inv.
set state := fun n : name => _.
set packets := fun src dst : name => _.
rewrite (sum_local_aggr_local_eq _ (onwState onet)) //.
move => H_inv.
rewrite H_inv {H_inv}.
rewrite (sum_aggregate_aggr_aggregate_eq _ (onwState onet)) //.
rewrite sum_aggregate_msg_incoming_active_map_msgs_eq /map_msgs /= -/packets.
by rewrite (sum_fail_balance_incoming_active_map_msgs_eq _ state) /map_msgs /= -/packets //.
Qed.

End TreeAggregationCorrect.
