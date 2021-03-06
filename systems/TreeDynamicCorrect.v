Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.DynamicNetLemmas.

Require Import StructTact.Update.
Require Import StructTact.Update2.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.

Require Import TreeAux.
Require Import FailureRecorderDynamic.
Require Import FailureRecorderDynamicCorrect.
Require Import TreeDynamic.

Require Import Sumbool.
Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import FMapInterface.
Require Import Sorting.Permutation.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module TreeCorrect (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC)
 (Import RNT : RootNameType NT) (Import ANT : AdjacentNameType NT)
 (Import TA : TAux NT NOT NSet NOTC NMap).

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Module FRC := FailureRecorderCorrect NT NOT NSet ANT.
Module FR := FRC.FR.

Module TR := Tree NT NOT NSet NOTC NMap RNT ANT TA.
Import TR.

Instance Tree_FailureRecorder_base_params_pt_map : BaseParamsPartialMap Tree_BaseParams FR.FailureRecorder_BaseParams :=
  {
    pt_map_data := fun d => FR.mkData d.(adjacent) ;
    pt_map_input := fun _ => None ;
    pt_map_output := fun _ => None
  }.

Instance Tree_FailureRecorder_name_tot_map : MultiParamsNameTotalMap Tree_MultiParams FR.FailureRecorder_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance Tree_FailureRecorder_name_tot_map_bijective : MultiParamsNameTotalMapBijective Tree_FailureRecorder_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance Tree_FailureRecorder_multi_params_pt_map : MultiParamsMsgPartialMap Tree_MultiParams FR.FailureRecorder_MultiParams :=
  {
    pt_map_msg := fun m => 
                   match m with 
                   | Fail => Some FR.Fail 
                   | New => Some FR.New
                   | _ => None 
                   end ;
  }.

Instance Tree_FailureRecorder_multi_params_pt_map_congruency : MultiParamsPartialMapCongruency Tree_FailureRecorder_base_params_pt_map Tree_FailureRecorder_name_tot_map Tree_FailureRecorder_multi_params_pt_map :=
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
  io_handler_cases; simpl in *; try by congruence.
  rewrite /level_adjacent NSet.fold_spec /flip /=.
  elim: NSet.elements => //=.
  move => n l IH.
  rewrite /flip /= /level_fold.
  rewrite (@fold_left_level_fold_eq Tree_TreeMsg).
  by rewrite filterMap_app /= IH.
Qed.

Instance Tree_FailureRecorder_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency Tree_FailMsgParams FR.FailureRecorder_FailMsgParams Tree_FailureRecorder_multi_params_pt_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance Tree_FailureRecorder_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency Tree_NameOverlayParams FR.FailureRecorder_NameOverlayParams Tree_FailureRecorder_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Instance Tree_FailureRecorder_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency Tree_NewMsgParams FR.FailureRecorder_NewMsgParams Tree_FailureRecorder_multi_params_pt_map := 
  {
    pt_new_msg_fst_snd := Logic.eq_refl
  }.

Theorem Tree_Failed_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ _ Tree_NewMsgParams Tree_FailMsgParams step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ _ FR.FailureRecorder_NewMsgParams FR.FailureRecorder_FailMsgParams step_ordered_dynamic_failure_init (failed, pt_map_odnet net) (filterMap pt_map_trace_ev tr).
Proof.
move => onet failed tr H_st.
apply step_ordered_dynamic_failure_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Lemma Tree_node_not_adjacent_self_lift :
forall net failed n,
(In n (odnwNodes (pt_map_odnet net)) -> ~ In n failed -> 
forall d, odnwState (pt_map_odnet net) n = Some d -> ~ NSet.In n (FR.adjacent d)) ->
(In n (odnwNodes net) -> ~ In n failed -> 
 forall d, odnwState net n = Some d -> ~ NSet.In n d.(adjacent)).
Proof.
move => net failed n H_p H_in H_in' d H_eq.
rewrite /= /id /= map_id H_eq /= in H_p.
have H_p' := H_p H_in H_in' {| FR.adjacent := d.(adjacent) |}.
exact: H_p'.
Qed.

Lemma Tree_node_not_adjacent_self : 
forall net failed tr,
 step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
 forall n, In n (odnwNodes net) ->
 ~ In n failed ->
 forall d, odnwState net n = Some d ->
 ~ NSet.In n d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f d H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_node_not_adjacent_self _ _ _ H_st' n.
eapply Tree_node_not_adjacent_self_lift in H_inv'; eauto.
Qed.

Lemma Tree_not_failed_no_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n, In n (odnwNodes onet) -> ~ In n failed ->
  forall n', ~ In Fail (onet.(odnwPackets) n n').
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FRC.Failure_not_failed_no_fail H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move => H_in.
case: IH'.
move: H_in.
apply: in_msg_filterMap_pt_map_msg.
exact: pt_fail_msg_fst_snd.
Qed.

Lemma Tree_in_after_all_fail_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->
        forall (n' : name), before_all New Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FRC.Failure_in_after_all_fail_new H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
exact: in_all_before_pt_map_msg.
Qed.

Lemma Tree_pt_map_msg_injective : 
  forall m0 m1 m2 : msg,
   pt_map_msg m0 = Some m2 -> pt_map_msg m1 = Some m2 -> m0 = m1.
Proof.
by case => [|lvo'|]; case => [|lvo''|] => //=; case.
Qed.

Lemma Tree_le_one_new : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) New <= 1.
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FRC.Failure_le_one_new H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_filterMap_pt_map_msg_eq => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_le_one_fail : 
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) -> ~ In n failed ->
   forall (n' : name), count_occ Msg_eq_dec (net.(odnwPackets) n' n) Fail <= 1.
Proof.
move => net failed tr H_st n H_n H_f n'.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have IH := FRC.Failure_le_one_fail H_st'.
rewrite /= map_id /id /= in IH.
have IH' := IH _ H_n H_f n'.
move: IH'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_filterMap_pt_map_msg_eq => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_in_new_failed_incoming_fail : 
  forall onet failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
    forall n, In n (odnwNodes onet) -> ~ In n failed ->
         forall n', In n' failed ->
               In New (onet.(odnwPackets) n' n) ->
               In Fail (onet.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_f' H_in.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_in_new_failed_incoming_fail H_st'.
rewrite /= map_id /id /= in H_inv'.
have IH := H_inv' _ H_n H_f _ H_f'.
move: IH.
set in_pt := In FR.Fail _.
move => IH.
suff H_suff: in_pt.
  move: H_suff.
  apply: in_filterMap_pt_map_msg_in_msg => //.
  exact: Tree_pt_map_msg_injective.
apply: IH.
move: H_in.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
          forall d, onet.(odnwState) n = Some d ->
               NSet.In n' d.(adjacent) ->
               adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_n H_f d H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_in_adj_adjacent_to _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f {| FR.adjacent := d.(adjacent) |}.
exact: H_inv''.
Qed.

Lemma Tree_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> 
  forall n n', In n (odnwNodes onet) -> ~ In n failed ->
       forall d, onet.(odnwState) n = Some d ->
            NSet.In n' d.(adjacent) ->
            (In n' (odnwNodes onet) /\ ~ In n' failed) \/ (In n' (odnwNodes onet) /\ In n' failed /\ In Fail (onet.(odnwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_n H_f d H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_in_adj_or_incoming_fail  _ _ _ H_st' n n'.
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
apply: in_filterMap_pt_map_msg_in_msg => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_new_incoming_not_in_adj :
forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n (odnwNodes net) ->
        ~ In n failed ->        
        forall (n' : name), In New (net.(odnwPackets) n' n) ->
                       forall d, net.(odnwState) n = Some d ->
                            ~ NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f n' H_in d H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_new_incoming_not_in_adj _ _ _ H_st' n _ _ n' _ {| FR.adjacent := d.(adjacent) |}.
rewrite /= map_id /id /= H_eq in H_inv'.
apply: H_inv' => //.
move: H_in.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_adjacent_to_no_incoming_new_n_adjacent :
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
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_adjacent_to_no_incoming_new_n_adjacent _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f H_n' H_f' H_adj {| FR.adjacent := d.(adjacent) |}.
apply: H_inv'' => //.
move => H_in'.
case: H_in.
apply: in_filterMap_pt_map_msg_in_msg => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_incoming_fail_then_incoming_new_or_in_adjacent : 
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
      (In New (net.(odnwPackets) n' n) /\ ~ NSet.In n' d.(adjacent)) \/ (~ In New (net.(odnwPackets) n' n) /\ NSet.In n' d.(adjacent)).
Proof.
move => net failed tr H_st n H_n H_f n' H_in d H_eq. 
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_incoming_fail_then_incoming_new_or_in_adjacent _ _ _ H_st' n.
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
    apply: in_filterMap_pt_map_msg_in_msg => //.
    exact: Tree_pt_map_msg_injective.
  break_and.
  right.
  split => //.
  move => H_in'.
  case: H.
  move: H_in'.
  exact: in_msg_filterMap_pt_map_msg.
rewrite /f_in.
move: H_in.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_incoming_fail_then_new_or_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In Fail (net.(odnwPackets) n' n) ->
      forall d, net.(odnwState) n = Some d ->
       In New (net.(odnwPackets) n' n) \/ NSet.In n' (adjacent d).
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f n' H_in d H_eq.
have H_or := Tree_incoming_fail_then_incoming_new_or_in_adjacent H_st _ H_in_n H_in_f _ H_in H_eq.
break_or_hyp; break_and; first by left.
by right.
Qed.

Lemma Tree_head_fail_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', head (net.(odnwPackets) n' n) = Some Fail ->
   forall d, net.(odnwState) n = Some d -> 
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_st n H_n H_f n' H_eq d H_eq'.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_head_fail_then_adjacent _ _ _ H_st' n.
rewrite /= map_id /id /= H_eq' in H_inv'.
have H_inv'' := H_inv' H_n H_f n' _ {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _).
apply: H_inv''.
move: H_eq.
exact: hd_error_filterMap_pt_map_msg.
Qed.

Lemma Tree_adjacent_or_incoming_new_reciprocal :
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
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_adjacent_or_incoming_new_reciprocal _ _ _ H_st' n n'.
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
  apply: in_filterMap_pt_map_msg_in_msg => //.
  exact: Tree_pt_map_msg_injective.
suff H_suff: inn.
  have H_or: NSet.In n' (adjacent d) \/ inn by right.
  concludes.
  case: H_inv'' => H_inv''; first by left.
  right.
  move: H_inv''.
  apply: in_filterMap_pt_map_msg_in_msg => //.
  exact: Tree_pt_map_msg_injective.
move: H_in.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_adjacent_then_adjacent_or_new_incoming :
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
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_adjacent_then_adjacent_or_new_incoming _ _ _ H_st' n n'.
rewrite /= map_id /id /= H_eq H_eq' in H_inv'.
have H_inv'' := H_inv' H_n H_f H_n' H_f' {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _) {| FR.adjacent := d'.(adjacent) |} (Logic.eq_refl _).
rewrite /= in H_inv''.
concludes.
break_or_hyp; first by left.
right.
move: H.
apply: in_filterMap_pt_map_msg_in_msg => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_fail_head_no_new :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
        forall n', head (net.(odnwPackets) n' n) = Some Fail ->
        ~ In New (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_fail_head_no_new _ _ _ H_st' n.
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
  exact: in_msg_filterMap_pt_map_msg.
move: H_eq.
exact: hd_error_filterMap_pt_map_msg.
Qed.

Lemma Tree_failed_adjacent_fail :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In n' failed ->
      forall d0, odnwState net n = Some d0 ->
      (NSet.In n' d0.(adjacent) \/ In New (net.(odnwPackets) n' n)) ->
      In Fail (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_st n H_n H_f n' H_f' d H_eq H_or.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_failed_adjacent_fail _ _ _ H_st' n.
rewrite /= map_id /id /= H_eq in H_inv'.
have H_inv'' := H_inv' H_n H_f _ H_f' {| FR.adjacent := d.(adjacent) |} (Logic.eq_refl _).
rewrite /= in H_inv''.
move: H_inv''.
set inn := In FR.Fail _.
move => H_inv''.
suff H_suff: inn.
  move: H_suff.
  apply: in_filterMap_pt_map_msg_in_msg => //.
  exact: Tree_pt_map_msg_injective.
apply: H_inv''.
case: H_or => H_or; first by left.
right.
move: H_or.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_in_new_then_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
      forall n, In n net.(odnwNodes) -> ~ In n failed ->
      forall n', In New (odnwPackets net n' n) ->
            adjacent_to n' n.
Proof.
move => net failed tr H_st n H_n H_f n' H_in.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_in_new_then_adjacent _ _ _ H_st' n.
rewrite /= map_id /id /= in H_inv'.
apply: (H_inv' H_n H_f n').
move: H_in.
exact: in_msg_filterMap_pt_map_msg.
Qed.

Lemma Tree_inactive_not_in_adjacent :
forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed ->
  forall n', ~ In n' (odnwNodes net) ->
  forall d0, odnwState net n = Some d0 ->
  ~ NSet.In n' d0.(adjacent).
Proof.
move => net failed tr H_st n H_in H_f n' H_n' d0 H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := @FRC.Failure_inactive_not_in_adjacent _ _ _ H_st' n _ _ n' _ {| FR.adjacent := d0.(adjacent) |}.
rewrite /= map_id /id /= H_eq /= in H_inv'.
by repeat concludes.
Qed.

Lemma Tree_self_channel_empty : 
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
    break_if; first by break_and; subst; repeat find_higher_order_rewrite.      
    by break_if; first by break_and; subst; break_or_hyp.
  * rewrite /update2 /=.
    break_if; last by find_higher_order_rewrite.
    break_and; repeat find_rewrite.
    by find_higher_order_rewrite.
  * rewrite /update2 /=.
    break_if; first by break_and; subst; repeat find_higher_order_rewrite.      
    by break_if; first by break_and; subst; break_or_hyp.   
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  case (name_eq_dec h n) => H_dec; last by rewrite collate_neq.
  subst.
  have H_ins := Tree_node_not_adjacent_self H H3 H2 H4.
  rewrite /level_adjacent NSet.fold_spec /flip /=.
  have H_ins': ~ In n (NSet.elements d.(adjacent)).
    move => H_ins'.
    case: H_ins.
    by apply NSetFacts.elements_2; auto.
  elim: NSet.elements H_ins' => //=.
  move => n' ns IH H_in.
  have H_neq: n' <> n by auto.
  have H_in': ~ In n ns by auto.
  rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
  rewrite collate_app /=.
  rewrite /update2.
  break_if; first by break_and; subst.
  by rewrite IH.
- move => n.  
  case (name_eq_dec h n) => H_dec; last by rewrite collate_neq; first by find_higher_order_rewrite.
  find_reverse_rewrite.
  rewrite collate_map2snd_not_related //.
  exact: adjacent_to_irreflexive.
Qed.

Lemma Tree_inactive_no_incoming :
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
    break_if; first by break_and; subst; rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) in H5.
    break_if; first by break_and; subst; rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) in H5.
    by rewrite IHrefl_trans_1n_trace1.
  * rewrite /update2 /=.
    break_if; break_and; last by eauto.
    by repeat find_rewrite; eauto.
  * rewrite /update2 /=.
    break_if; first by break_and; subst; rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) in H5.
    break_if; first by break_and; subst; rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) in H5.
    by rewrite IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * by auto.
  * case (name_eq_dec h n') => H_dec; last by rewrite collate_neq // IHrefl_trans_1n_trace1.
    subst.
    have H_ins: ~ NSet.In n d.(adjacent).
      move => H_ins.
      have H_or := Tree_in_adj_or_incoming_fail H _ H3 H2 H4 H_ins.
      by break_or_hyp; break_and.
    rewrite /level_adjacent NSet.fold_spec /flip /=.
    have H_ins': ~ In n (NSet.elements d.(adjacent)).
      move => H_ins'.
      case: H_ins.
      by apply NSetFacts.elements_2; auto.
    elim: NSet.elements H_ins' => /=; first by move => H_in; rewrite IHrefl_trans_1n_trace1.          
    move => n0 ns IH H_in.
    have H_neq: n0 <> n by auto.
    have H_in': ~ In n ns by auto.
    rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
    rewrite collate_app /=.
    rewrite /update2.
    break_if; first by break_and; subst.
    by rewrite IH.
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

(* bfs_net_ok_root_levels_empty *)
Lemma Tree_root_levels_empty :
  forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed -> root n ->
  forall d, net.(odnwState) n = Some d ->
  d.(levels) = NMap.empty lv.
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
- move => n H_in_n H_in_f H_r d H_d.
  destruct_update; first by find_injection.
  break_or_hyp => //.
  by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * destruct_update; last by eauto.
    find_injection.
    find_rewrite.
    by eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
  * destruct_update; last by eauto.
    find_injection.
    by eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
  * destruct_update; last by eauto.
    find_injection.
    find_rewrite.
    by eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  * destruct_update; last by eauto.
    find_injection.
    by eauto.
  * by destruct_update; eauto.
  * by destruct_update; eauto.
  * destruct_update; last by eauto.
    find_injection.
    by eauto.
  * by destruct_update; eauto.
- move => n H_in_n H_in_f H_r d H_eq.
  have H_neq: h <> n by auto.
  have H_in: ~ In n failed by auto.
  by eauto.
Qed. 

(* bfs_net_ok_root_levels_bot *)
Lemma Tree_root_levels_bot : 
forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed -> root n ->
  forall d, net.(odnwState) n = Some d ->
  forall n', NMap.find n' d.(levels) = None.
Proof.
move => net failed tr H_st.
move => n H_in_n H_in_f H_r d H_d n'.
have H_emp := Tree_root_levels_empty H_st H_in_n H_in_f H_r H_d.
rewrite H_emp /=.
apply NMapFacts.not_find_in_iff.
move => H_in.
by apply NMapFacts.empty_in_iff in H_in.
Qed.

(* in_after_all_fail_status *)
Lemma Tree_in_after_all_fail_level : 
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall (n : name), In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) ->
    forall lvo', before_all (Level lvo') Fail (net.(odnwPackets) n' n).
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
- move => n H_n H_f n' H_n' lvo'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by rewrite (Tree_self_channel_empty H).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H.
    rewrite collate_map2snd_not_in_related //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) //=.
    by left.
  * have H_neq: n <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Tree_inactive_no_incoming H).
    case (in_dec name_eq_dec n' failed) => H_dec'; last first.
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H.
      rewrite collate_ls_live_related //.
      rewrite collate_neq //.
      rewrite (Tree_inactive_no_incoming H) //=.
      by left.
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Tree_inactive_no_incoming H).
  * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
    have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; unfold update2 in *; break_if; break_and; subst_max; try by eauto.
  * have IH := IHrefl_trans_1n_trace1 _ H11 H13 _ H14 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H6 H8 _ H9 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H0 H8 _ H9 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H6 H8 _ H9 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHrefl_trans_1n_trace1 _ H11 H13 _ H3 lvo'.    
    have H_neq: n <> n'.
      move => H_eq.
      rewrite H_eq in H5.
      by rewrite (Tree_self_channel_empty H) in H5.             
    break_if; first by break_and.
    apply: before_all_not_in_2.
    move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in; last by case: H_in.
    contradict H_in.
    by apply: Tree_not_failed_no_fail; eauto.
  * break_if; last by eauto.
    break_and; subst.
    have H_neq: n <> n' by break_or_hyp; auto.      
    have IH := IHrefl_trans_1n_trace1 _ H11 H13 _ H14 lvo'.
    find_rewrite.
    simpl in *.
    break_or_hyp; last by break_and.
    exact: before_all_not_in_1.
  * have IH := IHrefl_trans_1n_trace1 _ H12 H14 _ H15 lvo'.
    find_rewrite.
    simpl in *.
    break_or_hyp; last by break_and.
    exact: before_all_not_in_1.
  * have H_neq: n <> n'.
      move => H_eq.
      rewrite H_eq in H5.
      by rewrite (Tree_self_channel_empty H) in H5.
    break_if; first by break_and; subst_max.
    apply: before_all_not_in_2.
    move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in; last by case: H_in.
    contradict H_in.
    by apply: Tree_not_failed_no_fail; eauto.
  * break_if; last by eauto.
    break_and; subst.
    have H_neq: n <> n' by break_or_hyp; auto.      
    have IH := IHrefl_trans_1n_trace1 _ H7 H9 _ H10 lvo'.
    find_rewrite.
    simpl in *.
    break_or_hyp; last by break_and.
    exact: before_all_not_in_1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; try by eauto.
  have IH := IHrefl_trans_1n_trace1 _ H11 H13 _ H14 lvo'.
  case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
  subst.
  have H_f := Tree_not_failed_no_fail H _ H3 H2 n.
  apply before_all_not_in_2.
  rewrite /level_adjacent NSet.fold_spec /flip /=.
  move => H_in.
  case: H_f.
  move: H_in.
  elim: (NSet.elements _) => //=.
  rewrite /flip /= /level_fold.
  move => n'' ns IH' H_in.
  rewrite (@fold_left_level_fold_eq Tree_TreeMsg) in H_in.
  rewrite (@fold_left_level_fold_eq Tree_TreeMsg) in IH'.
  rewrite app_nil_r in IH'.
  rewrite collate_app in H_in.
  apply IH'.
  rewrite /tree_level /= in H_in.
  update2_destruct_hyp; find_inversion; subst; rewrite_update2.
  - apply in_app_or in H_in.
    by case: H_in => H_in; last by case: H_in.
  - have H_neq: n'' <> n by move => H_eq; find_rewrite.
    rewrite_update2.
    by find_rewrite.
- move => n H_n H_f n' H_n' lvo'.
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
  exact: @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H.
Qed.

Lemma Tree_in_level_adjacent_or_incoming_new :
  forall net failed tr, 
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) ->
    forall lvo', In (Level lvo') (net.(odnwPackets) n' n) ->
    forall d, net.(odnwState) n = Some d ->
    NSet.In n' d.(adjacent) \/ In New (net.(odnwPackets) n' n).
Proof.
  move => net failed tr H.
  change failed with (fst (failed, net)).
  change net with (snd (failed, net)) at 1 3 4 5 6.
  remember step_ordered_dynamic_failure_init as y in *.
  move: Heqy.
  induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init.
  concludes.
  match goal with
  | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] =>
    invcs H
  end.
  - move => n H_n H_f n' H_n' lvo'.
    break_or_hyp; break_or_hyp.
    * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
      rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
        by rewrite (Tree_self_channel_empty H).
    * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
      case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
        by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H).
        have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H.
        rewrite collate_map2snd_not_in_related //.
        rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H) //=.
        move => H_or.
          by break_or_hyp.
    * have H_neq: n <> n' by move => H_eq; find_reverse_rewrite.
      case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
        by rewrite (Tree_inactive_no_incoming H).
        case (in_dec name_eq_dec n' failed) => H_dec'; last first.
        have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H.
        rewrite collate_ls_live_related //.
        rewrite collate_neq //.
        rewrite (Tree_inactive_no_incoming H) //=.
        move => H_or.
          by break_or_hyp.
          rewrite collate_ls_in_remove_all //.
          rewrite collate_neq //.
            by rewrite (Tree_inactive_no_incoming H).
    * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
      have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
      rewrite collate_ls_neq_to //.
      rewrite collate_neq //.
      rewrite_update.
        by eauto.
  - intros.
    find_apply_lem_hyp net_handlers_NetHandler.
    net_handler_cases => //=; simpl in *.
    + destruct (name_eq_dec to n), (name_eq_dec from n');
        subst; rewrite_update; rewrite_update2; find_inversion.
      * assert (H_in: In (Level lvo') (odnwPackets net0 n' n)).
        {
          repeat find_rewrite.
          auto with datatypes.
        }
        eapply IHrefl_trans_1n_trace1 with (d:=d) in H_in; eauto.
        break_or_hyp; last by find_rewrite; simpl in *; break_or_hyp; last by right.
        exfalso.
        match goal with
        | [ H : refl_trans_1n_trace _ _ (?failed, net0) ?tr |- _ ] =>
          assert (H_step: step_ordered_dynamic_failure_star
                            step_ordered_dynamic_failure_init
                            (failed, net0) tr)
            by auto;
            pose proof (Tree_in_after_all_fail_level H_step n) as H_after; simpl in H_after
        end.
        assert (before_all (Level lvo') Fail (odnwPackets net0 n' n)) by eauto.
        find_rewrite.
        simpl in *;
          break_or_hyp;
          break_and;
            by auto.
      * match goal with
        | [H : In (Level lvo') (odnwPackets _ n' n) |- _ ] =>
          eapply IHrefl_trans_1n_trace1 with (d:=d) in H; auto
        end.
        break_or_hyp.
        -- left.
           find_rewrite.
           apply NSet.remove_spec;
             by auto.
        -- by auto.
      * by eauto.
      * by eauto.
    + (* Fail case with broadcast = false *)
      destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try eauto.
      * exfalso.
        assert (before_all (Level lvo') Fail (odnwPackets net0 n' n))
          by eauto using Tree_in_after_all_fail_level.
        repeat find_rewrite.
        find_eapply_lem_hyp before_all_head_not_in; congruence.
      * find_inversion.
        match goal with
        | [H : In (Level lvo') (odnwPackets _ n' n) |- _ ] =>
          eapply IHrefl_trans_1n_trace1 with (d:=d) in H; auto
        end.
        break_or_hyp; [left|by auto].
        find_injection.
        repeat find_rewrite.
        apply NSet.remove_spec;
          by auto.
    + (* Fail case with broadcast = true (same proof) *)
      destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try eauto.
      * exfalso.
        assert (before_all (Level lvo') Fail (odnwPackets net0 n' n))
          by eauto using Tree_in_after_all_fail_level.
        repeat find_rewrite.
        find_eapply_lem_hyp before_all_head_not_in; congruence.
      * find_inversion.
        match goal with
        | [H : In (Level lvo') (odnwPackets _ n' n) |- _ ] =>
          eapply IHrefl_trans_1n_trace1 with (d:=d) in H; auto
        end.
        break_or_hyp; [left|by auto].
        find_rewrite.
        apply NSet.remove_spec;
          by auto.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp; [left|]; first by find_inversion.
        find_rewrite.
        simpl in *.
        by break_or_hyp; last by right.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp.
        -- left. by find_inversion.
        -- find_rewrite.
           right.
           by eauto using In_cons_neq.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp; [left|]; first by repeat find_rewrite.
        find_rewrite.
        simpl in *.
        by break_or_hyp; last by right.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp.
        -- repeat find_rewrite.
           auto.
        -- find_rewrite.
           right.
           eauto ||
           eapply In_cons_neq;
             eauto || congruence.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp; [left|]; first by repeat find_rewrite.
        find_rewrite.
        simpl in *.
        by break_or_hyp; last by right.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp.
        -- repeat find_rewrite.
           auto.
        -- find_rewrite.
           right.
           eauto ||
           eapply In_cons_neq;
             eauto || congruence.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp; [left|]; first by repeat find_rewrite.
        find_rewrite.
        simpl in *.
        by break_or_hyp; last by right.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp.
        -- repeat find_rewrite.
           auto.
        -- find_rewrite.
           right.
           eauto ||
           eapply In_cons_neq;
             eauto || congruence.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp; [left|]; first by repeat find_rewrite.
        find_rewrite.
        simpl in *.
        by break_or_hyp; last by right.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        by (eapply IHrefl_trans_1n_trace1; eauto; repeat find_rewrite; eauto with datatypes).
        break_or_hyp.
        -- repeat find_rewrite.
           auto.
        -- find_rewrite.
           right.
           eauto ||
           eapply In_cons_neq;
             eauto || congruence.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (n' <> n).
        {
          intro H_eq; subst.
          rewrite_update2.
          match goal with
          | [ H : context[ _ ++ [Level (Some 0)] ] |- _ ] =>
            eapply Tree_self_channel_empty with (n := n) in H;
              simpl in H;
              symmetry in H
          end.
          rewrite_update2.
          eapply app_cons_not_nil; eauto.
        }
        rewrite_update2; rewrite_update.
        assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        {
          eapply IHrefl_trans_1n_trace1 with (lvo':=lvo'); eauto.
          find_rewrite.
          auto with datatypes.
        }
        repeat find_rewrite.
        by auto with set.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)) by eauto.
        break_or_hyp; [left|by auto].
        find_rewrite.
        by auto with set.
      * move {H1}.
        case (name_eq_dec from n) => H_dec.
          subst_max.
          case (name_eq_dec to n') => H_dec.
            subst_max.
            rewrite_update2.
            have H_in: In New (odnwPackets net0 n n') by find_rewrite; left.
            have H_or: NSet.In n d.(adjacent) \/ In New (odnwPackets net0 n n') by right.
            have H_rec := Tree_adjacent_or_incoming_new_reciprocal H _ H3 H2 H0 H7 H4 H10 H_or.
            case: H_rec => H_rec; first by left.
            right.
            apply in_or_app.
            by left.
          rewrite_update2.
          by eauto.
        rewrite_update2.
        by eauto.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        {
          eapply IHrefl_trans_1n_trace1 with (lvo':=lvo'); eauto.
          find_rewrite.
          auto with datatypes.
        }
        break_or_hyp;
          repeat find_rewrite;
          by auto with set.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)) by eauto.
        break_or_hyp;
          repeat find_rewrite;
          by auto with set.
    + destruct (name_eq_dec from n'), (name_eq_dec to n);
        subst; rewrite_update2; rewrite_update; try find_injection; eauto.
      * assert (n' <> n).
        {
          intro H_eq; subst.
          rewrite_update2.
          match goal with
          | [ H : context[ _ ++ _ ] |- _ ] =>
            eapply Tree_self_channel_empty with (n := n) in H;
              simpl in H;
              symmetry in H
          end.
          rewrite_update2.
          eapply app_cons_not_nil; eauto.
        }
        rewrite_update2; rewrite_update.
        assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
        {
          eapply IHrefl_trans_1n_trace1 with (lvo':=lvo'); eauto.
          rewrite_update.
          find_rewrite.
          auto with datatypes.
        }
        break_or_hyp; [left|]; first by repeat find_rewrite; auto with set.
        repeat find_rewrite.
        by left; auto with set.
      * assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)) by eauto.
        break_or_hyp; [left|by auto].
        find_rewrite.
        by auto with set.
      * move {H1}.
        case (name_eq_dec from n) => H_dec.
          subst_max.
          case (name_eq_dec to n') => H_dec'.
            subst_max.
            rewrite_update2.
            have H_in: In New (odnwPackets net0 n n') by find_rewrite; left.
            have H_or: NSet.In n d.(adjacent) \/ In New (odnwPackets net0 n n') by right.
            have H_rec := Tree_adjacent_or_incoming_new_reciprocal H _ H3 H2 H0 H7 H4 H10 H_or.
            case: H_rec => H_rec; first by left.
            right.
            apply in_or_app.
            by left.
          rewrite_update2.
          by eauto.
        rewrite_update2.
        by eauto.
  - find_apply_lem_hyp input_handlers_IOHandler.
    io_handler_cases => //=; simpl in *; eauto.
    * eapply IHrefl_trans_1n_trace1; eauto.
      destruct (name_eq_dec h n);
        rewrite_update;
        try find_injection;
        auto.
    * destruct (name_eq_dec n n');
        subst; rewrite_update; try find_inversion;
          [match goal with
           | [ H : In (Level lvo') ?chan,
               H' : refl_trans_1n_trace _ _ (_, ?net) _ |- _ ] =>
             assert (H_empty: odnwPackets net n' n' = [])
               by eauto using Tree_self_channel_empty;
             simpl in H_empty;
             repeat find_rewrite;
             exfalso;
             auto with datatypes
           end|].
      destruct (name_eq_dec h n');
        subst; rewrite_update; try find_inversion; repeat find_rewrite.
      -- cut (NSet.In n' (adjacent d0) \/ In New (odnwPackets net0 n' n));
           try by intuition eauto using collate_in_in.
         match goal with
         | [ H : In (Level lvo') (collate _ _ _ ?sends _ _) |- _ ] =>
           destruct (In_dec name_eq_dec n (map fst sends));
             [eauto|erewrite collate_not_in_eq in H; eauto]
         end.
         eapply Tree_adjacent_or_incoming_new_reciprocal; eauto.
         unfold level_adjacent, flip, level_fold in *.
         find_rewrite_lem NSet.fold_spec.
         find_apply_lem_hyp in_map_iff.
         break_exists_name pkt; break_and.
         find_eapply_lem_hyp in_fold_left_by_cons_in;
           (repeat decide equality || auto using name_eq_dec).
         break_or_hyp => //=.
         break_exists; break_and.
         cut (InA eq (fst pkt) (NSet.elements (adjacent d)));
           cut (In (fst pkt) (NSet.elements (adjacent d)));
             by auto with set || by repeat find_rewrite.
      -- destruct (name_eq_dec h n);
           subst; rewrite_update; try find_inversion.
         ** assert (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n)).
            {
              eapply IHrefl_trans_1n_trace1; eauto.
              erewrite <- collate_neq; eauto.
            }
            break_or_hyp;
              find_rewrite;
              auto using collate_in_in.
         ** assert (NSet.In n' (adjacent d0) \/ In New (odnwPackets net0 n' n)).
            {
              eapply IHrefl_trans_1n_trace1; eauto.
              erewrite <- collate_neq; eauto.
            }
            break_or_hyp;
              find_rewrite;
              auto using collate_in_in.
    * eapply IHrefl_trans_1n_trace1; eauto.
      destruct (name_eq_dec h n);
        rewrite_update;
        try find_injection;
        auto.
    * eapply IHrefl_trans_1n_trace1; eauto.
      destruct (name_eq_dec h n);
        rewrite_update;
        try find_injection;
        auto.
    * eapply IHrefl_trans_1n_trace1; eauto.
      destruct (name_eq_dec h n);
        rewrite_update;
        try find_injection;
        auto.
  - intros.
    cut (NSet.In n' (adjacent d) \/ In New (odnwPackets net0 n' n));
      try by intuition auto using collate_in_in.
    eapply IHrefl_trans_1n_trace1 with (lvo':=lvo'); eauto.
    eapply collate_map2snd_in_neq_in_before; eauto || congruence.
Qed.

Lemma Tree_in_before_all_new_level : 
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) ->
    forall lvo', before_all New (Level lvo') (net.(odnwPackets) n' n).
Proof.
move => net failed tr H_step.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' lvo'.
  break_or_hyp; break_or_hyp.
  * have H_rel: ~ adjacent_to n n by apply adjacent_to_irreflexive.
    rewrite collate_ls_not_related //.
    rewrite collate_map2snd_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).    
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
    rewrite collate_map2snd_not_in_related //.
    rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1) //=.
    by left.
  * have H_neq: n <> n' by move => H_eq; subst_max.
    case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Tree_inactive_no_incoming H_step1).
    case (in_dec name_eq_dec n' failed0) => H_dec'; last first.
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
      rewrite collate_ls_live_related //.
      rewrite collate_neq //.
      rewrite (Tree_inactive_no_incoming H_step1) //=.
      by left.
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Tree_inactive_no_incoming H_step1).
  * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
    have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; simpl in *; update2_destruct_max_simplify;
    repeat find_rewrite; auto; try tuple_inversion.
  * have IH := IHH_step1 _ H9 H11 _ H12 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H10 H12 _ H13 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H10 H12 _ H13 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H1 H0 _ H7 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H1 H0 _ H7 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H1 H0 _ H7 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H1 H0 _ H13 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H1 H0 _ H13 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have H_neq: n <> n'.
      move => H_eq.
      subst_max.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    move {H_step2}.
    rewrite_update2.
    have IH := IHH_step1 _ H9 H11 _ H12 lvo'.
    exact: before_all_neq_append.
  * move {H_step2}.
    destruct_update2; last by eauto.
    tuple_inversion.
    have IH := IHH_step1 _ H9 H11 _ H12 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * have IH := IHH_step1 _ H10 H12 _ H13 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
  * move {H_step2}.
    destruct_update2.
    + tuple_inversion.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    + have H_neq: n <> n' by move => H_eq; subst_max.
      have IH := IHH_step1 _ H5 H7 _ H1 lvo'.
      exact: before_all_neq_append.
  * move {H_step2}.
    destruct_update2; last by eauto.
    tuple_inversion.
    have IH := IHH_step1 _ H5 H7 _ H8 lvo'.
    find_rewrite.
    case: IH => IH; first exact: before_all_not_in_1.
    by break_and.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * by eauto.
  * case (name_eq_dec h n') => H_dec; last by rewrite collate_neq; eauto.
    subst_max.
    have H_adj_in := Tree_in_adj_adjacent_to H_step1 _ H1 H0 H2.
    have H_adj_in_elts: forall k, In k (NSet.elements d.(adjacent)) -> adjacent_to k n'.
      move => k H_in.
      have H_adj_in_spec := NSet.elements_spec1 d.(adjacent) k.
      apply H_adj_in.
      apply H_adj_in_spec.
      apply InA_alt.
      by exists k.
    case (adjacent_to_dec n n') => H_adj.
    + case (in_dec Msg_eq_dec New (net0.(odnwPackets) n n')) => H_in.
        have H_n := Tree_new_incoming_not_in_adj H_step1 _ H1 H0 H_in H2.
        have H_inn: ~ In n (NSet.elements d.(adjacent)).
          move => H_inn.
          case: H_n.
          apply NSet.elements_spec1.
          apply InA_alt.
          by exists n.
        move: H_inn.
        rewrite /level_adjacent NSet.fold_spec /flip /=.
        elim: NSet.elements => //=; first by eauto.
        move => k ns IH H_inn.
        rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /= {2}/level_fold /=.
        rewrite collate_app /=.
        have H_neq: k <> n by auto.
        have H_nin: ~ In n ns by auto.
        rewrite_update2.
        exact: IH.
      have H_adj_new := Tree_adjacent_to_no_incoming_new_n_adjacent H_step1 H12 H0 H9 H11 H_adj H2 H_in.
      apply NSet.elements_spec1 in H_adj_new.
      have H_nd := NSet.elements_spec2w d.(adjacent).
      apply InA_alt in H_adj_new.
      break_exists.
      break_and.
      have H_eq_x: x = n by [].
      subst_max.
      find_apply_lem_hyp in_split.
      break_exists.
      find_rewrite.
      have H_not_in_1: ~ In n x.
        move => H_nx.
        apply NoDupA_swap in H_nd; last exact: eq_equivalence.
        inversion H_nd; subst_max.
        case: H14.
        apply InA_alt.
        exists n.
        split => //.
        apply in_or_app.
        by left.
      have H_not_in_2: ~ In n x0.
        move => H_nx.
        apply NoDupA_swap in H_nd; last exact: eq_equivalence.
        inversion H_nd; subst_max.
        case: H14.
        apply InA_alt.
        exists n.
        split => //.
        apply in_or_app.
        by right.
      rewrite /level_adjacent NSet.fold_spec /flip /=.
      rewrite H8 /= fold_left_app /= {2}/level_fold /= (@fold_left_level_fold_eq Tree_TreeMsg).
      rewrite collate_not_in; last first.
        simpl.
        move: H_not_in_2 {H_nd H8}.
        elim: x0 => //=.
        move => k ns IH H_inn.
        rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /= map_app /=.
        move => H_k.
        find_apply_lem_hyp in_app_or.
        break_or_hyp; last by simpl in *; break_or_hyp; eauto.
        by concludes.
      set e := ((n, _)).
      set l := fold_left _ _ _.
      have ->: e :: l = [e] ++ l by [].
      rewrite collate_not_in_rest; last first.
        rewrite /l {l} /=.
        move: H_not_in_1 {H_nd H8}.
        elim: x => //=.
        move => k ns IH H_inn.
        rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /= map_app /=.
        move => H_k.
        find_apply_lem_hyp in_app_or.
        break_or_hyp; last by simpl in *; break_or_hyp; eauto.
        by concludes.
      rewrite /=.
      rewrite_update2.
      by apply: before_all_neq_append; eauto.
    + rewrite collate_not_in_eq; first by eauto.
      unfold level_adjacent.
      rewrite NSet.fold_spec /flip /=.
      move: H_adj_in_elts.
      elim: (NSet.elements _) => //=; first by auto.
      move => k ns IH H_adj_in_elts.
      rewrite /level_fold /=.
      rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
      rewrite map_app /=.
      move => H_in.
      apply in_app_or in H_in.
      case: H_in => H_in; last first.
        case: H_in => H_in //.
        subst_max.
        contradict H_adj.
        apply H_adj_in_elts.
        by left.
      contradict H_in.
      apply IH.
      move => k' H_in_k'.
      apply H_adj_in_elts.
      by right.
  * by eauto.
  * by eauto.
  * by eauto.
- move => n H_n H_f n' H_n' lvo'.
  have H_neq: h <> n by auto.
  have H_in: ~ In n failed0 by auto.
  case (name_eq_dec h n') => H_dec; last by rewrite collate_neq; eauto.
  subst_max.
  case (adjacent_to_dec n' n) => H_dec'; last by rewrite collate_map2snd_not_related; eauto.
  have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
  rewrite collate_map2snd_not_in_related //.
  by apply: before_all_neq_append; eauto.
Qed.

(* bfs_net_ok_notin_adj_not_sent_status *)
Lemma Tree_notin_adjacent_not_sent_level :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d -> ~ NSet.In n' d.(adjacent) ->
    forall lvo', ~ In (Level lvo') (net.(odnwPackets) n n').
Proof.
move => net failed tr H_step.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 5 6.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' H_f' d H_d H_ins lvo'.
  break_or_hyp; break_or_hyp.
  * have H_rel: ~ adjacent_to n n by apply adjacent_to_irreflexive.
    rewrite collate_ls_not_related //.
    rewrite collate_map2snd_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).
  * rewrite_update.
    have H_neq: n' <> n by move => H_eq; subst_max.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Tree_inactive_no_incoming H_step1).
    case (in_dec name_eq_dec n' failed0) => H_dec'; first by rewrite collate_ls_in_remove_all.
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
    rewrite collate_ls_live_related //.
    rewrite collate_neq //.           
    rewrite (Tree_inactive_no_incoming H_step1) //=.
    move => H_in.
    by case: H_in.
  * rewrite_update.
    find_injection.
    simpl in *.
    have H_neq: n <> n' by move => H_eq; subst_max.
    rewrite collate_ls_neq_to //.
    case (adjacent_to_dec n n') => H_adj.
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
      rewrite collate_map2snd_not_in_related //.
      rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1) //=.
      move => H_in.
      by break_or_hyp.    
    rewrite collate_map2snd_not_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).
  * have H_neq: h <> n by move => H_eq; subst_max.
    have H_neq': h <> n' by move => H_eq; subst_max.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    rewrite_update.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; simpl in *; update2_destruct_max_simplify;
    update_destruct_max_simplify; repeat find_rewrite; auto; try tuple_inversion; try find_injection; repeat find_rewrite.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have H_bef := Tree_in_after_all_fail_level H_step1 _ H1 H0 _ H9 lvo'.
    find_rewrite.
    simpl in *.
    break_or_hyp => //.
    by break_and.
  * case (name_eq_dec from n) => H_dec.
      subst_max.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    case (name_eq_dec from n') => H_dec'.
      subst_max.
      have H_f := Tree_not_failed_no_fail H_step1 _ H12 H13 n.
      find_rewrite.
      case: H_f.
      by left.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H15.
      exact: NSetFacts.remove_2.
    by have IH := IHH_step1 _ H9 H11 _ H12 H13 _ H2 H_ins lvo'.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have H_f := Tree_not_failed_no_fail H_step1 _ H10 H12 n'.
    find_rewrite.
    by case: H_f; left.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_f := Tree_not_failed_no_fail H_step1 _ H13 H14 n.
      find_rewrite.
      by case: H_f; left.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H16.
      by auto with set.
    by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have H_f := Tree_not_failed_no_fail H_step1 _ H10 H12 n'.
    find_rewrite.
    by case: H_f; left.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_f := Tree_not_failed_no_fail H_step1 _ H13 H14 n.
      find_rewrite.
      by case: H_f; left.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H16.
      by auto with set.
    by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H4 H6 _ H7 H8 _ H9 H10 x.
    find_rewrite.
    by case: IH; left.
  * by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H H6 _ H7 H8 _ H9 H10 lvo'.
    find_rewrite.
    case: IH.
    by right.
  * by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H4 H6 _ H7 H8 _ H9 H10 (Some x).
    find_rewrite.
    by case: IH; left.
  * by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H10 H12 _ H13 H14 _ H15 H16 lvo'.
    find_rewrite.
    by case: IH; right.
  * by eauto.
  * by eauto.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H10 H12 _ H13 H14 _ H15 H16 lvo'.
    find_rewrite.
    by case: IH; right.
  * by eauto.
  * by eauto.
  * by auto with set.
  * by auto.
  * have H_neq: from <> n' by move => H_eq; subst_max.
    rewrite_update2.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H15.
      by auto with set.
    by eauto.
  * have IH := IHH_step1 _ H9 H11 _ H12 H13 _ H14 H15 lvo'.
    update2_destruct_max_simplify => //.
    find_injection.
    find_rewrite.
    simpl in *.
    case: IH.
    by right.
  * by find_rewrite_lem (Tree_self_channel_empty H_step1).
  * have IH := IHH_step1 _ H10 H12 _ H13 H14 _ H15 H16 lvo'.
    find_rewrite.
    case: IH.
    by right.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      by auto with set.
    have H_ins: ~ NSet.In n' d.(adjacent) by auto with set.
    by eauto.
  * by eauto.
  * by auto with set.
  * by auto.
  * have H_neq: from <> n' by move => H_eq; subst_max.
    rewrite_update2.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H15.
      by auto with set.
    by eauto.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      rewrite_update2.
      by eauto.
    have IH := IHH_step1 _ H5 H7 _ H8 H9 _ H10 H11 lvo'.
    update2_destruct_max_simplify => //.
    find_injection.
    find_rewrite.
    simpl in *.
    case: IH.
    by right.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; simpl in *;
    update_destruct_max_simplify; repeat find_rewrite; auto; try tuple_inversion; try find_injection; repeat find_rewrite.
  * by eauto.
  * by eauto.
  * have IH := IHH_step1 _ H9 H11 _ H12 H13 _ H2 H15 lvo'.
    have H_ins: ~ In n' (NSet.elements d.(adjacent)).
      move => H_ins.
      case: H15.
      have H_adj_in_spec := NSet.elements_spec1 d.(adjacent) n'.
      apply H_adj_in_spec.
      apply InA_alt.
      by exists n'.
    contradict H16.
    move: H_ins.
    rewrite /level_adjacent NSet.fold_spec /flip /=.
    elim: NSet.elements => //=.
    move => k ns IH' H_in.
    have H_neq: k <> n' by auto.
    rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
    rewrite {2}/level_fold /= collate_app /=.
    rewrite_update2.
    have H_in': ~ In n' ns by auto.
    exact: IH'.
  * rewrite collate_neq // in H16.
    by eauto.
  * by eauto.
  * by eauto.
  * by eauto.
  * by eauto.
  * by eauto.
  * by eauto.
- move => n H_n H_f n' H_n' H_f' d H_d H_ins lvo'.
  have H_neq: h <> n by auto.
  rewrite collate_neq //.
  have H_fn: ~ In n failed0 by auto.
  have H_fn': ~ In n' failed0 by auto.
  by eauto.
Qed.

Lemma Tree_level_head_in_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In n' net.(odnwNodes) ->
   forall lvo', head (net.(odnwPackets) n' n) = Some (Level lvo') ->
   forall d, net.(odnwState) n = Some d ->
   NSet.In n' d.(adjacent).
Proof.
move => net failed tr H_step.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3 4 5.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f n' H_n' lvo'.
  break_or_hyp; break_or_hyp.
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    rewrite collate_map2snd_not_in; last by eauto using in_remove_all_was_in.
    by rewrite (Tree_self_channel_empty H_step1).
  * rewrite collate_ls_not_in; last by apply: not_in_not_in_filter_rel; eauto using in_remove_all_was_in.
    case (adjacent_to_dec n' n) => H_dec; last first.
      rewrite collate_map2snd_not_related //.
      by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
    rewrite collate_map2snd_not_in_related //.
    by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1).
  * have H_neq: n <> n' by move => H_eq; find_reverse_rewrite.
    case (adjacent_to_dec n n') => H_dec; last first.
      rewrite collate_ls_not_related //.
      rewrite collate_neq //.
      by rewrite (Tree_inactive_no_incoming H_step1).
    case (in_dec name_eq_dec n' failed0) => H_dec'; last first.
      have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
      rewrite collate_ls_live_related //.
      rewrite collate_neq //.
      by rewrite (Tree_inactive_no_incoming H_step1).
    rewrite collate_ls_in_remove_all //.
    rewrite collate_neq //.
    by rewrite (Tree_inactive_no_incoming H_step1).
  * have H_neq: h <> n by move => H_eq; find_reverse_rewrite.
    have H_neq': h <> n' by move => H_eq; repeat find_rewrite.
    rewrite collate_ls_neq_to //.
    rewrite collate_neq //.
    rewrite_update.
    by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; simpl in *; update2_destruct_max_simplify;
    repeat find_rewrite; auto; try tuple_inversion.
  * have H_bef := Tree_in_after_all_fail_level H_step1 _ H9 H11 _ H12 lvo'.
    find_rewrite.
    simpl in *.
    case: H_bef => H_bef; last by case: H_bef.
    destruct ms => //.
    simpl in *.
    find_inversion.
    by case: H_bef; left.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by apply NSetFacts.remove_2; eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    have H_bef := Tree_in_after_all_fail_level H_step1 _ H10 H12 _ H13 lvo'.
    find_rewrite.
    simpl in *.
    case: H_bef => H_bef; last by case: H_bef; break_and.
    destruct ms => //.
    simpl in *.
    find_injection.
    by case: H_bef; left.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by apply NSetFacts.remove_2; eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    have H_bef := Tree_in_after_all_fail_level H_step1 _ H10 H12 _ H13 lvo'.
    find_rewrite.
    simpl in *.
    case: H_bef => H_bef; last by case: H_bef; break_and.
    destruct ms => //.
    simpl in *.
    find_injection.
    by case: H_bef; left.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by apply NSetFacts.remove_2; eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    have H_hd: hd_error (odnwPackets net0 n' n) = Some (Level x) by find_rewrite.
    by have IH := IHH_step1 _ H4 H6 _ H7 _ H_hd _ H2.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      by eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    find_rewrite.
    have H_hd: hd_error (odnwPackets net0 n' n) = Some (Level (Some x)) by find_rewrite.
    by have IH := IHH_step1 _ H1 H0 _ H7 _ H_hd _ H2.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    find_rewrite.
    have H_hd: hd_error (odnwPackets net0 n' n) = Some (Level (Some x)) by find_rewrite.
    by have IH := IHH_step1 _ H1 H0 _ H7 _ H_hd _ H2.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    find_rewrite.
    have H_hd: hd_error (odnwPackets net0 n' n) = Some (Level None) by find_rewrite.
    by have IH := IHH_step1 _ H1 H0 _ H13 _ H_hd _ H2.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by eauto.
    rewrite_update.
    by eauto.
  * rewrite_update.
    find_injection.
    find_rewrite.
    have H_hd: hd_error (odnwPackets net0 n' n) = Some (Level None) by find_rewrite.
    by have IH := IHH_step1 _ H1 H0 _ H13 _ H_hd _ H2.
  * have H_neq: ~ (from = n' /\ to = n) by move => H_neq; break_and; subst_max.
    case (name_eq_dec from n') => H_dec.
      subst_max.
      have H_neq': to <> n by auto.
      rewrite_update.
      by eauto.
    case (name_eq_dec to n) => H_dec'.
      subst_max.
      have H_neq': from <> n' by auto.
      rewrite_update.
      find_injection.
      find_rewrite.
      by eauto.
    rewrite_update.
    by eauto.
  * update_destruct_max_simplify.
      find_injection.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    update2_destruct_max_simplify; first by find_injection.
    have H_in_new: In New (odnwPackets net0 n n') by find_rewrite; left.
    have H_adj := Tree_in_new_then_adjacent H_step1 _ H1 H0 _ H_in_new.
    apply adjacent_to_symmetric in H_adj.
    case (in_dec Msg_eq_dec New (odnwPackets net0 n' n)) => H_in; last exact: (Tree_adjacent_to_no_incoming_new_n_adjacent H_step1 H9 H11 H1 H0 H_adj H14 H_in).
    have IH := IHH_step1 _ H9 H11 _ H1 lvo'.
    have H_bef := Tree_in_before_all_new_level H_step1 _ H9 H11 _ H1 lvo'.
    destruct (odnwPackets net0 n' n) => //.
    simpl in *.
    find_injection.
    case: H_in => H_in //.
    break_or_hyp => //.
    by break_and.
  * case (name_eq_dec to n) => H_dec.
      subst_max.
      rewrite_update.
      find_injection.
      find_rewrite.
      case (name_eq_dec from n') => H_dec'; first exact: NSetFacts.add_1.
      apply NSetFacts.add_2.
      update2_destruct_max_simplify.
        find_injection.
        by find_rewrite.
      by eauto.
    rewrite_update.
    update2_destruct_max_simplify.
      find_injection.
      find_rewrite.
      find_injection.
      by find_rewrite.
    by eauto.
  * rewrite_update.
    find_injection.
    find_rewrite.
    exact: NSetFacts.add_1.
  * update_destruct_max_simplify.
      find_injection.
      find_rewrite.
      apply NSetFacts.add_2.
      by eauto.
    by eauto.
  * update_destruct_max_simplify.
      find_injection.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    update2_destruct_max_simplify.
      find_injection.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).     
    have H_in_new: In New (odnwPackets net0 n n') by find_rewrite; left.
    have H_adj := Tree_in_new_then_adjacent H_step1 _ H1 H0 _ H_in_new.
    apply adjacent_to_symmetric in H_adj.
    case (in_dec Msg_eq_dec New (odnwPackets net0 n' n)) => H_in; last exact: (Tree_adjacent_to_no_incoming_new_n_adjacent H_step1 H5 H7 H1 H0 H_adj H10 H_in).          
    have IH := IHH_step1 _ H5 H7 _ H8 lvo'.
    have H_bef := Tree_in_before_all_new_level H_step1 _ H5 H7 _ H1 lvo'.
    destruct (odnwPackets net0 n' n) => //.
    simpl in *.
    find_injection.
    case: H_in => H_in //.
    break_or_hyp => //.
    by break_and.
  * have H_neq: from <> to. 
      move => H_eq; find_rewrite.
      subst_max.
      by find_rewrite_lem (Tree_self_channel_empty H_step1). 
    case (name_eq_dec from n') => H_dec.
      subst_max.
      update_destruct_max_simplify.
        find_injection.
        rewrite_update2.
        find_rewrite.
        by auto with set.
      rewrite_update2.
      by eauto.
    rewrite_update2.
    update_destruct_max_simplify.
      find_injection.
      find_rewrite.
      have IH := IHH_step1 _ H5 H7 _ H8 lvo' H9 _ H2.
      by auto with set.
    by eauto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; simpl in *; update_destruct_max_simplify;
    repeat find_rewrite; try find_injection; try by eauto.
  * case (name_eq_dec n n') => H_dec.
      subst_max.
      find_rewrite.
      have H_ins := Tree_node_not_adjacent_self H_step1 H1 H0 H2.
      suff H_suff: In n' (NSet.elements d.(adjacent)).
        have H_adj_in_spec := NSet.elements_spec1 d.(adjacent) n'.
        apply H_adj_in_spec.
        apply InA_alt.
        by exists n'.
      have H_ins': ~ In n' (NSet.elements d.(adjacent)).
        move => H_in.
        case: H_ins.
        have H_adj_in_spec := NSet.elements_spec1 d.(adjacent) n'.
        apply H_adj_in_spec.
        apply InA_alt.
        by exists n'.
      move: H_ins' H13.
      rewrite /level_adjacent /= NSet.fold_spec /flip /=.
      elim: NSet.elements => //=.
        move => H_ins' H_hd.
        by find_rewrite_lem (Tree_self_channel_empty H_step1).
      rewrite {3}/level_fold /=.
      move => n ns IH H_in.
      have H_neq: n <> n' by auto.
      rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
      rewrite collate_not_in_rest //=; last by move => H_neq'; break_or_hyp.
      move => H_in'.
      right.
      by eauto.
    rewrite collate_neq // in H13.
    find_rewrite.
    by eauto.
  * case (name_eq_dec h n') => H_dec.
      subst_max.
      case (adjacent_to_dec n n') => H_adj; last first.
        have H_ins: ~ NSet.In n d.(adjacent).
          move => H_ins.
          case: H_adj.
          exact: (Tree_in_adj_adjacent_to H_step1 _ H12 H0 H2 H_ins).
        have H_inl := Tree_notin_adjacent_not_sent_level H_step1 _ H1 H0 H9 H11 H2 H_ins lvo'.
        have H_ins': ~ In n (NSet.elements d.(adjacent)).
          move => H_ins'.
          case: H_ins.
          apply NSetFacts.elements_2.
          apply InA_alt.
          by exists n.
        move: H13 H_ins'.
        rewrite /level_adjacent NSet.fold_spec /flip /=.
        elim: NSet.elements => //=.
          move => H_hd H_ins'.
          destruct (odnwPackets net0 n' n); simpl in * => //.
          find_injection.
          case: H_inl.
          by left.
        move => k ns IH H_ins' H_in_k.
        have H_neq: k <> n by auto.
        have H_nin: ~ In n ns by auto.
        apply: IH => //.
        rewrite {2}/level_fold /= in H_ins'.
        rewrite (@fold_left_level_fold_eq Tree_TreeMsg) in H_ins'.
        by rewrite collate_not_in_rest //= in H_ins'; last by move => H_neq'; break_or_hyp.
      case (in_dec Msg_eq_dec New (net0.(odnwPackets) n' n)) => H_in; last first.
        apply adjacent_to_symmetric in H_adj.
        exact: (Tree_adjacent_to_no_incoming_new_n_adjacent H_step1 H9 H11 H1 H0 H_adj H14 H_in).
      have H_bef := Tree_in_before_all_new_level H_step1 _ H9 H11 _ H1 lvo'.
      contradict H13.
      rewrite /level_adjacent NSet.fold_spec /flip /=.
      elim: NSet.elements => //=.
        move => H_hd.
        destruct (odnwPackets net0 n' n) => //.
        simpl in *.
        find_injection.
        case: H_in => H_in //.
        case: H_bef => H_bef //.
        by break_and.
      move => k ns IH.
      rewrite {2}/level_fold /= (@fold_left_level_fold_eq Tree_TreeMsg) /=.
      case (name_eq_dec n k) => H_dec_nk; last first.
        rewrite collate_not_in_rest //=.
        move => H_neq.
        by break_or_hyp.
      subst_max.
      rewrite collate_app /=.
      rewrite_update2.
      move: IH.
      set l := fold_left _ _ _.
      have H_in_in := (@collate_in_in _ _ name_eq_dec l n' _ _ _ _ H_in).
      move: H_in_in.
      set ls := collate _ _ _ _ _ _.
      by destruct ls.
    rewrite collate_neq // in H13.
    by eauto.
- move => n H_n H_f n' H_n' lvo'.
  have H_neq: h <> n by auto.
  have H_in: ~ In n failed0 by auto.
  case (name_eq_dec h n') => H_dec.
    subst_max.
    case (adjacent_to_dec n' n) => H_adj; last by rewrite collate_map2snd_not_related; eauto.
    have H_nd := @ordered_dynamic_nodes_no_dup _ _ _ _ Tree_FailMsgParams _ _ _ H_step1.
    rewrite collate_map2snd_not_in_related //.
    move => H_hd.
    apply: (IHH_step1 _ _ _ _ _ lvo') => //.
    by destruct (odnwPackets net0 n' n).
  rewrite collate_neq //.
  by eauto.
Qed.

(* bfs_net_ok_notins_levels_bot *)
Lemma Tree_notins_levels_bot :
  forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed ->
  forall d, net.(odnwState) n = Some d ->
  forall n', ~ NSet.In n' d.(adjacent) ->
  NMap.find n' d.(levels) = None.
Proof.
move => net failed tr H_step.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 1 3.
remember step_ordered_dynamic_failure_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H
end; simpl in *.
- move => n H_n H_f d H_d n' H_ins.
  break_or_hyp; rewrite_update; first find_injection; simpl in *.
  * apply NMapFacts.not_find_in_iff.  
    by NMapFacts.map_iff.
  * by eauto.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=; simpl in *; update_destruct_max_simplify;
    repeat find_rewrite; try find_injection; repeat find_rewrite; try by eauto.
  * have H_emp :=  (Tree_root_levels_empty H_step1) _ H9 H11 H4 _ H2.
    repeat find_rewrite.
    apply NMapFacts.not_find_in_iff.
    by NMapFacts.map_iff.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      apply NMapFacts.not_find_in_iff.
      NMapFacts.map_iff.
      move => H_and.
      by break_and.
    apply NMapFacts.not_find_in_iff.
    NMapFacts.map_iff.
    move => H_and.
    break_and.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H14.
      by auto with set.
    have IH := IHH_step1 _ H10 H12 _ H2 _ H_ins.    
    by apply NMapFacts.not_find_in_iff in IH.
  * case (name_eq_dec from n') => H_dec.
      subst_max.
      apply NMapFacts.not_find_in_iff.
      NMapFacts.map_iff.
      move => H_or.
      by break_and.
    apply NMapFacts.not_find_in_iff.
    NMapFacts.map_iff.
    move => H_and.
    break_and.
    have H_ins: ~ NSet.In n' d.(adjacent).
      move => H_ins.
      case: H14.
      by auto with set.
    have IH := IHH_step1 _ H1 H0 _ H2 _ H_ins.
    by apply NMapFacts.not_find_in_iff in IH.
  * case (in_dec name_eq_dec from (odnwNodes net0)) => H_in; last by rewrite (@ordered_dynamic_no_outgoing_uninitialized _ _ _ _ Tree_FailMsgParams _ _ _ H_step1) in H3.
    have H_hd := Tree_level_head_in_adjacent H_step1 _ H1 H0 from H_in.
Admitted.

(* bfs_net_ok_root_status_in_queue *)
Lemma Tree_root_incoming_level_0 :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed -> 
    root n ->
    forall n' lvo', In (Level lvo') (net.(odnwPackets) n n') ->
    lvo' = Some 0.
Proof.
Admitted.

Lemma Tree_root_broadcast_false :
    forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
   root n ->
   forall d, net.(odnwState) n = Some d ->
   d.(broadcast) = false.
Proof.
Admitted.

(* bfs_net_ok_notin_adj_find_none *)
Lemma Tree_notin_adjacent_find_none :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->
    ~ NSet.In n' d.(adjacent) ->
    NMap.find n d'.(levels) = None.
Proof.
Admitted.

(* bfs_net_ok_root_have_level *)
Lemma Tree_root_have_level :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->
    root n ->
    NSet.In n' d.(adjacent) ->
    (count_occ msg_eq_dec (net.(odnwPackets) n n') (Level (Some 0)) = 1 /\ NMap.find n d'.(levels) = None) \/
    (~ In (Level (Some 0)) (net.(odnwPackets) n n') /\ NMap.find n d'.(levels) = Some 0).
Proof.
Admitted.

Corollary Tree_root_have_level_incoming :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->
    root n ->
    NSet.In n' d.(adjacent) ->
    In (Level (Some 0)) (net.(odnwPackets) n n') \/ NMap.find n d'.(levels) = Some 0.
Proof.
Admitted.

(* nonroot_have_level *)
Lemma Tree_nonroot_have_level : 
 forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall n', In n' net.(odnwNodes) -> ~ In n' failed ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net.(odnwState) n' = Some d' ->
    ~ root n ->
    ~ root n' ->
    NSet.In n' d.(adjacent) ->
    forall lv', level d.(adjacent) d.(levels) = Some lv' ->
    d.(broadcast) = true \/ 
    (In (Level (Some lv')) (net.(odnwPackets) n n') /\ (forall lvo5, lvo5 <> Some lv' -> In (Level lvo5) (net.(odnwPackets) n n') -> before (Level lvo5) (Level (Some lv')) (net.(odnwPackets) n n'))) \/
    (NMap.find n d'.(levels) = Some lv' /\ forall lvo5, ~ In (Level lvo5) (net.(odnwPackets) n n')).
Proof.
Admitted.

Lemma Tree_level_gt_zero : 
 forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall d, net.(odnwState) n = Some d ->
   forall lv', level d.(adjacent) d.(levels) = Some lv' ->
   lv' > 0.
Proof.
Admitted.

Lemma Tree_levels_some_in_adj :
 forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall d, net.(odnwState) n = Some d ->
   forall n' lv', NMap.find n' d.(levels) = Some lv' ->
   NSet.In n' d.(adjacent).
Proof.
Admitted.

(* status_0_in_queue_then_root *)
Lemma Tree_level_0_incoming_then_root : 
   forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n', In (Level (Some 0)) (net.(odnwPackets) n' n) ->
   root n'.
Proof.
Admitted.

Lemma Tree_find_level_0_then_root :
   forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall d, net.(odnwState) n = Some d ->
   forall n', NMap.find n' d.(levels) = Some 0 ->
   root n'.
Proof.
Admitted.

End TreeCorrect.
