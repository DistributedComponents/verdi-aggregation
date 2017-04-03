Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.DynamicNetLemmas.

Require Import StructTact.Update.
Require Import StructTact.Update2.
Require Import StructTact.StructTactics.

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

Set Bullet Behavior "Strict Subproofs".

Lemma Tree_in_level_adjacent_or_incoming_new :
  forall net failed tr, 
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
    forall n, ~ In n failed -> In n net.(odnwNodes) ->
     forall n' lvo', In (Level lvo') (net.(odnwPackets) n' n) ->
     In n' net.(odnwNodes) ->
     forall d, net.(odnwState) n = Some d ->
     NSet.In n' d.(adjacent) \/ In New (net.(odnwPackets) n' n).
Proof.
  intros.
  change failed with (fst (failed, net)) in H0.
  change net with (snd (failed, net)) in H1, H2, H3, H4.
  change net with (snd (failed, net)).
  generalize dependent d.
  remember step_ordered_dynamic_failure_init as y in *.
  move: Heqy.
  induction H using refl_trans_1n_trace_n1_ind.
  - intros. simpl. subst.
    match goal with
    | [ H : context[step_ordered_dynamic_failure_init] |- _ ] =>
      invcs H
    end.
  - pose proof H1 as H_mine.
    intros H_init d.
    match goal with
    | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invcs H
    end.
    + destruct (name_eq_dec h n).
      * break_or_hyp => //=; subst.
        intro H_st.
        right.
        find_apply_lem_hyp collate_ls_in_neq_in_before; [|congruence].
        find_eapply_lem_hyp collate_map2snd_in_neq_in_before; [|congruence].
        assert (n' <> n) by admit.
        admit.
      * rewrite update_diff; [|assumption].
        intros.
        copy_eapply_prop_hyp NSet.In failed0; eauto.
        find_copy_eapply_lem_hyp ordered_dynamic_state_not_initialized_not_failed; eauto.
        break_or_hyp.
        -- by eauto.
        -- right.
           apply collate_ls_in_in.
           apply collate_in_in.
           assumption.
        -- break_or_hyp; [congruence | assumption].
        -- eapply_lem_prop_hyp collate_ls_in_neq_in_before @collate_ls => //.
           eapply_lem_prop_hyp collate_map2snd_in_neq_in_before @collate => //.
        -- admit.
    + find_apply_lem_hyp net_handlers_NetHandler.
      net_handler_cases => //=; simpl in *.
      * destruct (name_eq_dec to n), (name_eq_dec from n'); subst.
        -- find_rewrite_lem update_same; find_inversion.
           find_rewrite_lem update2_same; repeat find_reverse_rewrite.
           assert (In (Level lvo') (odnwPackets net0 n' n)).
           {
             repeat find_rewrite.
             auto with datatypes.
           }
           find_apply_hyp_hyp; break_or_hyp.
           ++ exfalso.
              match goal with
              | [ H : refl_trans_1n_trace _ _ (?failed, net0) ?tr |- _ ] =>
                assert (H_step: step_ordered_dynamic_failure_star
                                  step_ordered_dynamic_failure_init
                                  (failed, net0) tr)
                  by auto;
                  pose proof (Tree_in_after_all_fail_level H_step n) as H_after; simpl in H_after
              end.
              assert (before_all (Level lvo') Fail (odnwPackets net0 n' n)) by eauto.
              find_rewrite. simpl in *; break_or_hyp; break_and; auto.
           ++ right.
              repeat find_rewrite.
              rewrite update2_same.
              find_apply_lem_hyp in_inv; break_or_hyp; auto || congruence.
        -- rewrite update2_diff1; [|assumption].
           match goal with
           | [ H: context[ update2 ] |- _ ] =>
             rewrite update2_diff1 in H; [|assumption]
           end.
           find_rewrite_lem update_same; find_inversion.
           assert (NSet.In n' (adjacent d0) \/ In New (odnwPackets net0 n' n)) by auto.
           break_or_hyp.
           ++ left.
              repeat find_rewrite.
              by apply FRC.NSetProps.Dec.F.remove_2.
           ++ by right.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- _ ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- _ ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * admit.
      * destruct (name_eq_dec to n); subst.
        -- find_rewrite_lem update_same; find_inversion.
           admit.
        -- rewrite update2_diff2; [|assumption].
           match goal with
           | [ H: _ |- ?G ] =>
             eapply H; eauto
           end.
           ++ erewrite <- update2_diff2; eauto.
           ++ match goal with
              | [ H: context[ update ] |- _ ] =>
                rewrite update_diff in H; assumption
              end.
      * admit.
    + find_apply_lem_hyp input_handlers_IOHandler.
      io_handler_cases => //=; simpl in *; eauto.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
    + admit.
Admitted.

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
    - tuple_inversion.
      by find_rewrite_lem (Tree_self_channel_empty H_step1).
    - have H_neq: n <> n' by move => H_eq; subst_max.
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

Lemma Tree_level_head_in_adjacent :
  forall net failed tr,
   step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr ->
   forall n, In n net.(odnwNodes) -> ~ In n failed ->
   forall n' lvo', head (net.(odnwPackets) n' n) = Some (Level lvo') ->
   forall d, net.(odnwState) n = Some d ->
   NSet.In n' d.(adjacent).
Proof.
Admitted.

(* bfs_net_ok_notins_levels_bot *)
Lemma Tree_notins_levels_bot :
  forall net failed tr,
  step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
  forall n, In n net.(odnwNodes) -> ~ In n failed ->
  forall d, net.(odnwState) n = Some d ->
  forall n', ~ NSet.In n' d.(adjacent) ->
  NMap.find n' d.(levels) = None.
Proof.
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

(* bfs_net_ok_notin_adj_not_sent_status *)
Lemma Tree_notin_adjacent_not_sent_level :
  forall net failed tr,
    step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> 
    forall n, In n net.(odnwNodes) -> ~ In n failed ->
    forall d, net.(odnwState) n = Some d ->
    forall n', ~ NSet.In n' d.(adjacent) ->
    forall lvo', ~ In (Level lvo') (net.(odnwPackets) n n').
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
