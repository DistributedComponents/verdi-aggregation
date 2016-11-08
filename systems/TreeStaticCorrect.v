Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.PartialExtendedMapSimulations.

Require Import NameAdjacency.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import Sumbool.
Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import FMapInterface.
Require Import Sorting.Permutation.

Require Import FailureRecorderStatic.
Require Import FailureRecorderStaticCorrect.
Require Import TreeAux.
Require Import TreeStatic.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Set Implicit Arguments.

Module TreeCorrect (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC)
 (Import RNT : RootNameType NT) 
 (Import ANT : AdjacentNameType NT) (Import A : Adjacency NT NOT NSet ANT)
 (Import TA : TAux NT NOT NSet NOTC NMap).

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Module FRC := FailureRecorderCorrect NT NOT NSet ANT A.
Module FR := FRC.FR.

Module TR := Tree NT NOT NSet NOTC NMap RNT ANT A TA.
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
    pt_map_msg := fun m => match m with Fail => Some FR.Fail | _ => None end ;
  }.

Instance Tree_FailureRecorder_multi_params_pt_map_congruency : MultiParamsPartialMapCongruency Tree_FailureRecorder_base_params_pt_map Tree_FailureRecorder_name_tot_map Tree_FailureRecorder_multi_params_pt_map :=
  {
    pt_init_handlers_eq := _ ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
Proof.
- by move => n; rewrite /= /InitData /=; break_if.
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
  io_handler_cases; simpl in *; try congruence.
    rewrite /level_adjacent NSet.fold_spec /flip /=.
    elim: NSet.elements => //=.
    move => n l IH.
    rewrite /flip /= /level_fold.
    rewrite (@fold_left_level_fold_eq Tree_TreeMsg).
    by rewrite pt_map_name_msgs_app_distr /= IH.
  rewrite /level_adjacent NSet.fold_spec /flip /=.
  elim: NSet.elements => //=.
  move => n l IH.
  rewrite /flip /= /level_fold.
  rewrite (@fold_left_level_fold_eq Tree_TreeMsg).
  by rewrite pt_map_name_msgs_app_distr /= IH.
Qed.

Instance Tree_FailureRecorder_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency Tree_FailMsgParams FR.FailureRecorder_FailMsgParams Tree_FailureRecorder_multi_params_pt_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance Tree_FailureRecorder_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency Tree_NameOverlayParams FR.FailureRecorder_NameOverlayParams Tree_FailureRecorder_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem Tree_Failed_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_ordered_failure_star _ _ _ Tree_FailMsgParams step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ _ FR.FailureRecorder_FailMsgParams step_ordered_failure_init (failed, pt_map_onet net) (pt_map_traces tr).
Proof.
move => onet failed tr H_st.
apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Lemma Tree_node_not_adjacent_self : 
forall net failed tr n, 
 step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr ->
 ~ In n failed ->
 ~ NSet.In n (onwState net n).(adjacent).
Proof.
move => onet failed tr n H_st H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact: FRC.Failure_node_not_adjacent_self H_st' H_in_f.
Qed.

Lemma Tree_not_failed_no_fail :
forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_not_failed_no_fail H_st' n n' H_in_f.
move => H_in.
case: H_inv'.
rewrite /= /id /=.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Tree_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact (FRC.Failure_in_adj_adjacent_to H_st' n H_in_f H_ins).
Qed.

Lemma Tree_pt_map_msg_injective : 
  forall m0 m1 m2 : msg,
   pt_map_msg m0 = Some m2 -> pt_map_msg m1 = Some m2 -> m0 = m1.
Proof.
by case => [|lvo]; case => [|lvo'] H_eq.
Qed.

Lemma Tree_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_in_adj_or_incoming_fail H_st' _ H_in_f H_ins.
case: H_inv' => H_inv'; first by left.
right.
move: H_inv' => [H_in_f' H_inv'].
split => //.
move: H_inv'.
apply: in_pt_map_msgs_in_msg; last exact: pt_fail_msg_fst_snd.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_le_one_fail : 
  forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_le_one_fail H_st' _ n' H_in_f.
rewrite /= /id /= in H_inv'.
move: H_inv'.
set c1 := count_occ _ _ _.
set c2 := count_occ _ _ _.
suff H_suff: c1 = c2 by rewrite -H_suff.
rewrite /c1 /c2 {c1 c2}.
apply: count_occ_pt_map_msgs_eq => //.
exact: Tree_pt_map_msg_injective.
Qed.

Lemma Tree_adjacent_to_in_adj :
forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_in_f' H_adj.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact: (FRC.Failure_adjacent_to_in_adj H_st' H_in_f H_in_f' H_adj).
Qed.

Lemma Tree_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_in_queue_fail_then_adjacent H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_ins.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Tree_first_fail_in_adj : 
  forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FRC.Failure_first_fail_in_adj H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Tree_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Tree_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

Ltac induct_step :=
  match goal with
  | H : step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) _ _ _ |- _ =>
    prep_induction H;
    induction H using refl_trans_1n_trace_n1_ind; intros; subst;
    [|match goal with
      | _ : step_ordered_failure ?s _ _,
            IH : context [?s = _] |- _ =>
        destruct s as [failed' net'];
        specialize (IH net' failed')
      end]
  end.

(* bfs_net_ok_root_levels_empty *)
Lemma Tree_root_levels_empty :
  forall net failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
  forall n, ~ In n failed -> 
  root n ->
  (net.(onwState) n).(levels) = NMap.empty lv.
Proof.
  intros. induct_step.
  - unfold step_ordered_failure_init in *.
    find_inversion. simpl.
    unfold InitData.
    now break_match.
  - match goal with
    | [ H : step_ordered_failure _ _ _ |- _ ] => invc H
    end; simpl.
    + find_apply_lem_hyp net_handlers_NetHandler.
      net_handler_cases; auto; simpl in *;
        update_destruct_max_simplify; repeat find_rewrite; auto.
    + find_apply_lem_hyp input_handlers_IOHandler.
      io_handler_cases; simpl in *; auto;
        update_destruct_max_simplify; repeat find_rewrite; auto.
    + intros. simpl in *.
      eauto.
Qed.

(* bfs_net_ok_root_levels_bot *)
Lemma Tree_root_levels_bot : 
forall net failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
  forall n, ~ In n failed -> root n ->
  forall n', NMap.find n' (net.(onwState) n).(levels) = None.
Proof.
    intros. induct_step.
  - unfold step_ordered_failure_init in *.
    find_inversion. simpl.
    unfold InitData.
    apply NMapFacts.not_find_in_iff.
    intro.
    break_if; simpl in *; eapply NMapFacts.empty_in_iff; eauto.
  - match goal with
    | [ H : step_ordered_failure _ _ _ |- _ ] => invc H
    end; simpl.
    + find_apply_lem_hyp net_handlers_NetHandler.
      net_handler_cases; auto; simpl in *;
        update_destruct_max_simplify; repeat find_rewrite; auto.
    + find_apply_lem_hyp input_handlers_IOHandler.
      io_handler_cases; simpl in *; auto;
        update_destruct_max_simplify; repeat find_rewrite; auto.
    + intros. simpl in *.
      eauto.
Qed.

(* in_after_all_fail_status *)
Lemma Tree_in_after_all_fail_level : 
forall onet failed tr,
 step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr ->
 forall (n : name), ~ In n failed ->
 forall (n' : name) lvo', before_all (Level lvo') Fail (onet.(onwPackets) n' n).
Proof.
  intros. induct_step.
  - unfold step_ordered_failure_init in *.
    find_inversion. simpl. auto.
  - match goal with
    | [ H : step_ordered_failure _ _ _ |- _ ] => invc H
    end; simpl.
    + find_apply_lem_hyp net_handlers_NetHandler.
      net_handler_cases; auto; simpl in *;
        update2_destruct_max_simplify; repeat find_rewrite;
          auto; tuple_inversion;
            try solve [
                  match goal with
                  | |- before_all ?x ?y _ =>
                    assert (x <> y) by congruence
                  end;
                  match goal with
                  | H : In ?n _ -> False,
                    IH : context [ In _ _ ] |- _ =>
                    specialize (IH n); intuition
                  end;
                  match goal with
                  | H : onwPackets _ ?n _ = _,
                    IH : context [ onwPackets _ _ _ ] |- _ =>
                    specialize (IH n); find_rewrite
                  end;
                  eauto using before_all_not_in, before_all_head_not_in];
      admit.
    + admit.
    + admit.
Admitted.

(* in_queue_status_then_new *)
Lemma Tree_level_msg_dst_adjacent_src : 
  forall onet failed tr, 
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, onet) tr ->
    forall n, ~ In n failed ->
     forall n' lvo', In (Level lvo') (onet.(onwPackets) n' n) ->
     NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
Admitted.

(* bfs_net_ok_notins_levels_bot *)
Lemma Tree_notins_levels_bot :
  forall net failed tr,
  step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
  forall n, ~ In n failed ->
  forall n', ~ NSet.In n' (net.(onwState) n).(adjacent) ->
  NMap.find n' (net.(onwState) n).(levels) = None.
Proof.
Admitted.

(* bfs_net_ok_root_status_in_queue *)
Lemma Tree_root_incoming_level_0 :
  forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed -> 
    root n ->
    forall n' lvo', In (Level lvo') (net.(onwPackets) n n') ->
    lvo' = Some 0.
Proof.
Admitted.

Lemma Tree_root_broadcast_false :
    forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
   root n ->
   (net.(onwState) n).(broadcast) = false.
Proof.
Admitted.

(* bfs_net_ok_notin_adj_not_sent_status *)
Lemma Tree_notin_adjacent_not_sent_level :
  forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
    forall n', ~ NSet.In n' (net.(onwState) n).(adjacent) ->
    forall lvo', ~ In (Level lvo') (net.(onwPackets) n n').
Proof.
Admitted.

(* bfs_net_ok_notin_adj_find_none *)
Lemma Tree_notin_adjacent_find_none :
  forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
    forall n', ~ In n' failed ->
    ~ NSet.In n' (net.(onwState) n).(adjacent) ->
    NMap.find n (net.(onwState) n').(levels) = None.
Proof.
Admitted.

(* bfs_net_ok_root_have_level *)
Lemma Tree_root_have_level :
  forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
    forall n', ~ In n' failed ->
    root n ->
    NSet.In n' (net.(onwState) n).(adjacent) ->
    (~ In (Level (Some 0)) (net.(onwPackets) n n') /\ 
     NMap.find n (net.(onwState) n').(levels) = None /\ 
     (net.(onwState) n).(broadcast) = true) \/ 
    (count_occ msg_eq_dec (net.(onwPackets) n n') (Level (Some 0)) = 1 /\ 
     NMap.find n (net.(onwState) n').(levels) = None /\ 
     (net.(onwState) n).(broadcast) = false) \/
    (~ In (Level (Some 0)) (net.(onwPackets) n n') /\ 
     NMap.find n (net.(onwState) n').(levels) = Some 0 /\ 
     (net.(onwState) n).(broadcast) = false).
Proof.
Admitted.

(* nonroot_have_level *)
Lemma Tree_nonroot_have_level : 
 forall net failed tr,
    step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->    
    forall n', ~ In n' failed ->
    ~ root n ->
    ~ root n' ->
    NSet.In n' (net.(onwState) n).(adjacent) ->
    forall lv', level (net.(onwState) n).(adjacent) (net.(onwState) n).(levels) = Some lv' ->
    (net.(onwState) n).(broadcast) = true \/
    (In (Level (Some lv')) (net.(onwPackets) n n')
     /\ (forall lvo5, lvo5 <> Some lv' -> In (Level lvo5) (net.(onwPackets) n n') -> before (Level lvo5) (Level (Some lv')) (net.(onwPackets) n n'))) \/
    (NMap.find n (net.(onwState) n').(levels) = Some lv' /\ forall lvo5, ~ In (Level lvo5) (net.(onwPackets) n n')).
Proof.
Admitted.

Lemma Tree_level_gt_zero : 
 forall net failed tr,
   step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall lv', level (net.(onwState) n).(adjacent) (net.(onwState) n).(levels) = Some lv' ->
   lv' > 0.
Proof.
Admitted.

Lemma Tree_levels_some_in_adj :
 forall net failed tr,
   step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n' lv', NMap.find n' (net.(onwState) n).(levels) = Some lv' ->
   NSet.In n' (net.(onwState) n).(adjacent).
Proof.
Admitted.

(* status_0_in_queue_then_root *)
Lemma Tree_level_0_incoming_then_root : 
   forall net failed tr,
   step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n', In (Level (Some 0)) (net.(onwPackets) n' n) ->
   root n'.
Proof.
Admitted.

Lemma Tree_find_level_0_then_root :
   forall net failed tr,
   step_ordered_failure_star (fail_msg_params := Tree_FailMsgParams) step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n', NMap.find n' (net.(onwState) n).(levels) = Some 0 ->
   root n'.
Proof.
Admitted.

End TreeCorrect.
