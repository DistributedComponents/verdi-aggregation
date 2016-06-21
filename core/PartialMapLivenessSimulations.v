Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import LabeledNet.
Require Import StructTact.Util.
Require Import FunctionalExtensionality.

Require Import TotalMapSimulations.
Require Import PartialMapSimulations.
Require Import TotalMapLivenessSimulations.
Require Import infseq.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Set Implicit Arguments.

Class LabeledMultiParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1)
  (B : BaseParamsPartialMap B0 B1) 
  (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (P : MultiParamsMsgPartialMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (L : LabeledMultiParamsLabelTotalMap P0 P1) :=
  {
    pt_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent ;
    pt_lb_net_handlers_some : forall me src m st m' out st' ps lb,
      pt_map_msg m = Some m' ->
      lb_net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) = (lb, out, st', ps) ->
      lb <> label_silent /\ tot_mapped_lb_net_handlers_label me src m st = lb ;
    pt_lb_net_handlers_none : forall me src m st,
      pt_map_msg m = None ->
      tot_mapped_lb_net_handlers_label me src m st = label_silent ;
    pt_lb_input_handlers_some : forall me inp st inp' out st' ps lb,
      pt_map_input inp = Some inp' ->
      lb_input_handlers (tot_map_name me) inp' (pt_map_data st) = (lb, out, st', ps) ->
      lb <> label_silent /\ tot_mapped_lb_input_handlers_label me inp st = lb ;
    pt_lb_input_handlers_none : forall me inp st,
      pt_map_input inp = None ->
      tot_mapped_lb_input_handlers_label me inp st = label_silent
  }.

Section PartialMapLivenessSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgPartialMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsPartialMapCongruency base_map name_map msg_map label_map}.

Theorem lb_step_f_pt_mapped_simulation_1_non_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb <> label_silent ->
    @lb_step_f _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_f _ labeled_multi_snd (map tot_map_name failed, pt_map_net net) (tot_map_label lb) (map tot_map_name failed', pt_map_net net') (pt_map_trace tr).
Proof.
move => net net' failed failed' lb tr H_neq H_step.
have H_neq': lb <> label_silent.
  rewrite -pt_lb_label_silent_fst_snd in H_neq.
  move => H_eq.
  by rewrite H_eq in H_neq.
invcs H_step => //=.
- case H_m: (pt_map_packet p) => [p'|]; last first.
    destruct p.
    simpl in *.
    break_match => //.
    have H_q := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr pDst pSrc _ (nwState net pDst) Heqo.
    rewrite /tot_mapped_lb_net_handlers_label in H_q.
    repeat break_let.
    by tuple_inversion.
  have H_eq_n: tot_map_name (pDst p) = pDst p'.
    destruct p.
    simpl in *.
    break_match => //.
    by find_injection.
  rewrite H_eq_n.
  apply (@LSF_deliver _ _ _ _ _ _ (pt_map_packets xs) (pt_map_packets ys) (pt_map_outputs out) (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * rewrite /pt_map_net /=.
    find_rewrite.
    by rewrite pt_map_packets_app_distr /= H_m.
  * rewrite -H_eq_n.
    exact: not_in_failed_not_in.
  * rewrite /pt_map_net /= -{2}H_eq_n tot_map_name_inv_inverse.
    destruct p, p'.
    simpl in *.
    break_match => //.
    find_injection.
    clean.
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) _ Heqo.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ Heqo Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    break_and.
    by repeat tuple_inversion.
  * rewrite /pt_map_net /= 2!pt_map_packets_app_distr.
    by rewrite (pt_map_packet_map_eq_some _ _ H_m) (pt_map_update_eq_some _ _ _ H_m).
- case H_i: pt_map_input => [inp'|]; last first.
    have H_q := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (nwState net h) H_i.
    rewrite /tot_mapped_lb_input_handlers_label /= in H_q.
    repeat break_let.
    by tuple_inversion.
  apply (@LSF_input _ _ _ _ _ _ _ _ (pt_map_data d) (@pt_map_name_msgs _ _ _ _ _ msg_map l)).
  * exact: not_in_failed_not_in.
  * have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    repeat tuple_inversion.
    by rewrite /pt_map_net /= tot_map_name_inv_inverse.
  * rewrite /pt_map_net /=.
    rewrite pt_map_packets_app_distr pt_map_packet_map_eq.
    by rewrite -pt_map_update_eq.
Qed.

Theorem lb_step_f_pt_mapped_simulation_1_silent :
  forall net net' failed failed' lb tr,
    tot_map_label lb = label_silent ->
    @lb_step_f _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_f _ labeled_multi_snd (map tot_map_name failed, pt_map_net net) label_silent (map tot_map_name failed', pt_map_net net') [].
Proof.
move => net net' failed failed' lb tr H_eq H_step.
invcs H_step => //=.
- case H_m: (pt_map_packet p) => [p'|].
    destruct p, p'.
    simpl in *.
    break_match => //.
    find_injection.
    have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) _ Heqo.
    rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ Heqo Heqp1.
    break_and.
    unfold tot_mapped_lb_net_handlers_label in *.
    repeat break_let.
    by repeat tuple_inversion.
  destruct p.
  simpl in *.
  break_match => //.
  have H_q := @pt_net_handlers_none _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) out d l Heqo.
  rewrite /net_handlers /= /unlabeled_net_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr pDst pSrc _ (nwState net pDst) Heqo.
  rewrite /tot_mapped_lb_net_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_net /=.
  rewrite pt_map_packets_app_distr.
  rewrite pt_map_name_msgs_empty_eq //=.
  rewrite H3.
  rewrite pt_map_packets_app_distr /=.
  repeat break_match => //.
  rewrite -pt_map_packets_app_distr.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite H e.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  exact: LSF_stutter.
- case H_i: (pt_map_input inp) => [inp'|].
    have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) _ H_i.
    rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
    break_and.
    unfold tot_mapped_lb_input_handlers_label in *.
    repeat break_let.
    by tuple_inversion.
  have H_q := @pt_input_handlers_none _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) out d l H_i.
  rewrite /input_handlers /= /unlabeled_input_handlers in H_q.
  repeat break_let.
  repeat tuple_inversion.
  concludes.
  break_and.
  have H_q' := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (nwState net h) H_i.
  rewrite /tot_mapped_lb_input_handlers_label in H_q'.
  repeat break_let.
  repeat tuple_inversion.
  rewrite /pt_map_net /=.
  rewrite pt_map_packets_app_distr.
  rewrite pt_map_name_msgs_empty_eq //=.
  set s1 := fun _ => _.
  set s2 := fun _ => _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2.
    apply functional_extensionality => n.
    rewrite /update.
    by break_if; first by rewrite H e.
  rewrite -H_eq_s /s1 {s1 s2 H_eq_s}.
  exact: LSF_stutter.
- exact: LSF_stutter.
Qed.

Definition pt_map_event_state e :=
{| evt_r_a := (map tot_map_name (fst e.(evt_r_a)), pt_map_net (snd e.(evt_r_a))) ;
   evt_r_l := tot_map_label e.(evt_r_l) |}.

Lemma pt_map_event_state_Map_unfold : forall s,
 Cons (pt_map_event_state (hd s)) (Map pt_map_event_state (tl s)) = Map pt_map_event_state s.
Proof.
by move => s; rewrite -Map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_execution_lb_step_f_pt_map_infseq : forall s,
  lb_step_state_execution lb_step_f s ->
  lb_step_state_execution lb_step_f (Map pt_map_event_state s).
Proof.
cofix c.
move => s H_exec.
rewrite -pt_map_event_state_Map_unfold {1}/pt_map_event_state /=.
inversion H_exec; subst => /=.
rewrite -pt_map_event_state_Map_unfold /= /pt_map_event_state /=.
case (label_eq_dec (tot_map_label (evt_l e)) label_silent) => H_eq.
  apply: (@Cons_lb_step_exec _ _ _ _ _ _ _ _ []) => /=.
    rewrite H_eq.
    move: H_eq H.
    rewrite /=.
    destruct e, e'.
    destruct evt_r_a, evt_r_a0.
    simpl in *.  
    exact: lb_step_f_pt_mapped_simulation_1_silent.  
  pose s' := Cons e' s0.
  rewrite (pt_map_event_state_Map_unfold s').
  exact: c.
apply: (@Cons_lb_step_exec _ _ _ _ _ _ _ _ (pt_map_trace tr)) => /=.
  move: H_eq H.
  destruct e, e'.
  destruct evt_r_a, evt_r_a0.
  simpl in *.
  exact: lb_step_f_pt_mapped_simulation_1_non_silent.  
pose s' := Cons e' s0.
rewrite (pt_map_event_state_Map_unfold s').
exact: c.
Qed.

Lemma tot_map_label_event_state_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (Map pt_map_event_state s).
Proof.
move => l.
apply: always_Map.
apply: eventually_Map.
case => e s.
rewrite /= /occurred /evt_l /=.
move => H_eq.
by rewrite H_eq.
Qed.

Hypothesis tot_map_label_injective : 
  forall l l', tot_map_label l = tot_map_label l' -> l = l'.

Lemma tot_map_label_event_state_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (Map pt_map_event_state s) ->
    inf_often (now (occurred l)) s.
Proof.
move => l.
apply: always_Map_conv.
apply: eventually_Map_conv => //.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- rewrite /extensional /=.
  case => e s1.
  case => e' s2.
  move => H_eq.
  by inversion H_eq; subst_max.
- case => e s.
  rewrite /= /occurred /=.
  move => H_eq.
  exact: tot_map_label_injective.
Qed.

(*
Context {fail_fst : FailureParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_snd : FailureParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_map_congr : FailureParamsPartialMapCongruency fail_fst fail_snd base_map}.

Lemma pt_map_hd_step_f_star_ex_always : 
  forall s, event_step_star_ex step_f step_f_init (hd s) ->
       lb_step_execution lb_step_f s ->
       always (now (event_step_star_ex step_f step_f_init)) (Map pt_map_event_state s).
Proof.
case => e s H_star H_exec.
apply: step_f_star_ex_lb_step_execution.
  rewrite /= /tot_map_event_state /= /event_step_star_ex /=.
  rewrite /= /tot_map_event_state /= /event_step_star_ex /= in H_star.
  break_exists.
  exists ((@pt_map_trace _ _ _ _ _ name_map) x).
  apply: step_f_pt_mapped_simulation_star_1 => //.
  by rewrite -prod_fst_snd_eq.  
exact: lb_step_execution_lb_step_f_tot_map_infseq.
Qed.
*)

End PartialMapLivenessSimulations.
