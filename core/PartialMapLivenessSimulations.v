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

Definition pt_map_event e : event _ _ _ := 
((map tot_map_name (fst (a_of_event e)), pt_map_net (snd (a_of_event e))), tot_map_label (l_of_event e), pt_map_trace (tr_of_event e)).

(*
Definition select lb 
 (tr : list (@name _ (@unlabeled_multi_params _ labeled_multi_fst) * (@input base_fst + list (@output base_fst)))) 
 (s : infseq (event (list (@name _ (@unlabeled_multi_params _ labeled_multi_fst)) * 
                     (@network _ (@unlabeled_multi_params _ labeled_multi_fst))) (@label _ labeled_multi_fst) _)) :=
if label_eq_dec (tot_map_label lb) label_silent then tr else tr_of_event (hd s).

CoFixpoint pt_map_infseq s tr :=
match s with
| Cons e s' => Cons (pt_map_event ((a_of_event e), (l_of_event e), tr)) (pt_map_infseq s' (select (l_of_event e) tr s'))
end.

Lemma pt_map_infseq_unfold : forall s tr,
    Cons (pt_map_event (a_of_event (hd s), l_of_event (hd s), tr)) (pt_map_infseq (tl s) (select (l_of_event (hd s)) tr (tl s))) = 
    pt_map_infseq s tr.
Proof.
Admitted.

Lemma lb_step_execution_lb_step_f_pt_map_infeq : forall s,
  lb_step_execution lb_step_f s  ->
  lb_step_execution lb_step_f (pt_map_infseq s (tr_of_event (hd s))).
Proof.
Admitted.
*)

End PartialMapLivenessSimulations.
