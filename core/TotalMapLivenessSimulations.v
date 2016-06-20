Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import LabeledNet.
Require Import StructTact.Util.

Require Import TotalMapSimulations.
Require Import infseq.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class LabeledMultiParamsLabelTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1) :=
  {    
    tot_map_label : @label B0 P0 -> @label B1 P1
  }.

Section LabeledTotalMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.

Definition tot_mapped_lb_net_handlers_label me src m st :=
  let '(lb, out, st', ps) := lb_net_handlers me src m st in tot_map_label lb.

Definition tot_mapped_lb_input_handlers_label me inp st :=
  let '(lb, out, st', ps) := lb_input_handlers me inp st in tot_map_label lb.

End LabeledTotalMapDefs.

Class LabeledMultiParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1)
  (B : BaseParamsTotalMap B0 B1) 
  (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (P : MultiParamsMsgTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1))
  (L : LabeledMultiParamsLabelTotalMap P0 P1) :=
  {
    tot_lb_net_handlers_eq : forall me src m st out st' ps lb, 
      lb_net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) = (lb, out, st', ps)  ->
      tot_mapped_lb_net_handlers_label me src m st = lb ;
    tot_lb_input_handlers_eq : forall me inp st out st' ps lb, 
      lb_input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st) = (lb, out, st', ps) ->
      tot_mapped_lb_input_handlers_label me inp st = lb ;
    tot_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent
  }.

Section TotalMapLivenessSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsTotalMapCongruency base_map name_map msg_map label_map}.

Theorem lb_step_f_tot_mapped_simulation_1 :
  forall net net' failed failed' lb tr,
    @lb_step_f _ labeled_multi_fst (failed, net) lb (failed', net') tr ->
    @lb_step_f _ labeled_multi_snd (map tot_map_name failed, tot_map_net net) (tot_map_label lb) (map tot_map_name failed', tot_map_net net') (map tot_map_trace_occ tr).
Proof.
move => net net' failed failed' lb tr H_step.
invcs H_step => //=.
- have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by destruct p.
  apply: (@LSF_deliver _ _ _ _ _ _ (map tot_map_packet xs) (map tot_map_packet ys) (map tot_map_output out) (tot_map_data d) (@tot_map_name_msgs _ _ _ _ _ msg_map l)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * destruct p.
    simpl in *.
    exact: not_in_failed_not_in.
  * destruct p.
    simpl in *.
    rewrite tot_map_name_inv_inverse.
    have H_q := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst).
    rewrite /tot_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_net_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_net_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * rewrite /tot_map_net /= 2!map_app -tot_map_update_packet_eq.
    destruct p.
    by rewrite tot_map_packet_map_eq.
- apply: (@LSF_input _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /tot_map_net /= tot_map_name_inv_inverse.
    have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= /unlabeled_input_handlers in H_q.
    repeat break_let.
    repeat tuple_inversion.
    have H_q' := @tot_lb_input_handlers_eq _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ Heqp1.
    rewrite /tot_mapped_lb_input_handlers_label in H_q'.
    repeat break_let.
    by repeat tuple_inversion.
  * by rewrite /tot_map_net /= map_app tot_map_packet_map_eq -tot_map_update_eq.
- rewrite tot_lb_label_silent_fst_snd.
  exact: LSF_stutter.
Qed.

Definition tot_map_event_state e :=
{| evt_r_a := (map tot_map_name (fst e.(evt_r_a)), tot_map_net (snd e.(evt_r_a))) ;
   evt_r_l := tot_map_label e.(evt_r_l) |}.

Lemma tot_map_event_state_Map_unfold : forall s,
 Cons (tot_map_event_state (hd s)) (Map tot_map_event_state (tl s)) = Map tot_map_event_state s.
Proof.
by move => s; rewrite -Map_Cons /= -{3}(recons s).
Qed.

Lemma prod_fst_snd_eq : 
  forall A B (ab : A * B),
    ab = (fst ab, snd ab).
Proof.
move => A B ab.
by destruct ab.
Qed.
  
Lemma lb_step_execution_lb_step_f_tot_map_infseq : forall s,
  lb_step_execution lb_step_f s ->
  lb_step_execution lb_step_f (Map tot_map_event_state s).
Proof.
cofix c.
move => s H_exec.
rewrite -tot_map_event_state_Map_unfold {1}/tot_map_event_state /=.
inversion H_exec; subst => /=.
rewrite -tot_map_event_state_Map_unfold /= /tot_map_event_state /=.
apply: (@Cons_lb_step_exec _ _ _ _ _ _ _ _ (map tot_map_trace_occ tr)) => /=.
- apply: lb_step_f_tot_mapped_simulation_1.
  by rewrite -2!prod_fst_snd_eq.
- set e0 := {| evt_r_a := _ ; evt_r_l := _  |}.
  have ->: e0 = tot_map_event_state e' by [].
  pose s' := Cons e' s0.
  rewrite (tot_map_event_state_Map_unfold s').
  exact: c.
Qed.

Lemma tot_map_label_event_state_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (Map tot_map_event_state s).
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
    inf_often (now (occurred (tot_map_label l))) (Map tot_map_event_state s) ->
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

Definition tot_map_event_state_trace e :=
{| evt_tr_r_a := (map tot_map_name (fst e.(evt_tr_r_a)), tot_map_net (snd e.(evt_tr_r_a))) ;
   evt_tr_r_l := tot_map_label e.(evt_tr_r_l) ;
   evt_tr_r_trace := map tot_map_trace_occ e.(evt_tr_r_trace) |}.

Lemma tot_map_event_state_trace_Map_unfold : forall s,
 Cons (tot_map_event_state_trace (hd s)) (Map tot_map_event_state_trace (tl s)) = Map tot_map_event_state_trace s.
Proof.
by move => s; rewrite -Map_Cons /= -{3}(recons s).
Qed.

Lemma lb_step_trace_execution_lb_step_f_tot_map_infseq : forall s,
  lb_step_trace_execution lb_step_f s ->
  lb_step_trace_execution lb_step_f (Map tot_map_event_state_trace s).
Proof.
cofix c.
move => s H_exec.
rewrite -tot_map_event_state_trace_Map_unfold {1}/tot_map_event_state_trace /=.
inversion H_exec; subst => /=.
rewrite -tot_map_event_state_trace_Map_unfold /= /tot_map_event_state_trace /=.
apply: (@Cons_lb_step_trace_exec _ _ _ _ _ _ _ _ (map tot_map_trace_occ tr)) => /=.
- apply: lb_step_f_tot_mapped_simulation_1.
  by rewrite -2!prod_fst_snd_eq.
- unfold evt_tr_trace in *.
  simpl in *.
  find_rewrite.
  by rewrite map_app.
- set e0 := {| evt_tr_r_a := _ ; evt_tr_r_l := _ ; evt_tr_r_trace := _ |}.
  have ->: e0 = tot_map_event_state_trace e' by [].
  pose s' := Cons e' s0.
  rewrite (tot_map_event_state_trace_Map_unfold s').
  exact: c.
Qed.

Lemma tot_map_label_event_state_trace_inf_often_occurred :
  forall l s,
    inf_often (now (occurred l)) s ->
    inf_often (now (occurred (tot_map_label l))) (Map tot_map_event_state_trace s).
Proof.
move => l.
apply: always_Map.
apply: eventually_Map.
case => e s.
rewrite /= /occurred /=.
move => H_eq.
by rewrite H_eq.
Qed.

Lemma tot_map_label_event_state_trace_inf_often_occurred_conv :
  forall l s,
    inf_often (now (occurred (tot_map_label l))) (Map tot_map_event_state_trace s) ->
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

Context {fail_fst : FailureParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_snd : FailureParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.

Lemma tot_map_hd_step_f_star_ex_always : 
  forall s, event_step_star_ex step_f step_f_init (hd s) ->
       lb_step_execution lb_step_f s ->
       always (now (event_step_star_ex step_f step_f_init)) (Map tot_map_event_state s).
Proof.
case => e s H_star H_exec.
apply: step_f_star_ex_lb_step_execution.
  rewrite /= /tot_map_event_state /= /event_step_star_ex /=.
  rewrite /= /tot_map_event_state /= /event_step_star_ex /= in H_star.
  break_exists.
  exists (map (@tot_map_trace_occ _ _ _ _ _ name_map) x).
  apply: step_f_tot_mapped_simulation_star_1 => //.
  by rewrite -prod_fst_snd_eq.  
exact: lb_step_execution_lb_step_f_tot_map_infseq.
Qed.

Lemma tot_map_hd_step_f_star_always : 
  forall s, event_step_star step_f step_f_init (hd s) ->
       lb_step_trace_execution lb_step_f s ->
       always (now (event_step_star step_f step_f_init)) (Map tot_map_event_state_trace s).
Proof.
case => e s H_star H_exec.
apply: step_f_star_lb_step_trace_execution.
  rewrite /=.
  rewrite /tot_map_event_state_trace /= /event_step_star /=.
  apply: step_f_tot_mapped_simulation_star_1.
  by rewrite -prod_fst_snd_eq.
exact: lb_step_trace_execution_lb_step_f_tot_map_infseq.
Qed.

End TotalMapLivenessSimulations.
