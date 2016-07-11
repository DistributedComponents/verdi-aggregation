Require Import Verdi.
Require Import InfSeqExt.infseq.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class LabeledMultiParams (P : BaseParams) :=
  {
    lb_name : Type ;
    lb_msg : Type ;
    lb_msg_eq_dec : forall x y : lb_msg, {x = y} + {x <> y} ;
    lb_name_eq_dec : forall x y : lb_name, {x = y} + {x <> y} ;
    lb_nodes : list lb_name ;
    lb_all_names_nodes : forall n, In n lb_nodes ;
    lb_no_dup_nodes : NoDup lb_nodes ;
    label : Type ;
    label_silent : label ;
    lb_init_handlers : lb_name -> data ;
    lb_net_handlers : lb_name -> lb_name -> lb_msg -> data -> label * (list output) * data * list (lb_name * lb_msg) ;
    lb_input_handlers : lb_name -> input -> data -> label * (list output) * data * list (lb_name * lb_msg)
  }.

Section CustomLabeledParams.

Context {base_params : BaseParams}.
Context {labeled_multi_params : LabeledMultiParams base_params}.

Definition unlabeled_net_handlers me src m st :=
let '(lb, out, st', ps) := lb_net_handlers me src m st in (out, st', ps).

Definition unlabeled_input_handlers me inp st :=
let '(lb, out, st', ps) := lb_input_handlers me inp st in (out, st', ps).

Global Instance unlabeled_multi_params : MultiParams base_params :=
  {
    name := lb_name ;
    msg := lb_msg ;
    msg_eq_dec := lb_msg_eq_dec ;
    name_eq_dec := lb_name_eq_dec ;
    nodes := lb_nodes ;
    all_names_nodes := lb_all_names_nodes ;
    no_dup_nodes := lb_no_dup_nodes ;
    init_handlers := lb_init_handlers;
    net_handlers := unlabeled_net_handlers ;
    input_handlers := unlabeled_input_handlers
  }.

End CustomLabeledParams.

Section DefaultLabeledParams.

Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.

Inductive default_label :=
| DL_recv_msg : name -> name -> msg -> default_label
| DL_recv_input : name -> input -> default_label
| DL_tau : default_label.

Definition default_lb_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (DL_recv_msg me src m, out, st', ps).

Definition default_lb_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (DL_recv_input me inp, out, st', ps).

Global Instance default_labeled_multi_params : LabeledMultiParams base_params :=
  {
    lb_name := name ;
    lb_msg := msg ;
    lb_msg_eq_dec := msg_eq_dec ;
    lb_name_eq_dec := name_eq_dec ;
    lb_nodes := nodes ;
    lb_all_names_nodes := all_names_nodes ;
    lb_no_dup_nodes := no_dup_nodes ;
    label := default_label ;
    label_silent := DL_tau ;
    lb_init_handlers := init_handlers ;
    lb_net_handlers := default_lb_net_handlers ;
    lb_input_handlers := default_lb_input_handlers
  }.

Context {EqDec_eq_input : EqDec_eq input}.

Definition default_label_eq_dec : forall x y : default_label, {x = y} + {x <> y}.
decide equality; auto using name_eq_dec, msg_eq_dec, eq_dec.
Defined.

Global Instance EqDec_eq_default_label : EqDec_eq label := default_label_eq_dec.

End DefaultLabeledParams.

Section Events.
  Variable S : Type.
  Variable A : Type.
  Variable L : Type.
  Variable trace : Type.

  Class event_state := { evt_a : S -> A ; evt_l : S -> L }.
  Class event_state_trace := { evt_st :> event_state ; evt_trace : S -> list trace }.
End Events.

Record event_state_r {A L} := { evt_r_a : A ; evt_r_l : L }.
Instance event_state_event_state_r {A L} : event_state event_state_r A L :=
  {
    evt_a := evt_r_a;
    evt_l := evt_r_l
  }.

Record event_state_trace_r {A L trace} := { evt_tr_r_a : A ; evt_tr_r_l : L ; evt_tr_r_trace : list trace }.
Instance event_state_trace_event_state_trace_r {A L trace} : event_state_trace event_state_trace_r A L trace :=
  {
    evt_st := {| evt_a := evt_tr_r_a ; evt_l := evt_tr_r_l |} ;
    evt_trace := evt_tr_r_trace
  }.

Section LabeledStepExecutions.
  Variable event : Type.
  Variable A : Type.
  Variable L : Type.
  Variable trace : Type.
  Context {e_st : event_state event A L}.

  Definition lb_step_relation := A -> L -> A -> list trace -> Prop.

  Definition enabled (step : lb_step_relation) (l : L) (a : A) : Prop :=
  exists a' tr, step a l a' tr.

  Definition l_enabled (step : lb_step_relation) (l : L) (e : event) : Prop :=
  enabled step l (evt_a e).

  Definition occurred (l : L) (e : event) : Prop := l = evt_l e.

  Definition inf_enabled (step : lb_step_relation) (l : L) (s : infseq event) : Prop :=
    inf_often (now (l_enabled step l)) s.

  Definition cont_enabled (step : lb_step_relation) (l : L) (s : infseq event) : Prop :=
    continuously (now (l_enabled step l)) s.

  Definition inf_occurred (l : L) (s : infseq event) : Prop :=
    inf_often (now (occurred l)) s.

  Definition strong_local_fairness (step : lb_step_relation) (s : infseq event) : Prop :=
    forall l : L, inf_enabled step l s -> inf_occurred l s.

  Definition weak_local_fairness (step : lb_step_relation) (s : infseq event) : Prop :=
    forall l : L, cont_enabled step l s -> inf_occurred l s.

  Lemma strong_local_fairness_invar :
    forall step e s, strong_local_fairness step (Cons e s) -> strong_local_fairness step s.
  Proof. 
    unfold strong_local_fairness. unfold inf_enabled, inf_occurred, inf_often. 
    intros step e s fair a alev. 
    assert (alevt_es: always (eventually (now (l_enabled step a))) (Cons e s)).
    constructor. 
    constructor 2. destruct alev; assumption. 
    simpl. assumption.
    clear alev. generalize (fair a alevt_es); clear fair alevt_es.
    intro fair; case (always_Cons fair); trivial.
  Qed.

  Lemma weak_local_fairness_invar :
    forall step e s, weak_local_fairness step (Cons e s) -> weak_local_fairness step s.
  Proof.
    unfold weak_local_fairness. unfold cont_enabled, inf_occurred, continuously, inf_often.
    intros step e s fair a eval.
    assert (eval_es: eventually (always (now (l_enabled step a))) (Cons e s)).
      apply E_next. assumption.
    apply fair in eval_es.
    apply always_invar in eval_es.
    assumption.
  Qed.

  Lemma strong_local_fairness_weak :
    forall step s, strong_local_fairness step s -> weak_local_fairness step s.
  Proof.
  move => step.
  case => e s.
  rewrite /strong_local_fairness /weak_local_fairness /inf_enabled /cont_enabled.
  move => H_str l H_cont.
  apply: H_str.
  exact: continuously_inf_often.
  Qed.

  CoInductive lb_step_state_execution (step : lb_step_relation) : infseq event -> Prop :=
    Cons_lb_step_exec : forall (e e' : event) (tr : list trace) (s : infseq event),
      step (evt_a e) (evt_l e) (evt_a e') tr ->
      lb_step_state_execution step (Cons e' s) ->
      lb_step_state_execution step (Cons e (Cons e' s)).

  Lemma lb_step_state_execution_invar :
    forall step x s, lb_step_state_execution step (Cons x s) -> lb_step_state_execution step s.
  Proof.
    intros step x s e. change (lb_step_state_execution step (tl (Cons x s))).
    destruct e; simpl. assumption. 
  Qed.

  Definition event_step_star_ex (step : step_relation A trace) (init : A) (e : event) :=
  exists tr, refl_trans_1n_trace step init (evt_a e) tr.

  Definition step_star_lb_step_reachable (lb_step : lb_step_relation) (step : step_relation A trace) (init : A) :=
    forall a l a' tr tr',
     refl_trans_1n_trace step init a tr' ->
     lb_step a l a' tr ->
     refl_trans_1n_trace step init a' (tr' ++ tr).
  
  Lemma step_star_ex_lb_step_state_execution :
    forall lb_step step init,
      step_star_lb_step_reachable lb_step step init ->
      forall s, event_step_star_ex step init (hd s) ->
      lb_step_state_execution lb_step s ->
      always (now (event_step_star_ex step init)) s.
  Proof.
  move => lb_step step init H_r.
  case => e s H_star.
  move: e s H_star.
  cofix cf.
  move => e.
  case => e' s H_star H_exec'.
  constructor; first by [].    
  apply cf.
    inversion H_exec'; subst_max.
    simpl in *.    
    rewrite /event_step_star_ex /=.
    rewrite /event_step_star_ex /= in H_star.
    break_exists.
    rewrite /step_star_lb_step_reachable in H_r.
    have H_d := H_r _ _ _ _ _ H H1.
    by exists (x ++ tr).
  move: H_exec'.
  apply: lb_step_state_execution_invar.
  Qed.
End LabeledStepExecutions.

Section LabeledStepTraceExecutions.
  Variable event : Type.
  Variable A : Type.
  Variable L : Type.
  Variable trace : Type.
  Context {e_tr : event_state_trace event A L trace}.

  CoInductive lb_step_state_trace_execution (step : lb_step_relation A L trace) : infseq event -> Prop :=
    Cons_lb_step_trace_exec : forall (e e' : event) (tr : list trace) (s : infseq event),
      step (evt_a e) (evt_l e) (evt_a e') tr ->
      evt_trace e' = evt_trace e ++ tr ->
      lb_step_state_trace_execution step (Cons e' s) ->
      lb_step_state_trace_execution step (Cons e (Cons e' s)).

  Lemma lb_step_state_trace_execution_invar :
    forall step x s, lb_step_state_trace_execution step (Cons x s) -> lb_step_state_trace_execution step s.
  Proof.
    intros step x s e. change (lb_step_state_trace_execution step (tl (Cons x s))).
    destruct e; simpl. assumption. 
  Qed.

  Lemma lb_step_state_trace_execution_step_state_execution : 
    forall step s, lb_step_state_trace_execution step s -> lb_step_state_execution step s.
   Proof.
     move => step.
     cofix c.
     move => s H_tr_exec.
     invcs H_tr_exec.
     apply c in H1.
     move: H H1.
     exact: Cons_lb_step_exec.
   Qed.

   Definition event_step_star (step : step_relation A trace) (init : A) (e : event) :=
     refl_trans_1n_trace step init (evt_a e) (evt_trace e).

  Lemma step_star_lb_step_state_trace_execution :
    forall lb_step step init,
      step_star_lb_step_reachable lb_step step init ->
      forall s, event_step_star step init (hd s) ->
      lb_step_state_trace_execution lb_step s ->
      always (now (event_step_star step init)) s.
  Proof.
    move => lb_step step init H_r.
    case => e s H_star.
    move: e s H_star.
    cofix cf.
    move => e.
    case => e' s H_star H_exec'.
    constructor; first by [].
    apply cf.
    inversion H_exec'; subst_max.
    simpl in *.    
    rewrite /event_step_star /=.
    rewrite /event_step_star /= in H_star.
    rewrite /step_star_lb_step_reachable in H_r.
    have H_d := H_r _ _ _ _ _ H_star H2.
    rewrite H3.
    exact: H_r _ _ _ _ _ H_star H2.
    move: H_exec'.
    apply: lb_step_state_trace_execution_invar.
  Qed.
End LabeledStepTraceExecutions.

Section LabeledStepFailure.
  Context `{labeled_multi_params : LabeledMultiParams}.

  Inductive lb_step_f : lb_step_relation (list name * network) label (name * (input + list output)) :=
  | LSF_deliver : forall net net' failed p xs ys out d l lb,
                     nwPackets net = xs ++ p :: ys ->
                     ~ In (pDst p) failed ->
                     lb_net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (lb, out, d, l) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     lb_step_f (failed, net) lb (failed, net') [(pDst p, inr out)]
  | LSF_input : forall h net net' failed out inp d l lb,
                  ~ In h failed ->
                  lb_input_handlers h inp (nwState net h) = (lb, out, d, l) ->
                  net' = mkNetwork (send_packets h l ++ nwPackets net)
                                   (update (nwState net) h d) ->
                  lb_step_f (failed, net) lb (failed, net') [(h, inl inp); (h, inr out)]
  | LSF_stutter : forall net failed, lb_step_f (failed, net) label_silent (failed, net) [].
  
  Context {failure_params : FailureParams unlabeled_multi_params}.

  Lemma step_f_star_lb_step_reachable :
    step_star_lb_step_reachable lb_step_f step_f step_f_init.
  Proof.
    rewrite /step_star_lb_step_reachable.
    case => failed net l.
    case => failed' net' tr tr' H_star H_st.
    invcs H_st.
    - set net' := {| nwPackets := _ ; nwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      have ->: [(pDst p, inr out)] = [(pDst p, inr out)] ++ [] by [].
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: (@SF_deliver _ _ _ _ _ _ _ xs ys _ d l0) => //.
      rewrite /net_handlers /= /unlabeled_net_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - set net' := {| nwPackets := _ ; nwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      have ->: [(h, inl inp); (h, inr out)] = [(h, inl inp); (h, inr out)] ++ [] by [].
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: SF_input => //.
      rewrite /input_handlers /= /unlabeled_input_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - by have ->: tr' ++ [] = tr' by auto with datatypes.
  Qed.

  Lemma step_f_star_ex_lb_step_state_execution :
    forall s, event_step_star_ex step_f step_f_init (hd s) ->
         lb_step_state_execution lb_step_f s ->
         always (now (event_step_star_ex step_f step_f_init)) s.
  Proof.
  apply: step_star_ex_lb_step_state_execution.
  exact: step_f_star_lb_step_reachable.
  Qed.

  Lemma step_f_star_lb_step_state_trace_execution :
    forall s, event_step_star step_f step_f_init (hd s) ->
         lb_step_state_trace_execution lb_step_f s ->
         always (now (event_step_star step_f step_f_init)) s.
  Proof.
  apply: step_star_lb_step_state_trace_execution.
  exact: step_f_star_lb_step_reachable.
  Qed.
End LabeledStepFailure.

Section LabeledStepOrder.
  Context `{labeled_multi_params : LabeledMultiParams}.

  Inductive lb_step_o_f : lb_step_relation (list name * ordered_network) label (name * (input + output)) :=
  | LSOF_deliver : forall net net' failed tr m ms out d l from to lb,
                     onwPackets net from to = m :: ms ->
                     ~ In to failed ->
                     lb_net_handlers to from m (onwState net to) = (lb, out, d, l) ->
                     net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l)
                                       (update' (onwState net) to d) ->
                     tr = map (fun o => (to, inr o)) out ->
                     lb_step_o_f (failed, net) lb (failed, net') tr
  | LSOF_input : forall h net net' failed tr out inp d l lb,
                   ~ In h failed ->
                   lb_input_handlers h inp (onwState net h) = (lb, out, d, l) ->
                   net' = mkONetwork (@collate name EqDec_eq_name msg h (onwPackets net) l)
                                     (update' (onwState net) h d) ->
                   tr = (h, inl inp) :: map (fun o => (h, inr o)) out ->
                   lb_step_o_f (failed, net) lb (failed, net') tr
  | LSOF_stutter : forall net failed, lb_step_o_f (failed, net) label_silent (failed, net) [].

  Context {overlay_params : NameOverlayParams unlabeled_multi_params}.
  Context {fail_msg_params : FailMsgParams unlabeled_multi_params}.

  Lemma step_o_f_star_lb_step_reachable :
    step_star_lb_step_reachable lb_step_o_f step_o_f step_o_f_init.
  Proof.
    rewrite /step_star_lb_step_reachable.
    case => failed net l.
    case => failed' net' tr tr' H_star H_st.
    invcs H_st.
    - set net' := {| onwPackets := _ ; onwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      rewrite (app_nil_end (map _ _)).
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: (SOF_deliver _ _ _ H3) => //.
      rewrite /net_handlers /= /unlabeled_net_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - set net' := {| onwPackets := _ ; onwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      rewrite (app_nil_end (_ :: _)).
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: SOF_input => //; first by [].
      rewrite /input_handlers /= /unlabeled_input_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - by have ->: tr' ++ [] = tr' by auto with datatypes.
  Qed.

  Lemma step_o_f_star_ex_lb_step_state_execution :
    forall s, event_step_star_ex step_o_f step_o_f_init (hd s) ->
         lb_step_state_execution lb_step_o_f s ->
         always (now (event_step_star_ex step_o_f step_o_f_init)) s.
  Proof.
  apply: step_star_ex_lb_step_state_execution.
  exact: step_o_f_star_lb_step_reachable.
  Qed.

  Lemma step_o_f_star_lb_step_state_trace_execution :
    forall s, event_step_star step_o_f step_o_f_init (hd s) ->
         lb_step_state_trace_execution lb_step_o_f s ->
         always (now (event_step_star step_o_f step_o_f_init)) s.
  Proof.
  apply: step_star_lb_step_state_trace_execution.
  exact: step_o_f_star_lb_step_reachable.
  Qed.
End LabeledStepOrder.

Section LabeledStepOrderDynamic.
  Context `{labeled_multi_params : LabeledMultiParams}.

  Inductive lb_step_o_d_f : lb_step_relation (list name * ordered_dynamic_network) label (name * (input + output)) :=
  | LSODF_deliver : forall net net' failed tr m ms out d d' l from to lb,
      ~ In to failed ->
      In to (odnwNodes net) ->
      odnwState net to = Some d ->
      odnwPackets net from to = m :: ms ->
      lb_net_handlers to from m d = (lb, out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate to (update2 (odnwPackets net) from to ms) l;
                odnwState := update_opt (odnwState net) to d' |} ->
      tr = map (fun o => (to, inr o)) out ->
      lb_step_o_d_f (failed, net) lb (failed, net') tr
  | LSODF_input : forall h net net' failed tr out inp d d' l lb,
      ~ In h failed ->
      In h (odnwNodes net) ->
      odnwState net h = Some d ->
      lb_input_handlers h inp d = (lb, out, d', l) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate h (odnwPackets net) l;
                odnwState := update_opt (odnwState net) h d' |} ->
      tr = (h, inl inp) :: map (fun o => (h, inr o)) out ->
      lb_step_o_d_f (failed, net) lb (failed, net') tr
  | LSODF_stutter : forall net failed, lb_step_o_d_f (failed, net) label_silent (failed, net) [].

  Context {overlay_params : NameOverlayParams unlabeled_multi_params}.
  Context {fail_msg_params : FailMsgParams unlabeled_multi_params}.
  Context {new_msg_params : NewMsgParams unlabeled_multi_params}.

  Lemma step_o_d_f_star_lb_step_reachable :
    step_star_lb_step_reachable lb_step_o_d_f step_o_d_f step_o_d_f_init.
  Proof.
    rewrite /step_star_lb_step_reachable.
    case => failed net l.
    case => failed' net' tr tr' H_star H_st.
    invcs H_st.
    - set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      rewrite (app_nil_end (map _ _)).
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: (SODF_deliver _ _ _ _ _ H5 H6) => //.
      rewrite /net_handlers /= /unlabeled_net_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
      apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
      rewrite (app_nil_end (_ :: _)).
      apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
      apply: (SODF_input _ _ _ _ H5) => //.
      rewrite /input_handlers /= /unlabeled_input_handlers /=.
      repeat break_let.
      by tuple_inversion.
    - by have ->: tr' ++ [] = tr' by auto with datatypes.
  Qed.

  Lemma step_o_d_f_star_ex_lb_step_state_execution :
    forall s, event_step_star_ex step_o_d_f step_o_d_f_init (hd s) ->
         lb_step_state_execution lb_step_o_d_f s ->
         always (now (event_step_star_ex step_o_d_f step_o_d_f_init)) s.
  Proof.
    apply: step_star_ex_lb_step_state_execution.
    exact: step_o_d_f_star_lb_step_reachable.
  Qed.

  Lemma step_o_d_f_star_lb_step_state_trace_execution :
    forall s, event_step_star step_o_d_f step_o_d_f_init (hd s) ->
         lb_step_state_trace_execution lb_step_o_d_f s ->
         always (now (event_step_star step_o_d_f step_o_d_f_init)) s.
  Proof.
    apply: step_star_lb_step_state_trace_execution.
    exact: step_o_d_f_star_lb_step_reachable.
  Qed.
End LabeledStepOrderDynamic.

Hint Extern 4 (@LabeledMultiParams _) => apply unlabeled_multi_params : typeclass_instances.
