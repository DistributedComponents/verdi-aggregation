Require Import Verdi.
Require Import infseq.

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
    label_stutter : label ;
    lb_init_handlers : lb_name -> data ;
    lb_net_handlers : lb_name -> lb_name -> lb_msg -> data -> (list output) * data * list (lb_name * lb_msg) * label ;
    lb_input_handlers : lb_name -> input -> data -> (list output) * data * list (lb_name * lb_msg) * label
  }.

Section LabeledParams.

Context {base_params : BaseParams}.
Context {params : LabeledMultiParams base_params}.

Definition unlabeled_net_handlers me src m st :=
let '(out, st', ps, lb) := lb_net_handlers me src m st in (out, st', ps).

Definition unlabeled_input_handlers me inp st :=
let '(out, st', ps, lb) := lb_input_handlers me inp st in (out, st', ps).

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

End LabeledParams.

Section LabeledStepRelations.
  Variable A : Type.
  Variable L : Type.
  Variable trace : Type.

  Definition lb_step_relation := A -> L -> A -> list trace -> Prop.

  Definition enabled (step : lb_step_relation) (l : L) (a : A) : Prop :=
  exists a' tr, step a l a' tr.

  Definition event := (A * L)%type.

  Definition a_of_event : event -> A := fun x => fst x.
  Definition l_of_event : event -> L := fun x => snd x.

  Definition l_enabled_for_event (step : lb_step_relation) (l : L) (e : event) : Prop :=
  enabled step l (a_of_event e).

  CoInductive lb_step_execution (step : lb_step_relation) : infseq event -> Prop :=
    Cons_lb_step_exec : forall (a a' : A) (l l' : L) (tr tr' : list trace) (s : infseq event),
      step a l a' tr ->
      lb_step_execution step (Cons (a', l') s) ->
      lb_step_execution step (Cons (a, l) (Cons (a', l') s)).

  Definition occurred (l : L) (e : event) : Prop :=
    l = l_of_event e.

  Definition inf_enabled (step : lb_step_relation) (l : L) (s : infseq event) : Prop :=
    inf_often (now (l_enabled_for_event step l)) s.

  Definition inf_occurred (l : L) (s : infseq event) : Prop :=
    inf_often (now (occurred l)) s.

  Definition strong_local_fairness (step : lb_step_relation) (s : infseq event) : Prop :=
    forall l : L, inf_enabled step l s -> inf_occurred l s.

  Lemma strong_local_fairness_invar :
    forall step e s, strong_local_fairness step (Cons e s) -> strong_local_fairness step s.
  Proof. 
    unfold strong_local_fairness. unfold inf_enabled, inf_occurred, inf_often. 
    intros step e s fair a alev. 
    assert (alev_es: always (eventually (now (l_enabled_for_event step a))) (Cons e s)).
    constructor. 
    constructor 2. destruct alev; assumption. 
    simpl. assumption.
    clear alev. generalize (fair a alev_es); clear fair alev_es.
    intro fair; case (always_Cons fair); trivial.
  Qed.

  Lemma lb_step_execution_invar :
    forall step x s, lb_step_execution step (Cons x s) -> lb_step_execution step s.
  Proof.
    intros step x s e. change (lb_step_execution step (tl (Cons x s))). 
    destruct e; simpl. assumption. 
  Qed.
End LabeledStepRelations.

Section LabeledStepAsync.

  Context `{params : LabeledMultiParams}.

  Inductive lb_step_m : lb_step_relation network label (name * (input + list output)) :=
  | LSM_deliver : forall net net' p xs ys out d l lb,
                     nwPackets net = xs ++ p :: ys ->
                     lb_net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l, lb) ->
                     net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                      (update (nwState net) (pDst p) d) ->
                     lb_step_m net lb net' [(pDst p, inr out)]
  | LSM_input : forall h net net' out inp d l lb,
                   lb_input_handlers h inp (nwState net h) = (out, d, l, lb) ->
                   net' = mkNetwork (send_packets h l ++ nwPackets net)
                                    (update (nwState net) h d) ->
                   lb_step_m net lb net' [(h, inl inp); (h, inr out)]
  | LSM_stutter : forall net, lb_step_m net label_stutter net [].

  Definition event_step_m_star (e : event _ label) :=
    exists tr, step_m_star step_m_init (a_of_event e) tr.

  Lemma step_m_star_lb_step_reachable_ex :
    forall net l net' tr tr',
    lb_step_m net l net' tr ->
    step_m_star step_m_init net tr' ->
    exists tr0, step_m_star step_m_init net' tr0.
  Proof.  
  move => net l net' tr tr' H_step H_star.
  exists (tr ++ tr').    
  Admitted.

  Lemma step_m_star_lb_step_execution : 
    forall s, event_step_m_star (hd s) ->
         lb_step_execution lb_step_m s ->
         always (now event_step_m_star) s.
  Proof.
  case => e s H_star.
  move: e s H_star.
  cofix cf.
  move => e.
  case => e' s H_star H_exec'.
  constructor; first by [].
  apply cf.
    inversion H_exec'; subst_max.
    rewrite /event_step_m_star /a_of_event /=.
    rewrite /event_step_m_star /a_of_event /= in H_star.
    break_exists.
    move: H1 H.
    apply: step_m_star_lb_step_reachable_ex.
  move: H_exec'.
  exact: lb_step_execution_invar.
  Qed.      
End LabeledStepAsync.

Section LabeledStepOrder.
  Context `{params : LabeledMultiParams}.

  Inductive lb_step_o : lb_step_relation (list name * ordered_network) label (name * (input + list output)) :=
  | LSO_deliver : forall net net' failed m ms out d l from to lb,
                     onwPackets net from to = m :: ms ->
                     ~ In to failed ->
                     lb_net_handlers to from m (onwState net to) = (out, d, l, lb) ->
                     net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l)
                                       (update' (onwState net) to d) ->
                     lb_step_o (failed, net) lb (failed, net') [(to, inr out)]
  | LSO_input : forall h net net' failed out inp d l lb,
                   ~ In h failed ->
                   lb_input_handlers h inp (onwState net h) = (out, d, l, lb) ->
                   net' = mkONetwork (@collate name EqDec_eq_name msg h (onwPackets net) l)
                                     (update' (onwState net) h d) ->
                   lb_step_o (failed, net) lb (failed, net') [(h, inl inp); (h, inr out)]
  | LSO_stutter : forall net failed, lb_step_o (failed, net) label_stutter (failed, net) [].

End LabeledStepOrder.

Section LabeledStepOrderDynamic.
  Context `{params : LabeledMultiParams}.

  Inductive lb_step_o_d : lb_step_relation (list name * ordered_dynamic_network) label (name * (input + list output)) :=
  | LSOD_deliver : forall net net' failed m ms out d d' l from to lb,
      ~ In to failed ->
      In to (odnwNodes net) ->
      odnwState net to = Some d ->
      odnwPackets net from to = m :: ms ->
      lb_net_handlers to from m d = (out, d', l, lb) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate to (update2 (odnwPackets net) from to ms) l;
                odnwState := update_opt (odnwState net) to d' |} ->
      lb_step_o_d (failed, net) lb (failed, net') [(to, inr out)]
  | LSOD_input : forall h net net' failed out inp d d' l lb,
      ~ In h failed ->
      In h (odnwNodes net) ->
      odnwState net h = Some d ->
      lb_input_handlers h inp d = (out, d', l, lb) ->
      net' = {| odnwNodes := odnwNodes net;
                odnwPackets := collate h (odnwPackets net) l;
                odnwState := update_opt (odnwState net) h d' |} ->
      lb_step_o_d (failed, net) lb (failed, net') [(h, inl inp); (h, inr out)]
  | LSOD_stutter : forall net failed, lb_step_o_d (failed, net) label_stutter (failed, net) [].

End LabeledStepOrderDynamic.
