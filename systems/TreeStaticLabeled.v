Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.TotalMapExecutionSimulations.
Require Import Verdi.PartialMapExecutionSimulations.

Require Import NameAdjacency.
Require Import TreeAux.
Require Import FailureRecorderStaticLabeled.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import InfSeqExt.exteq.
Require Import InfSeqExt.map.

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

Module Tree (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC)
 (Import RNT : RootNameType NT) (Import ANT : AdjacentNameType NT).

Module A := Adjacency NT NOT NSet ANT.
Import A.

Module AX := TAux NT NOT NSet NOTC NMap.
Import AX.

Module FR := FailureRecorder NT NOT NSet ANT.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Inductive Msg : Set := 
| Fail : Msg
| Level : option lv -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
case: o; case: o0.
- move => n m.
  case (lv_eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Inductive Input : Set :=
| LevelRequest : Input
| Broadcast : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Output : Set :=
| LevelResponse : option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
case: o; case: o0.
- move => n m.
  case (lv_eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Record Data := mkData { 
  adjacent : NS ; 
  broadcast : bool ; 
  levels : NL
}.

Definition InitData (n : name) := 
if root_dec n then
  {| adjacent := adjacency n nodes ;
     broadcast := true ;
     levels := NMap.empty lv |}
else
  {| adjacent := adjacency n nodes ;
     broadcast := false ;
     levels := NMap.empty lv |}.

Inductive Label : Type :=
| Tau : Label
| RecvFail : name -> name -> Label
| RecvLevel : name -> name -> Label
| DeliverBroadcastTrue : name -> Label
| DeliverBroadcastFalse : name -> Label
| DeliverLevelRequest : name -> Label.

Definition Label_eq_dec : forall x y : Label, {x = y} + {x <> y}.
decide equality; auto using name_eq_dec.
Defined.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output Label.

Definition RootNetHandler (me src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Level _ => ret (RecvLevel me src)
| Fail => 
  put {| adjacent := NSet.remove src st.(adjacent) ;
         broadcast := st.(broadcast) ;
         levels := st.(levels) |} ;;
  ret (RecvFail me src)
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Level None =>
 (if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.remove src st.(levels))) then
    put {| adjacent := st.(adjacent) ;           
           broadcast := st.(broadcast) ;
           levels := NMap.remove src st.(levels) |}
  else 
    put {| adjacent := st.(adjacent) ;           
           broadcast := true ;
           levels := NMap.remove src st.(levels) |}) ;;
  ret (RecvLevel me src)
| Level (Some lv') =>
  (if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.add src lv' st.(levels))) then
    put {| adjacent := st.(adjacent) ;
           broadcast := st.(broadcast) ;
           levels := NMap.add src lv' st.(levels) |}
  else
    put {| adjacent := st.(adjacent) ;
           broadcast := true ;
           levels := NMap.add src lv' st.(levels) |}) ;;
  ret (RecvLevel me src)
| Fail => 
  (if olv_eq_dec (level st.(adjacent) st.(levels)) (level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels))) then
    put {| adjacent := NSet.remove src st.(adjacent) ;
           broadcast := st.(broadcast) ;
           levels := NMap.remove src st.(levels) |}
  else
    put {| adjacent := NSet.remove src st.(adjacent) ;
           broadcast := true ;
           levels := NMap.remove src st.(levels) |}) ;; 
   ret (RecvFail me src)
end.

Definition NetHandler (me src : name) (msg : Msg) : Handler Data :=
if root_dec me then RootNetHandler me src msg 
else NonRootNetHandler me src msg.

Instance Tree_TreeMsg : TreeMsg := 
  {
    tree_msg := Msg ;
    tree_level := Level
  }.

Definition send_level_fold (lvo : option lv) (n : name) (res : Handler Data) : Handler Data :=
send (n, Level lvo) ;; res.

Definition send_level_adjacent (lvo : option lv) (fs : NS) : Handler Data :=
NSet.fold (send_level_fold lvo) fs (ret Tau).

Definition RootIOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Broadcast => 
  if st.(broadcast) then
    send_level_adjacent (Some 0) st.(adjacent) ;;
    put {| adjacent := st.(adjacent);
          broadcast := false;
          levels := st.(levels) |} ;;
    ret (DeliverBroadcastTrue me)
  else
    ret (DeliverBroadcastFalse me)
| LevelRequest => 
  write_output (LevelResponse (Some 0)) ;;
  ret (DeliverLevelRequest me)
end.

Definition NonRootIOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Broadcast =>
  if st.(broadcast) then
    (send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent) ;; 
    put {| adjacent := st.(adjacent);
           broadcast := false;
           levels := st.(levels) |} ;;
    ret (DeliverBroadcastTrue me))
  else
    ret (DeliverBroadcastFalse me)
| LevelRequest =>   
  write_output (LevelResponse (level st.(adjacent) st.(levels))) ;;
  ret (DeliverLevelRequest me)
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler me i 
else NonRootIOHandler me i.

Instance Tree_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Tree_LabeledMultiParams : LabeledMultiParams Tree_BaseParams :=
  {
    lb_name := name ;
    lb_msg  := Msg ;
    lb_msg_eq_dec := Msg_eq_dec ;
    lb_name_eq_dec := name_eq_dec ;
    lb_nodes := nodes ;
    lb_all_names_nodes := all_names_nodes ;
    lb_no_dup_nodes := no_dup_nodes ;
    label := Label ;
    label_silent := Tau ;
    lb_init_handlers := InitData ;
    lb_net_handlers := fun dst src msg s =>
                      runGenHandler s (NetHandler dst src msg) ;
    lb_input_handlers := fun nm msg s =>
                        runGenHandler s (IOHandler nm msg)
  }.

Instance Tree_MultiParams : MultiParams Tree_BaseParams := unlabeled_multi_params.

Instance Tree_NameOverlayParams : NameOverlayParams Tree_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance Tree_FailMsgParams : FailMsgParams Tree_MultiParams :=
  {
    msg_fail := Fail
  }.

Lemma net_handlers_NetHandler :
  forall dst src m st os st' ms,
    net_handlers dst src m st = (os, st', ms) ->
    exists lb, NetHandler dst src m st = (lb, os, st', ms).
Proof.
intros.
simpl in *.
unfold unlabeled_net_handlers, lb_net_handlers in *.
simpl in *.
repeat break_let.
find_inversion.
by exists l0; auto.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st lb out st' ms,
    NetHandler dst src msg st = (lb, out, st', ms) ->
    (root dst /\ msg = Fail /\ lb = RecvFail dst src /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ lb = RecvLevel dst src /\ 
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st lb out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg; monad_unfold.
- case root_dec => /= H_dec.
  * move => H_eq.
    find_injection.
    by left.
  * case olv_eq_dec => /= H_dec' H_eq; find_injection; first find_rewrite.
      by right; left.
    by right; right; left.
- case root_dec => /= H_dec olv_msg.
    move => H_eq.
    find_injection.
    right; right; right; left.
    split => //.
    by exists olv_msg.
  case H_olv_dec: olv_msg => [lv_msg|]; case olv_eq_dec => /= H_dec' H_eq; find_injection.
  * right; right; right; right; left.
    split => //.
    by exists lv_msg.
  * right; right; right; right; right; left.
    split => //.
    by exists lv_msg.
  * by right; right; right; right; right; right; left.
  * by right; right; right; right; right; right; right.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    exists lb, IOHandler h i d = (lb, os, d', ms).
Proof.
intros.
simpl in *.
unfold unlabeled_input_handlers, lb_input_handlers in *.
simpl in *.
repeat break_let.
find_inversion.
by exists l0; auto.
Qed.

Lemma send_level_fold_app :
  forall ns st olv nm lb,
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (lb, [], s, nm)) st) = 
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (lb, [], s, [])) st) ++ nm.
Proof.
elim => //=.
move => n ns IH st olv nm lb.
rewrite {1}/send_level_fold /=.
monad_unfold.
rewrite /=.
rewrite IH.
rewrite app_assoc.
by rewrite -IH.
Qed.

Lemma send_level_adjacent_fst_eq : 
forall fs olv st,
  snd (send_level_adjacent olv fs st) = level_adjacent olv fs.
Proof.
move => fs olv st.
rewrite /send_level_adjacent /level_adjacent.
rewrite 2!NSet.fold_spec.
move: olv st.
elim: NSet.elements => [|n ns IH] //=.
move => olv st.
rewrite {2}/level_fold {2}/send_level_fold /= /flip /=.
rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
have IH' := IH olv st.
rewrite -IH'.
monad_unfold.
by rewrite -send_level_fold_app.
Qed.

Lemma fst_fst_fst_tt_send_level_fold : 
forall ns nm olv st lb,
fst
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st))) = lb.
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma send_level_adjacent_fst_fst_eq : 
forall fs olv st,
  fst (fst (fst (send_level_adjacent olv fs st))) = Tau.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite fst_fst_fst_tt_send_level_fold.
Qed.

Lemma snd_fst_fst_out_send_level_fold : 
forall ns nm olv st lb,
snd
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st))) = [].
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma snd_fst_st_send_level_fold : 
forall ns nm olv st lb,
snd (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st)) = st.
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma send_level_adjacent_snd_fst_fst : 
forall fs olv st,
  snd (fst (fst (send_level_adjacent olv fs st))) = [].
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite snd_fst_fst_out_send_level_fold.
Qed.

Lemma send_level_adjacent_snd_fst : 
forall fs olv st,
  snd (fst (send_level_adjacent olv fs st)) = st.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite snd_fst_st_send_level_fold.
Qed.

Lemma send_level_adjacent_eq : 
  forall fs olv st,
  send_level_adjacent olv fs st = (Tau, [], st, level_adjacent olv fs).
Proof.
move => fs olv st.
case H_eq: send_level_adjacent => [[[u o] s b]].
have H_eq'_1 := send_level_adjacent_fst_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_1.
have H_eq'_2 := send_level_adjacent_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_2.
have H_eq'_3 := send_level_adjacent_snd_fst_fst fs olv st.
rewrite H_eq /= in H_eq'_3.
have H_eq'_4 := send_level_adjacent_snd_fst fs olv st.
rewrite H_eq /= in H_eq'_4.
by rewrite H_eq'_1 H_eq'_2 H_eq'_3 H_eq'_4.
Qed.

Lemma IOHandler_cases :
  forall h i st lb out st' ms,
      IOHandler h i st = (lb, out, st', ms) ->
      (root h /\ i = Broadcast /\ lb = DeliverBroadcastTrue h /\ 
       st.(broadcast) = true /\
       st'.(adjacent) = st.(adjacent) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (Some 0) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\ lb = DeliverBroadcastTrue h /\
       st.(broadcast) = true /\
       st'.(adjacent) = st.(adjacent) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (i = Broadcast /\ lb = DeliverBroadcastFalse h /\
       st.(broadcast) = false /\
       st' = st /\
       out = [] /\ ms = []) \/
      (root h /\ i = LevelRequest /\ lb = DeliverLevelRequest h /\
       st' = st /\
       out = [LevelResponse (Some 0)] /\ ms = []) \/
      (~ root h /\ i = LevelRequest /\ lb = DeliverLevelRequest h /\
       st' = st /\
       out = [LevelResponse (level st.(adjacent) st.(levels))] /\ ms = []).
Proof.
move => h i st lb out st' ms.
rewrite /IOHandler /RootIOHandler /NonRootIOHandler.
case: i => [|]; monad_unfold.
- case root_dec => /= H_dec H_eq; find_injection.
    by right; right; right; left.
  by right; right; right; right.
- case root_dec => /= H_dec; case H_b: broadcast => /=.
  * left.
    repeat break_let.
    repeat find_injection.
    have H_eq := send_level_adjacent_eq st.(adjacent) (Some 0) st.
    find_rewrite.
    tuple_inversion.
    by rewrite app_nil_l -app_nil_end.
  * right; right; left.
    by find_injection.
  * right; left.
    repeat break_let.
    repeat find_injection.
    have H_eq := send_level_adjacent_eq st.(adjacent) (level st.(adjacent) st.(levels)) st.
    find_rewrite.
    tuple_inversion.
    by rewrite app_nil_l -app_nil_end.
  * right; right; left.
    by find_injection.
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
  rewrite /net_handlers /= /runGenHandler_ignore /= /unlabeled_net_handlers /lb_net_handlers /= /runGenHandler /id in Heqp H_n.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  by net_handler_cases; FR.net_handler_cases; simpl in *; congruence.
- move => me src mg st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /unlabeled_net_handlers /= /runGenHandler /= in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  by net_handler_cases; simpl in *; congruence.
- move => me inp st inp' H_eq.
  rewrite /pt_mapped_input_handlers.
  repeat break_let.
  case H_i: input_handlers => [[out st'] ps].
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler in Heqp H_i.
  repeat break_let.
  repeat tuple_inversion.
  by io_handler_cases.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
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

Instance Tree_FailureRecorder_label_tot_map : LabeledMultiParamsLabelTotalMap Tree_LabeledMultiParams FR.FailureRecorder_LabeledMultiParams :=
  {
    tot_map_label := fun lb =>
                      match lb with
                      | Tau => FR.Tau
                      | RecvFail dst src => FR.RecvFail dst src
                      | RecvLevel _ _ => FR.Tau
                      | DeliverBroadcastTrue _ => FR.Tau
                      | DeliverBroadcastFalse _ => FR.Tau
                      | DeliverLevelRequest _ => FR.Tau
                      end
  }.

Instance Tree_FailureRecorder_labeled_partial_map_congruency : LabeledMultiParamsPartialMapCongruency Tree_FailureRecorder_base_params_pt_map Tree_FailureRecorder_name_tot_map Tree_FailureRecorder_multi_params_pt_map Tree_FailureRecorder_label_tot_map :=
  {
    pt_lb_label_silent_fst_snd := Logic.eq_refl ;
    pt_lb_net_handlers_some := _ ;
    pt_lb_net_handlers_none := _ ;
    pt_lb_input_handlers_some := _ ;
    pt_lb_input_handlers_none := _
  }.
Proof.
- move => me src m st m' out st' ps lb H_m H_eq.
  rewrite /lb_net_handlers /= /runGenHandler /= /id /= in H_eq.
  rewrite /tot_mapped_lb_net_handlers_label /= /runGenHandler /=.
  case H_n: NetHandler => [[[lb' out'] st''] ps'].
  by net_handler_cases; FR.net_handler_cases; simpl in *; congruence.
- move => me src m st H_eq.
  rewrite /tot_mapped_lb_net_handlers_label /= /runGenHandler /=.
  case H_n: NetHandler => [[[lb out] st'] ps].
  by net_handler_cases.
- move => me inp st inp' out st' ps lb H_i H_eq.
  rewrite /tot_mapped_lb_input_handlers_label /= /runGenHandler /=.
  case H_inp: IOHandler => [[[lb' out'] st''] ps'].
  by io_handler_cases.
- move => me inp st H_eq.
  rewrite /tot_mapped_lb_input_handlers_label /= /runGenHandler /=.
  case H_inp: IOHandler => [[[lb' out'] st''] ps'].
  by io_handler_cases.
Qed.

Lemma Tree_node_not_adjacent_self : 
forall net failed tr n, 
 step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
 ~ In n failed ->
 ~ NSet.In n (onwState net n).(adjacent).
Proof.
move => onet failed tr n H_st H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact: FR.Failure_node_not_adjacent_self H_st' H_in_f.
Qed.

Lemma Tree_not_failed_no_fail :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_not_failed_no_fail H_st' n n' H_in_f.
move => H_in.
case: H_inv'.
rewrite /= /id /=.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Tree_in_adj_adjacent_to :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact (FR.Failure_in_adj_adjacent_to H_st' n H_in_f H_ins).
Qed.

Lemma Tree_pt_map_msg_injective : 
  forall m0 m1 m2 : msg,
   pt_map_msg m0 = Some m2 -> pt_map_msg m1 = Some m2 -> m0 = m1.
Proof.
by case => [|lvo]; case => [|lvo'] H_eq.
Qed.

Lemma Tree_in_adj_or_incoming_fail :
forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_adj_or_incoming_fail H_st' _ H_in_f H_ins.
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
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st n n' H_in_f.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_le_one_fail H_st' _ n' H_in_f.
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
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_in_f' H_adj.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
exact: (FR.Failure_adjacent_to_in_adj H_st' H_in_f H_in_f' H_adj).
Qed.

Lemma Tree_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_ins.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_queue_fail_then_adjacent H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_ins.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Tree_first_fail_in_adj : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_eq.
have H_st' := Tree_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_first_fail_in_adj H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Tree_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr -> 
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

(* bfs_net_ok_root_levels_empty *)
Lemma Tree_root_levels_empty :
  forall net failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
  forall n, ~ In n failed -> 
  root n ->
  (net.(onwState) n).(levels) = NMap.empty lv.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_ordered_failure_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}.
  rewrite H_init /=.
  move => n H_in H_r.
  rewrite /InitData /=.
  by break_if.
concludes.
match goal with
| [ H : step_ordered_failure _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler; break_exists.
  net_handler_cases => //= ; simpl in *;
    update_destruct_max_simplify; repeat find_rewrite; auto.
- find_apply_lem_hyp input_handlers_IOHandler; break_exists.
  io_handler_cases => //=; simpl in *;
    update_destruct_max_simplify; repeat find_rewrite; auto.
- intros. simpl in *.
  eauto.
Qed.

Definition head_message_enables_label m src dst l :=
  forall net failed, 
  ~ In dst failed ->
  head (net.(onwPackets) src dst) = Some m ->
  enabled lb_step_ordered_failure l (failed, net).

Lemma Fail_enables_RecvFail :
  forall src dst, head_message_enables_label Fail src dst (RecvFail dst src).
Proof.
move => src dst.
rewrite /head_message_enables_label.
move => net failed H_f H_eq.
case H_eq_p: (onwPackets net src dst) => [|m ms]; first by find_rewrite.
find_rewrite.
simpl in *.
find_injection.
rewrite /enabled.
case H_hnd: (@lb_net_handlers _ Tree_LabeledMultiParams dst src Fail (onwState net dst)) => [[[lb' out] d'] l].
have H_lb := H_hnd.
rewrite /lb_net_handlers /= in H_hnd.
by net_handler_cases => //;
 exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
Qed.

Lemma Level_enables_RecvLevel :
  forall src dst lvo, head_message_enables_label (Level lvo) src dst (RecvLevel dst src).
Proof.
move => src dst lvo.
rewrite /head_message_enables_label.
move => net failed H_f H_eq.
case H_eq_p: (onwPackets net src dst) => [|m ms]; first by find_rewrite.
find_rewrite.
simpl in *.
find_injection.
rewrite /enabled.
case H_hnd: (@lb_net_handlers _ Tree_LabeledMultiParams dst src (Level lvo) (onwState net dst)) => [[[lb' out] d'] l].
have H_lb := H_hnd.
rewrite /lb_net_handlers /= in H_hnd.
net_handler_cases => //; find_injection.
- by exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst (onwState net dst) |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
- by exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
- by exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
- by exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
- by exists (failed, {| onwPackets := update2 Net.name_eq_dec (onwPackets net) src dst ms; onwState := update name_eq_dec (onwState net) dst d' |}), []; apply: LabeledStepOrderedFailure_deliver; eauto.
Qed.

Lemma Tree_lb_step_ordered_failure_RecvFail_enabled :
  forall net net' net'' failed failed' failed'' tr tr' dst src l,
  l <> RecvFail dst src ->
  lb_step_ordered_failure (failed, net) l (failed', net') tr ->
  lb_step_ordered_failure (failed, net) (RecvFail dst src) (failed'', net'') tr' ->
  enabled lb_step_ordered_failure (RecvFail dst src) (failed', net').
Proof.
move => net net' net'' failed failed' failed'' tr tr' dst src l H_neq H_st H_st'.
destruct l => //.
- invcs H_st => //. 
  * by net_handler_cases.
  * by io_handler_cases.
  * invcs H_st' => //; last by io_handler_cases.
    have H_hd: head (onwPackets net' src dst) = Some Fail by net_handler_cases => //; find_injection; find_rewrite.
    have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
    exact: Fail_enables_RecvFail.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; last by io_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    net_handler_cases => //=; rewrite /update2.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
  exact: Fail_enables_RecvFail.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; last by io_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    net_handler_cases => //=; rewrite /update2.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
  exact: Fail_enables_RecvFail.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    io_handler_cases => //=.
    * find_injection.
      case (name_eq_dec h src) => H_dec; last by rewrite collate_neq //; find_rewrite.
      subst_max.
      apply collate_head_head.
      by find_rewrite.
    * find_injection.
      case (name_eq_dec h src) => H_dec; last by rewrite collate_neq //; find_rewrite.
      subst_max.
      apply collate_head_head.
      by find_rewrite.
  exact: Fail_enables_RecvFail.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    io_handler_cases => //=.
    by find_rewrite.
  exact: Fail_enables_RecvFail.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: onwPackets net src dst = Fail :: ms by net_handler_cases => //; find_injection; find_rewrite.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some Fail.
    rewrite /net' /=.
    by io_handler_cases => //=; find_rewrite.
  exact: Fail_enables_RecvFail.
Qed.

Lemma Tree_lb_step_ordered_failure_RecvLevel_enabled :
  forall net net' net'' failed failed' failed'' tr tr' dst src l,
  l <> RecvLevel dst src ->
  lb_step_ordered_failure (failed, net) l (failed', net') tr ->
  lb_step_ordered_failure (failed, net) (RecvLevel dst src) (failed'', net'') tr' ->
  enabled lb_step_ordered_failure (RecvLevel dst src) (failed', net').
Proof.
move => net net' net'' failed failed' failed'' tr tr' dst src l H_neq H_st H_st'.
destruct l => //.
- invcs H_st => //. 
  * by net_handler_cases.
  * by io_handler_cases.
  * invcs H_st' => //; last by io_handler_cases.
    have H_hd: exists lvo, head (onwPackets net' src dst) = Some (Level lvo) by net_handler_cases => //; find_injection; find_rewrite; eexists.
    break_exists.
    have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
    by apply: Level_enables_RecvLevel; eauto.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: exists lvo, onwPackets net src dst = Level lvo :: ms by net_handler_cases => //; find_injection; find_rewrite; eexists.
  break_exists_name lvo.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; last by io_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some (Level lvo).
    rewrite /net' /=.
    net_handler_cases => //=; rewrite /update2.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
    * break_if.
      + break_and; subst.
        by find_rewrite.
      + by find_rewrite.
  by apply: Level_enables_RecvLevel; eauto.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: exists lvo, onwPackets net src dst = Level lvo :: ms by net_handler_cases => //; find_injection; find_rewrite; eexists.
  break_exists_name lvo.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; last by io_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some (Level lvo).
    rewrite /net' /=.
    net_handler_cases => //=; rewrite /update2.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
    * break_if.
      + by break_and; subst; intuition.
      + by find_rewrite.
  by apply: Level_enables_RecvLevel; eauto.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: exists lvo, onwPackets net src dst = Level lvo :: ms by net_handler_cases => //; find_injection; find_rewrite; eexists.
  break_exists_name lvo.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some (Level lvo).
    rewrite /net' /=.
    io_handler_cases => //=.
    * find_injection.
      case (name_eq_dec h src) => H_dec; last by rewrite collate_neq //; find_rewrite.
      subst_max.
      apply collate_head_head.
      by find_rewrite.
    * find_injection.
      case (name_eq_dec h src) => H_dec; last by rewrite collate_neq //; find_rewrite.
      subst_max.
      apply collate_head_head.
      by find_rewrite.
  by apply: Level_enables_RecvLevel; eauto.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: exists lvo, onwPackets net src dst = Level lvo :: ms by net_handler_cases => //; find_injection; find_rewrite; eexists.
  break_exists_name lvo.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some (Level lvo).
    rewrite /net' /=.
    io_handler_cases => //=.
    by find_rewrite.
  by apply: Level_enables_RecvLevel; eauto.
- invcs H_st' => //; last by io_handler_cases.
  have H_eq: exists lvo, onwPackets net src dst = Level lvo :: ms by net_handler_cases => //; find_injection; find_rewrite; eexists.
  break_exists_name lvo.
  have H_f: ~ In dst failed'' by net_handler_cases => //; find_injection; find_rewrite.
  invcs H_st => //; first by net_handler_cases.
  set net' := {| onwPackets := _ ; onwState := _ |}.
  have H_hd': head (onwPackets net' src dst) = Some (Level lvo).
    rewrite /net' /=.
    by io_handler_cases => //=; find_rewrite.
  by apply: Level_enables_RecvLevel; eauto.
Qed.

Lemma Tree_RecvFail_enabled_weak_until_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvFail dst src) (hd s) ->
                  weak_until (now (l_enabled lb_step_ordered_failure (RecvFail dst src))) 
                             (now (occurred (RecvFail dst src))) 
                             s.
Proof.
cofix c.
case => /=.
case; case => failed net l tr s H_exec src dst.
case (Label_eq_dec l (RecvFail dst src)) => H_eq H_en.
- find_rewrite.
  exact: W0.
- apply: W_tl; first by [].
  apply: c; first by find_apply_lem_hyp lb_step_execution_invar.
  unfold l_enabled in *.
  unfold enabled in H_en.
  break_exists.
  destruct s as [e s].
  inversion H_exec; subst_max.
  inversion H5; subst.  
  destruct e, evt_a.
  destruct e', evt_a.
  destruct x.
  simpl in *.
  by apply: Tree_lb_step_ordered_failure_RecvFail_enabled; eauto.
Qed.

Lemma Tree_RecvLevel_enabled_weak_until_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvLevel dst src) (hd s) ->
                  weak_until (now (l_enabled lb_step_ordered_failure (RecvLevel dst src))) 
                             (now (occurred (RecvLevel dst src))) 
                             s.
Proof.
cofix c.
case => /=.
case; case => failed net l tr s H_exec src dst.
case (Label_eq_dec l (RecvLevel dst src)) => H_eq H_en.
- find_rewrite.
  exact: W0.
- apply: W_tl; first by [].
  apply: c; first by find_apply_lem_hyp lb_step_execution_invar.
  unfold l_enabled in *.
  unfold enabled in H_en.
  break_exists.
  destruct s as [e s].
  inversion H_exec; subst_max.
  inversion H5; subst.  
  destruct e, evt_a.
  destruct e', evt_a.
  destruct x.
  simpl in *.
  by apply: Tree_lb_step_ordered_failure_RecvLevel_enabled; eauto.
Qed.

Lemma Tree_RecvFail_eventually_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvFail dst src) (hd s) ->
                  eventually (now (occurred (RecvFail dst src))) s.
Proof.
move => s H_exec H_fair src dst H_en.
have H_wu := Tree_RecvFail_enabled_weak_until_occurred H_exec H_en.
apply weak_until_until_or_always in H_wu.
case: H_wu; first exact: until_eventually.
move => H_al.
apply always_continuously in H_al.
apply H_fair in H_al => //.
destruct s as [x s].
by apply always_now in H_al.
Qed.

Lemma Tree_RecvLevel_eventually_occurred :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst, l_enabled lb_step_ordered_failure (RecvLevel dst src) (hd s) ->
                  eventually (now (occurred (RecvLevel dst src))) s.
Proof.
move => s H_exec H_fair src dst H_en.
have H_wu := Tree_RecvLevel_enabled_weak_until_occurred H_exec H_en.
apply weak_until_until_or_always in H_wu.
case: H_wu; first exact: until_eventually.
move => H_al.
apply always_continuously in H_al.
apply H_fair in H_al => //.
destruct s as [x s].
by apply always_now in H_al.
Qed.

Lemma Tree_lb_step_ordered_failure_not_in_failed :
  forall net net' failed failed' lb tr h,
  ~ In h failed ->
  lb_step_ordered_failure (failed, net) lb (failed', net') tr ->
  ~ In h failed'.
Proof.
move => net net' failed failed' lb tr h H_in_f H_step.
by invcs H_step.
Qed.

Lemma Tree_not_in_failed_always : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       forall h, ~ In h (fst (hd s).(evt_a)) ->
       always (now (fun e => ~ In h (fst e.(evt_a)))) s.
Proof.
cofix c.
move => s H_exec.
inversion H_exec => /=.
move => h H_in_f.
apply: Always; first by [].
rewrite /=.
apply: c; first by [].
rewrite /=.
destruct e, e', evt_a, evt_a0.
simpl in *.
by eapply Tree_lb_step_ordered_failure_not_in_failed; eauto.
Qed.

Lemma Tree_lb_step_ordered_failure_Fail_head_add_msg_end : 
  forall net net' failed failed' tr l,
    lb_step_ordered_failure (failed, net) l (failed', net') tr ->
    forall dst src ms, l <> RecvFail dst src ->
    onwPackets net src dst = Fail :: ms ->
    exists ms' : list Msg, onwPackets net' src dst = Fail :: ms ++ ms'.
Proof.
move => net net' failed failed' tr l H_st dst src ms H_neq H_eq.
invcs H_st => //=.
- net_handler_cases => //=.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
- io_handler_cases => //=.
  * case (name_eq_dec h src) => H_dec.
    + subst_max.
      case H_adj: (NSet.mem dst (net.(onwState) src).(adjacent)).
      -- find_apply_lem_hyp NSetFacts.mem_2.
         have H_in: In dst (NSet.elements (adjacent (onwState net src))).
           apply NSet.elements_spec1 in H_adj.
           rewrite /NSet.E.eq in H_adj.
           apply InA_alt in H_adj.
           break_exists.
           break_and.
           by subst_max.
         have H_nd := NSet.elements_spec2w (adjacent (onwState net src)).
         rewrite /NSet.E.eq in H_nd.
         rewrite /level_adjacent NSet.fold_spec /flip /=.
         elim: (NSet.elements (adjacent (onwState net src))) H_in H_nd => /= [|n ns IH] H_in H_nd; first by exists []; rewrite -app_nil_end.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         inversion H_nd; subst_max.
         break_or_hyp.
           rewrite /update2.
           break_if; last by intuition.
           exists [Level (Some 0)].
           have H_not_in: ~ In dst ns.
             move => H_in'.
             contradict H7.
             apply InA_alt.
             by exists dst.
           move {IH H8 H_nd H7}.
           elim: ns H_not_in => /= [|n' ns IH] H_not_in; first by find_rewrite.
           have H_in': ~ In dst ns by auto.
           have H_neq': n' <> dst by auto.
           concludes.
           rewrite /flip /= {2}/level_fold.
           rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
           rewrite collate_app /=.
           rewrite /update2.
           break_if; first by break_and; subst_max.
           by rewrite IH.                          
         concludes.
         concludes.
         break_exists.
         have H_neq': n <> dst.
           move => H_eq'.
           subst_max.
           contradict H7.
           apply InA_alt.
           by exists dst.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H1.
         by exists x.
      -- have H_adj': ~ NSet.In dst (adjacent (onwState net src)).
           move => H_ins.
           find_apply_lem_hyp NSetFacts.mem_1.
           by find_rewrite.
         rewrite /level_adjacent NSet.fold_spec /=.
         have H_in: ~ In dst (NSet.elements (adjacent (onwState net src))).
           move => H_in.
           contradict H_adj'.
           apply NSet.elements_spec1.
           rewrite /NSet.E.eq.
           apply InA_alt.
           exists dst.
           by split.
         elim: (NSet.elements (adjacent (onwState net src))) H_in => /= [|n ns IH] H_in; first by exists []; rewrite -app_nil_end.
         have H_in': ~ In dst ns by auto.
         have H_neq': n <> dst by auto.
         concludes.
         break_exists.
         rewrite /flip /= {2}/level_fold.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H.
         by exists x.
    + rewrite collate_neq //.
      by exists []; rewrite -app_nil_end.
  * case (name_eq_dec h src) => H_dec.
    + subst_max.
      case H_adj: (NSet.mem dst (net.(onwState) src).(adjacent)).
      -- find_apply_lem_hyp NSetFacts.mem_2.
         have H_in: In dst (NSet.elements (adjacent (onwState net src))).
           apply NSet.elements_spec1 in H_adj.
           rewrite /NSet.E.eq in H_adj.
           apply InA_alt in H_adj.
           break_exists.
           break_and.
           by subst_max.
         have H_nd := NSet.elements_spec2w (adjacent (onwState net src)).
         rewrite /NSet.E.eq in H_nd.
         rewrite /level_adjacent NSet.fold_spec /flip /=.
         elim: (NSet.elements (adjacent (onwState net src))) H_in H_nd => /= [|n ns IH] H_in H_nd; first by exists []; rewrite -app_nil_end.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         inversion H_nd; subst_max.
         break_or_hyp.
           rewrite /update2.
           break_if; last by intuition.
           exists [Level (level (adjacent (onwState net src)) (levels (onwState net src)))].
           have H_not_in: ~ In dst ns.
             move => H_in'.
             contradict H7.
             apply InA_alt.
             by exists dst.
           move {IH H8 H_nd H7}.
           elim: ns H_not_in => /= [|n' ns IH] H_not_in; first by find_rewrite.
           have H_in': ~ In dst ns by auto.
           have H_neq': n' <> dst by auto.
           concludes.
           rewrite /flip /= {2}/level_fold.
           rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
           rewrite collate_app /=.
           rewrite /update2.
           break_if; first by break_and; subst_max.
           by rewrite IH.                          
         concludes.
         concludes.
         break_exists.
         have H_neq': n <> dst.
           move => H_eq'.
           subst_max.
           contradict H7.
           apply InA_alt.
           by exists dst.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H1.
         by exists x.
      -- have H_adj': ~ NSet.In dst (adjacent (onwState net src)).
           move => H_ins.
           find_apply_lem_hyp NSetFacts.mem_1.
           by find_rewrite.
         rewrite /level_adjacent NSet.fold_spec /=.
         have H_in: ~ In dst (NSet.elements (adjacent (onwState net src))).
           move => H_in.
           contradict H_adj'.
           apply NSet.elements_spec1.
           rewrite /NSet.E.eq.
           apply InA_alt.
           exists dst.
           by split.
         elim: (NSet.elements (adjacent (onwState net src))) H_in => /= [|n ns IH] H_in; first by exists []; rewrite -app_nil_end.
         have H_in': ~ In dst ns by auto.
         have H_neq': n <> dst by auto.
         concludes.
         break_exists.
         rewrite /flip /= {2}/level_fold.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H0.
         by exists x.
    + rewrite collate_neq //.
      by exists []; rewrite -app_nil_end.
  * by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
Qed.

Lemma Tree_lb_step_ordered_failure_Level_head_add_msg_end : 
  forall net net' failed failed' tr l,
    lb_step_ordered_failure (failed, net) l (failed', net') tr ->
    forall dst src lvo ms, l <> RecvLevel dst src ->
    onwPackets net src dst = Level lvo :: ms ->
    exists ms' : list Msg, onwPackets net' src dst = Level lvo :: ms ++ ms'.
Proof.
move => net net' failed failed' tr l H_st dst src lvo ms H_neq H_eq.
invcs H_st => //=.
- net_handler_cases => //=.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst; find_rewrite.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
  * exists [].
    rewrite /update2.
    break_if; first by break_and; subst_max; intuition.
    by rewrite -app_nil_end.
- io_handler_cases => //=.
  * case (name_eq_dec h src) => H_dec.
    + subst_max.
      case H_adj: (NSet.mem dst (net.(onwState) src).(adjacent)).
      -- find_apply_lem_hyp NSetFacts.mem_2.
         have H_in: In dst (NSet.elements (adjacent (onwState net src))).
           apply NSet.elements_spec1 in H_adj.
           rewrite /NSet.E.eq in H_adj.
           apply InA_alt in H_adj.
           break_exists.
           break_and.
           by subst_max.
         have H_nd := NSet.elements_spec2w (adjacent (onwState net src)).
         rewrite /NSet.E.eq in H_nd.
         rewrite /level_adjacent NSet.fold_spec /flip /=.
         elim: (NSet.elements (adjacent (onwState net src))) H_in H_nd => /= [|n ns IH] H_in H_nd; first by exists []; rewrite -app_nil_end.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         inversion H_nd; subst_max.
         break_or_hyp.
           rewrite /update2.
           break_if; last by intuition.
           exists [Level (Some 0)].
           have H_not_in: ~ In dst ns.
             move => H_in'.
             contradict H7.
             apply InA_alt.
             by exists dst.
           move {IH H8 H_nd H7}.
           elim: ns H_not_in => /= [|n' ns IH] H_not_in; first by find_rewrite.
           have H_in': ~ In dst ns by auto.
           have H_neq': n' <> dst by auto.
           concludes.
           rewrite /flip /= {2}/level_fold.
           rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
           rewrite collate_app /=.
           rewrite /update2.
           break_if; first by break_and; subst_max.
           by rewrite IH.
         concludes.
         concludes.
         break_exists.
         have H_neq': n <> dst.
           move => H_eq'.
           subst_max.
           contradict H7.
           apply InA_alt.
           by exists dst.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H1.
         by exists x.
      -- have H_adj': ~ NSet.In dst (adjacent (onwState net src)).
           move => H_ins.
           find_apply_lem_hyp NSetFacts.mem_1.
           by find_rewrite.
         rewrite /level_adjacent NSet.fold_spec /=.
         have H_in: ~ In dst (NSet.elements (adjacent (onwState net src))).
           move => H_in.
           contradict H_adj'.
           apply NSet.elements_spec1.
           rewrite /NSet.E.eq.
           apply InA_alt.
           exists dst.
           by split.
         elim: (NSet.elements (adjacent (onwState net src))) H_in => /= [|n ns IH] H_in; first by exists []; rewrite -app_nil_end.
         have H_in': ~ In dst ns by auto.
         have H_neq': n <> dst by auto.
         concludes.
         break_exists.
         rewrite /flip /= {2}/level_fold.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H.
         by exists x.
    + rewrite collate_neq //.
      by exists []; rewrite -app_nil_end.
  * case (name_eq_dec h src) => H_dec.
    + subst_max.
      case H_adj: (NSet.mem dst (net.(onwState) src).(adjacent)).
      -- find_apply_lem_hyp NSetFacts.mem_2.
         have H_in: In dst (NSet.elements (adjacent (onwState net src))).
           apply NSet.elements_spec1 in H_adj.
           rewrite /NSet.E.eq in H_adj.
           apply InA_alt in H_adj.
           break_exists.
           break_and.
           by subst_max.
         have H_nd := NSet.elements_spec2w (adjacent (onwState net src)).
         rewrite /NSet.E.eq in H_nd.
         rewrite /level_adjacent NSet.fold_spec /flip /=.
         elim: (NSet.elements (adjacent (onwState net src))) H_in H_nd => /= [|n ns IH] H_in H_nd; first by exists []; rewrite -app_nil_end.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         inversion H_nd; subst_max.
         break_or_hyp.
           rewrite /update2.
           break_if; last by intuition.
           exists [Level (level (adjacent (onwState net src)) (levels (onwState net src)))].
           have H_not_in: ~ In dst ns.
             move => H_in'.
             contradict H7.
             apply InA_alt.
             by exists dst.
           move {IH H8 H_nd H7}.
           elim: ns H_not_in => /= [|n' ns IH] H_not_in; first by find_rewrite.
           have H_in': ~ In dst ns by auto.
           have H_neq': n' <> dst by auto.
           concludes.
           rewrite /flip /= {2}/level_fold.
           rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
           rewrite collate_app /=.
           rewrite /update2.
           break_if; first by break_and; subst_max.
           by rewrite IH.                          
         concludes.
         concludes.
         break_exists.
         have H_neq': n <> dst.
           move => H_eq'.
           subst_max.
           contradict H7.
           apply InA_alt.
           by exists dst.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H1.
         by exists x.
      -- have H_adj': ~ NSet.In dst (adjacent (onwState net src)).
           move => H_ins.
           find_apply_lem_hyp NSetFacts.mem_1.
           by find_rewrite.
         rewrite /level_adjacent NSet.fold_spec /=.
         have H_in: ~ In dst (NSet.elements (adjacent (onwState net src))).
           move => H_in.
           contradict H_adj'.
           apply NSet.elements_spec1.
           rewrite /NSet.E.eq.
           apply InA_alt.
           exists dst.
           by split.
         elim: (NSet.elements (adjacent (onwState net src))) H_in => /= [|n ns IH] H_in; first by exists []; rewrite -app_nil_end.
         have H_in': ~ In dst ns by auto.
         have H_neq': n <> dst by auto.
         concludes.
         break_exists.
         rewrite /flip /= {2}/level_fold.
         rewrite (@fold_left_level_fold_eq Tree_TreeMsg) /=.
         rewrite collate_app /=.
         rewrite /update2.
         break_if; first by break_and.
         rewrite H0.
         by exists x.
    + rewrite collate_neq //.
      by exists []; rewrite -app_nil_end.
  * by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
- by exists []; rewrite -app_nil_end.
Qed.

Lemma Tree_Fail_eventually_remove_head :
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  forall ms, onwPackets (snd (evt_a (hd s))) src dst = Fail :: ms ->
  eventually (now (fun e => exists ms', onwPackets (snd (evt_a e)) src dst = ms ++ ms')) s.
Proof.
move => s H_exec H_fair src dst H_f ms H_eq.
have H_hd: head (onwPackets (snd (evt_a (hd s))) src dst) = Some Fail by find_rewrite.
have H_en := Fail_enables_RecvFail _ _ _ _ H_f H_hd.
have H_ev: eventually (now (occurred (RecvFail dst src))) s.
  apply (@Tree_RecvFail_eventually_occurred _ H_exec H_fair src dst).
  rewrite /l_enabled.
  by destruct evt_a.
have H_ex: exists ms', onwPackets (snd (evt_a (hd s))) src dst = Fail :: ms ++ ms' by exists []; rewrite app_nil_r.
have H_al := Tree_not_in_failed_always H_exec _ H_f.
have H_wu := @Tree_RecvFail_enabled_weak_until_occurred _ H_exec src dst.
move: H_wu.
set le := l_enabled _ _ _.
have H_le: le by rewrite /le /l_enabled; destruct evt_a.
move => H_wu.
concludes.  
move {H_eq H_f H_hd H_en H_le le}.
elim: H_ev H_exec H_fair H_ex H_al H_wu.
* case; case; case => /= failed net l tr.
  case; case; case => /= failed' net' l' tr'.
  case; case; case => /= failed'' net'' l'' tr'' s0 H_occ H_exec H_fair H_ex H_al H_wu.
  apply: E_next.
  apply: E0.
  rewrite /=.
  rewrite /occurred /= in H_occ.
  subst_max.
  inversion H_exec; subst_max.
  break_exists_name ms'.
  exists ms'.
  simpl in *.
  invcs H2; last by io_handler_cases.
  net_handler_cases => //=. 
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
* case; case => failed net l tr.
  case; case; case => failed' net' l' tr'.
  case; case; case => failed'' net'' l'' tr'' s0 H_ev IH H_exec H_fair H_ex H_al H_wu.
  simpl in *.
  break_exists_name ms'.
  case (Label_eq_dec l (RecvFail dst src)) => H_eq.
  + subst_max.
    apply E_next.
    apply E0.
    inversion H_exec; subst_max.
    simpl in *.
    exists ms'.
    invcs H2; last by io_handler_cases.
    net_handler_cases => //=. 
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
  + apply E_next.
    apply IH.
    -- by find_apply_lem_hyp lb_step_execution_invar.
    -- by find_apply_lem_hyp weak_local_fairness_invar.
    -- inversion H_exec; subst_max.
       simpl in *.
       have H_add := Tree_lb_step_ordered_failure_Fail_head_add_msg_end H2 H_eq H_ex.
       break_exists.
       rewrite app_assoc_reverse in H.
       by exists (ms' ++ x).
    -- by find_apply_lem_hyp always_invar.
    -- find_apply_lem_hyp weak_until_Cons.
       simpl in *.
       rewrite /occurred in H_wu.
       break_or_hyp; simpl in *; last by intuition.
       by rewrite H in H_eq.
Qed.

Lemma Tree_Level_eventually_remove_head :
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  forall lvo ms, onwPackets (snd (evt_a (hd s))) src dst = Level lvo :: ms ->
  eventually (now (fun e => exists ms', onwPackets (snd (evt_a e)) src dst = ms ++ ms')) s.
Proof.
move => s H_exec H_fair src dst H_f lvo ms H_eq.
have H_hd: head (onwPackets (snd (evt_a (hd s))) src dst) = Some (Level lvo) by find_rewrite.
have H_en := Level_enables_RecvLevel _ _ _ _ H_f H_hd.
have H_ev: eventually (now (occurred (RecvLevel dst src))) s.
  apply (@Tree_RecvLevel_eventually_occurred _ H_exec H_fair src dst).
  rewrite /l_enabled.
  by destruct evt_a.
have H_ex: exists ms', onwPackets (snd (evt_a (hd s))) src dst = Level lvo :: ms ++ ms' by exists []; rewrite app_nil_r.
have H_al := Tree_not_in_failed_always H_exec _ H_f.
have H_wu := @Tree_RecvLevel_enabled_weak_until_occurred _ H_exec src dst.
move: H_wu.
set le := l_enabled _ _ _.
have H_le: le by rewrite /le /l_enabled; destruct evt_a.
move => H_wu.
concludes.  
move {H_eq H_f H_hd H_en H_le le}.
elim: H_ev H_exec H_fair H_ex H_al H_wu.
* case; case; case => /= failed net l tr.
  case; case; case => /= failed' net' l' tr'.
  case; case; case => /= failed'' net'' l'' tr'' s0 H_occ H_exec H_fair H_ex H_al H_wu.
  apply: E_next.
  apply: E0.
  rewrite /=.
  rewrite /occurred /= in H_occ.
  subst_max.
  inversion H_exec; subst_max.
  break_exists_name ms'.
  exists ms'.
  simpl in *.
  invcs H2; last by io_handler_cases.
  net_handler_cases => //=.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
  + find_injection; subst_max.
    find_rewrite.
    find_injection.
    rewrite /update2.
    by break_if; intuition.
* case; case => failed net l tr.
  case; case; case => failed' net' l' tr'.
  case; case; case => failed'' net'' l'' tr'' s0 H_ev IH H_exec H_fair H_ex H_al H_wu.
  simpl in *.
  break_exists_name ms'.
  case (Label_eq_dec l (RecvLevel dst src)) => H_eq.
  + subst_max.
    apply E_next.
    apply E0.
    inversion H_exec; subst_max.
    simpl in *.
    exists ms'.
    invcs H2; last by io_handler_cases.
    net_handler_cases => //=. 
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
    -- find_injection; subst_max.
       find_rewrite.
       find_injection.
       rewrite /update2.
       by break_if; intuition.
  + apply E_next.
    apply IH.
    -- by find_apply_lem_hyp lb_step_execution_invar.
    -- by find_apply_lem_hyp weak_local_fairness_invar.
    -- inversion H_exec; subst_max.
       simpl in *.
       have H_add := Tree_lb_step_ordered_failure_Level_head_add_msg_end H2 H_eq H_ex.
       break_exists.
       rewrite app_assoc_reverse in H.
       by exists (ms' ++ x).
    -- by find_apply_lem_hyp always_invar.
    -- find_apply_lem_hyp weak_until_Cons.
       simpl in *.
       rewrite /occurred in H_wu.
       break_or_hyp; simpl in *; last by intuition.
       by rewrite H in H_eq.
Qed.

Lemma Tree_msg_eventually_remove_head :
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  forall m ms, onwPackets (snd (evt_a (hd s))) src dst = m :: ms ->
  eventually (now (fun e => exists ms', onwPackets (snd (evt_a e)) src dst = ms ++ ms')) s.
Proof.
move => s H_exec H_fai src dst H_in.
case.
- move => ms H_eq.
  by apply: Tree_Fail_eventually_remove_head; eauto.
- move => ms H_eq.
  by apply: Tree_Level_eventually_remove_head; eauto.
Qed.

Lemma Tree_msg_in_eventually_first : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  forall m, In m (onwPackets (snd (evt_a (hd s))) src dst) ->
  eventually (now (fun e => head (onwPackets (snd (evt_a e)) src dst) = Some m)) s.
Proof.
move => s H_exec H_fair src dst H_f m H_in.
find_apply_lem_hyp in_split.
break_exists_name l1.
break_exists_name l2.
elim: l1 s H_exec H_fair l2 H_in H_f => /=.
- case; case; case => failed net lb tr s H_exec H_fair l2.
  rewrite /= => H_eq H_f.
  apply: E0.
  by rewrite /= H_eq.
- move => m' l /= IH.
  case; case; case => /= failed net lb tr s.
  set s' := Cons _ _.
  move => H_exec H_fair l2 H_eq H_f.
  have H_ev := Tree_msg_eventually_remove_head H_exec H_fair _ _ H_f H_eq.
  have H_al := Tree_not_in_failed_always H_exec _ H_f.
  simpl in *.
  elim: H_ev H_exec H_fair H_al.
  * case; case; case => /= failed' net' lb' tr' s0 H_eq' H_exec H_fair H_al.
    break_exists.
    rewrite app_assoc_reverse -app_comm_cons in H.
    apply always_now in H_al.
    by apply: IH => //=; eauto.
  * case; case => /= failed' net' lb' tr' s0 H_ev IH' H_exec H_fair H_al.
    apply: E_next.
    apply IH'.
    + by find_apply_lem_hyp lb_step_execution_invar.
    + by find_apply_lem_hyp weak_local_fairness_invar.
    + by find_apply_lem_hyp always_invar.
Qed.

Lemma Tree_Fail_in_eventually_enabled : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  In Fail (onwPackets (snd (evt_a (hd s))) src dst) ->
  eventually (now (l_enabled lb_step_ordered_failure (RecvFail dst src))) s.
Proof.
move => s H_exec H_fair src dst H_f H_in.
have H_ev := Tree_msg_in_eventually_first H_exec H_fair _ _ H_f _ H_in.
have H_al := Tree_not_in_failed_always H_exec _ H_f.
move: H_al H_ev.
apply: eventually_monotonic.
- move => e s0 H_al.
  by find_apply_lem_hyp always_invar.
- case; case; case => failed net l tr s' H_eq.
  rewrite /l_enabled.
  simpl in *.
  apply: Fail_enables_RecvFail => //.
  by find_apply_lem_hyp always_now.
Qed.

Lemma Tree_Level_in_eventually_enabled : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  forall src dst, ~ In dst (fst (evt_a (hd s))) ->
  forall lvo, In (Level lvo) (onwPackets (snd (evt_a (hd s))) src dst) ->
  eventually (now (l_enabled lb_step_ordered_failure (RecvLevel dst src))) s.
Proof.
move => s H_exec H_fair src dst H_f lvo H_in.
have H_ev := Tree_msg_in_eventually_first H_exec H_fair _ _ H_f _ H_in.
have H_al := Tree_not_in_failed_always H_exec _ H_f.
move: H_al H_ev.
apply: eventually_monotonic.
- move => e s0 H_al.
  by find_apply_lem_hyp always_invar.
- case; case; case => failed net l tr s' H_eq.
  rewrite /l_enabled.
  simpl in *.
  apply: Level_enables_RecvLevel => //.
  by find_apply_lem_hyp always_now.
Qed.

Lemma Tree_FailureRecorder_lb_step_execution_pt_map : forall s,
  lb_step_execution lb_step_ordered_failure s ->
  lb_step_execution lb_step_ordered_failure (map pt_map_onet_event s).
Proof.
apply: lb_step_execution_lb_step_ordered_failure_pt_map_onet_infseq.
exact: FR.Label_eq_dec.
Qed.
 
Lemma Tree_FailureRecorder_pt_map_onet_hd_step_ordered_failure_star_always : 
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       always (now (event_step_star step_ordered_failure step_ordered_failure_init)) (map pt_map_onet_event s).
Proof.
apply: pt_map_onet_hd_step_ordered_failure_star_always.
exact: FR.Label_eq_dec.
Qed.

Lemma Tree_lb_step_ordered_failure_enabled_weak_fairness_pt_map_onet_eventually :
forall l, tot_map_label l <> FR.Tau ->
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  l_enabled lb_step_ordered_failure (tot_map_label l) (pt_map_onet_event (hd s)) ->
  eventually (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
case => //= dst src H_neq {H_neq}.
case => [[[failed net] l]] tr s H_exec H_fair H_en.
rewrite /l_enabled /enabled /= map_id in H_en.
break_exists.
destruct x as [failed' net'].
invcs H => //.
unfold id in *.
rewrite /runGenHandler /= in H7.
FR.net_handler_cases.
find_injection.
simpl in *.
move {H6}.
have H_in: In Fail (onwPackets net from to).
  apply: in_pt_map_msgs_in_msg.
  - by case => //; case.
  - by eexists.
  - by rewrite H4; left.
exact: Tree_Fail_in_eventually_enabled.
Qed.

Lemma Tree_pt_map_onet_tot_map_label_event_state_strong_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       strong_local_fairness lb_step_ordered_failure label_silent s ->
       strong_local_fairness lb_step_ordered_failure label_silent (map pt_map_onet_event s).
Proof.
apply: pt_map_onet_tot_map_label_event_strong_local_fairness.
- case; first by exists Tau.
  move => dst src.
  by exists (RecvFail dst src).
- move => l H_neq s H_exec H_fair.
  find_apply_lem_hyp strong_local_fairness_weak.
  exact: Tree_lb_step_ordered_failure_enabled_weak_fairness_pt_map_onet_eventually.  
Qed.

Lemma Tree_pt_map_onet_always_enabled_continuously :
forall l : label,
  tot_map_label l <> label_silent ->
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  always (now (l_enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) ->
  continuously (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
case => //= src dst H_neq.
case; case; case => /= failed net l tr s H_exec H_fair H_al.
find_rewrite_lem map_Cons.
find_apply_lem_hyp always_Cons.
break_and.
rewrite /= /l_enabled /enabled /= map_id /id in H.
break_exists_name a.
break_exists_name tr'.
destruct a as [failed' net'].
invcs H; last by FR.io_handler_cases.
unfold id in *.
FR.net_handler_cases => //.
simpl in *.
find_injection.
move: H5.
set ptm := pt_map_msgs _.
move => H_eq_pt.
have H_in_pt: In FR.Fail ptm by find_rewrite; left.
have H_in: In Fail (onwPackets net from to).
  move: H_in_pt.
  apply: in_pt_map_msgs_in_msg => //.
  by case => //=; case.
unfold ptm in *.
move {ptm H_in_pt}.
have H_ev := Tree_msg_in_eventually_first H_exec H_fair _ _ H6 _ H_in.
have H_al := Tree_not_in_failed_always H_exec to H6.
simpl in *.
find_apply_lem_hyp always_invar.
move {H_fair H7 H_in H6}.
Admitted.

Lemma Tree_pt_map_onet_tot_map_label_event_state_weak_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       weak_local_fairness lb_step_ordered_failure label_silent (map pt_map_onet_event s).
Proof.
move => s H_star H_exec H_fair.
apply: pt_map_onet_tot_map_label_event_state_weak_local_fairness => //.
- case; first by exists Tau.
  move => dst src.
  by exists (RecvFail dst src).
- exact: Tree_pt_map_onet_always_enabled_continuously.
Qed.

Lemma Tree_lb_step_ordered_failure_continuously_no_fail :
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall src dst,
       ~ In dst (fst (hd s).(evt_a)) ->
       continuously (now (fun e => ~ In Fail ((snd e.(evt_a)).(onwPackets) src dst))) s.
Proof.
move => s H_exec H_fair src dst H_in_f.
have H_exec_map := Tree_FailureRecorder_lb_step_execution_pt_map H_exec.
have H_w := Tree_pt_map_onet_tot_map_label_event_state_weak_local_fairness H_exec H_fair.
have H_map := FR.Failure_lb_step_ordered_failure_continuously_no_fail H_exec_map H_w src dst.
move: H_map.
set ind := ~ In _ _.
move => H_map.
have H_ind: ind.
  move => H_ind.
  case: H_in_f.
  destruct s as [e s].
  simpl in *.
  by rewrite map_id in H_ind.
concludes.
move: H_map.
apply continuously_map_conv.
- exact: extensional_now.
- exact: extensional_now.
- case => /= e s0.
  rewrite /id /=.
  move => H_in H_in'.
  case: H_in.
  move: H_in'.
  exact: in_msg_pt_map_msgs.
Qed.

Lemma Tree_lb_step_ordered_failure_continuously_adj_not_failed : 
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       forall n n',
       ~ In n (fst (hd s).(evt_a)) ->
       continuously (now (fun e => 
         NSet.In n' ((snd e.(evt_a)).(onwState) n).(adjacent) -> 
         ~ In n' (fst e.(evt_a)) /\ adjacent_to n' n)) s.
Proof.
move => s H_star H_exec H_fair src dst H_in_f.
have H_exec_map := Tree_FailureRecorder_lb_step_execution_pt_map H_exec.
have H_w := Tree_pt_map_onet_tot_map_label_event_state_weak_local_fairness H_exec H_fair.
have H_map := FR.Failure_lb_step_ordered_failure_continuously_adj_not_failed _ H_exec_map H_w src dst.
move: H_map.
set ind := ~ In _ _.
set eex := event_step_star _ _ _.
move => H_map.
have H_ind: ind.
  move => H_ind.
  case: H_in_f.
  destruct s as [e s].
  simpl in *.
  by rewrite map_id in H_ind.
have H_eex: eex.
  rewrite /eex.
  destruct s as [e s].
  exact: pt_map_onet_hd_step_ordered_failure_star.
concludes.
concludes.
move: H_map.
apply continuously_map_conv.
- exact: extensional_now.
- exact: extensional_now.
- case => /= e s0.
  rewrite /id map_id /=.
  move => H_in H_in'.
  by concludes.
Qed.

Inductive root_path_length (failed : list name) : name -> nat -> Prop :=
| root_path_length_self : forall n, 
    ~ In n failed -> 
    root n -> 
    root_path_length failed n 0
| root_path_length_proxy : forall n n' k,
    root_path_length failed n k ->
    ~ In n' failed ->
    adjacent_to n n' ->
    root_path_length failed n' (S k).

Definition min_root_path_length (failed : list name) (n : name) (k : nat) : Prop :=
root_path_length failed n k /\ (forall k', root_path_length failed n k' -> k <= k').

Lemma root_path_length_exists_root : 
  forall failed n k,
    root_path_length failed n k ->
    exists r, ~ In r failed /\ root r.
Proof.
move => failed n k.
elim => //.
move => r H_in H_eq.
by exists r.
Qed.

Lemma root_path_length_not_failed : 
  forall failed n k,
  root_path_length failed n k ->
  ~ In n failed.
Proof. by move => failed n k; case. Qed.

Lemma min_root_path_length_not_adjacent_plus_2 : 
  forall failed n k n' k',
  min_root_path_length failed n k ->
  min_root_path_length failed n' k' ->
  k' >= S (S k) ->
  ~ adjacent_to n n'.
Proof.
move => failed n k n' k' H_min H_min' H_ge H_adj.
unfold min_root_path_length in *.
repeat break_and.
have H_r: root_path_length failed n' (S k).
  apply: root_path_length_proxy; eauto.
  by apply: root_path_length_not_failed; eauto.
have H_r' := H0 _ H_r.
by omega.
Qed.

End Tree.
