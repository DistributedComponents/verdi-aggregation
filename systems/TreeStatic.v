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

Require Import TreeAux.
Require Import FailureRecorderStatic.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

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

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition RootNetHandler (src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Level _ => nop 
| Fail => 
  put {| adjacent := NSet.remove src st.(adjacent) ;
         broadcast := st.(broadcast) ;
         levels := st.(levels) |}
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Level None =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.remove src st.(levels))) then
    put {| adjacent := st.(adjacent) ;           
           broadcast := st.(broadcast) ;
           levels := NMap.remove src st.(levels) |}
  else 
    put {| adjacent := st.(adjacent) ;           
           broadcast := true ;
           levels := NMap.remove src st.(levels) |}
| Level (Some lv') =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.add src lv' st.(levels))) then
    put {| adjacent := st.(adjacent) ;
           broadcast := st.(broadcast) ;
           levels := NMap.add src lv' st.(levels) |}
  else
    put {| adjacent := st.(adjacent) ;
           broadcast := true ;
           levels := NMap.add src lv' st.(levels) |}
| Fail => 
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels))) then
    put {| adjacent := NSet.remove src st.(adjacent) ;
           broadcast := st.(broadcast) ;
           levels := NMap.remove src st.(levels) |}
  else
    put {| adjacent := NSet.remove src st.(adjacent) ;
           broadcast := true ;
           levels := NMap.remove src st.(levels) |}
end.

Definition NetHandler (me src : name) (msg : Msg) : Handler Data :=
if root_dec me then RootNetHandler src msg 
else NonRootNetHandler me src msg.

Instance Tree_TreeMsg : TreeMsg := 
  {
    tree_msg := Msg ;
    tree_level := Level
  }.

Definition send_level_fold (lvo : option lv) (n : name) (res : Handler Data) : Handler Data :=
send (n, Level lvo) ;; res.

Definition send_level_adjacent (lvo : option lv) (fs : NS) : Handler Data :=
NSet.fold (send_level_fold lvo) fs nop.

Definition RootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Broadcast => 
  when st.(broadcast)
  (send_level_adjacent (Some 0) st.(adjacent) ;;
   put {| adjacent := st.(adjacent);
          broadcast := false;
          levels := st.(levels) |})
| LevelRequest => 
  write_output (LevelResponse (Some 0))
end.

Definition NonRootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Broadcast =>
  when st.(broadcast)
  (send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent) ;; 
  put {| adjacent := st.(adjacent);
         broadcast := false;
         levels := st.(levels) |})
| LevelRequest =>   
  write_output (LevelResponse (level st.(adjacent) st.(levels)))
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler i 
else NonRootIOHandler i.

Instance Tree_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Tree_MultiParams : MultiParams Tree_BaseParams :=
  {
    name := name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := name_eq_dec ;
    nodes := nodes ;
    all_names_nodes := all_names_nodes ;
    no_dup_nodes := no_dup_nodes ;
    init_handlers := InitData ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

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
    NetHandler dst src m st = (tt, os, st', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (root dst /\ msg = Fail /\ 
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ 
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg; monad_unfold.
- case root_dec => /= H_dec.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    by left.
  * case olv_eq_dec => /= H_dec' H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
      by right; left.
    by right; right; left.
- case root_dec => /= H_dec olv_msg.
    move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; left.
    split => //.
    by exists olv_msg.
  case H_olv_dec: olv_msg => [lv_msg|]; case olv_eq_dec => /= H_dec' H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
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
    IOHandler h i d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma send_level_fold_app :
  forall ns st olv nm,
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, nm)) st) = 
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, [])) st) ++ nm.
Proof.
elim => //=.
move => n ns IH st olv nm.
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
forall ns nm olv st,
fst
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = tt.
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma send_level_adjacent_fst_fst_eq : 
forall fs olv st,
  fst (fst (fst (send_level_adjacent olv fs st))) = tt.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite fst_fst_fst_tt_send_level_fold.
Qed.

Lemma snd_fst_fst_out_send_level_fold : 
forall ns nm olv st,
snd
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = [].
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma snd_fst_st_send_level_fold : 
forall ns nm olv st,
snd (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st)) = st.
Proof.
elim => //=.
move => n ns IH nm olv st.
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
  send_level_adjacent olv fs st = (tt, [], st, level_adjacent olv fs).
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
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) ->
      (root h /\ i = Broadcast /\ st.(broadcast) = true /\
       st'.(adjacent) = st.(adjacent) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (Some 0) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\ st.(broadcast) = true /\
       st'.(adjacent) = st.(adjacent) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (i = Broadcast /\ st.(broadcast) = false /\
       st' = st /\
       out = [] /\ ms = []) \/
      (root h /\ i = LevelRequest /\
       st' = st /\
       out = [LevelResponse (Some 0)] /\ ms = []) \/
      (~ root h /\ i = LevelRequest /\
       st' = st /\
       out = [LevelResponse (level st.(adjacent) st.(levels))] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler /RootIOHandler /NonRootIOHandler.
case: i => [|]; monad_unfold.
- case root_dec => /= H_dec H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left.
  by right; right; right; right.
- case root_dec => /= H_dec; case H_b: broadcast => /=.
  * left.
    repeat break_let.
    injection Heqp => H_ms H_st H_out H_tt.
    subst.
    injection Heqp2 => H_ms H_st H_out H_tt.
    subst.
    injection H => H_ms H_st H_out H_tt.
    subst.
    rewrite /=.
    have H_eq := send_level_adjacent_eq st.(adjacent) (Some 0) st.
    rewrite Heqp5 in H_eq.
    injection H_eq => H_eq_ms H_eq_st H_eq_o H_eq_tt.
    rewrite H_eq_ms H_eq_o.
    by rewrite app_nil_l -2!app_nil_end.
  * right; right; left.
    injection H => H_ms H_st H_o H_tt.
    by rewrite H_st H_o H_ms.
  * right; left.
    repeat break_let.
    injection Heqp => H_ms H_st H_out H_tt.
    subst.
    injection Heqp2 => H_ms H_st H_out H_tt.
    subst.
    injection H => H_ms H_st H_out H_tt.
    subst.
    rewrite /=.
    have H_eq := send_level_adjacent_eq st.(adjacent) (level st.(adjacent) st.(levels)) st.
    rewrite Heqp5 in H_eq.
    injection H_eq => H_eq_ms H_eq_st H_eq_o H_eq_tt.
    rewrite H_eq_ms H_eq_o.
    by rewrite app_nil_l -2!app_nil_end.
  * right; right; left.
    injection H => H_ms H_st H_o H_tt.
    by rewrite H_st H_o H_ms.
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
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //= ; simpl in *;
    update_destruct_max_simplify; repeat find_rewrite; auto.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=; simpl in *;
    update_destruct_max_simplify; repeat find_rewrite; auto.
- intros. simpl in *.
  eauto.
Qed.

Ltac induct_step :=
  match goal with
  | H : step_ordered_failure_star _ _ _ |- _ =>
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
Lemma Tree_root_levels_empty' :
  forall net failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
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
  step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
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
 step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
 forall (n : name), ~ In n failed ->
 forall (n' : name) lvo', before_all (Level lvo') Fail (onet.(onwPackets) n' n).
Proof.
Admitted.

(* in_queue_status_then_new *)
Lemma Tree_level_msg_dst_adjacent_src : 
  forall onet failed tr, 
    step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
    forall n, ~ In n failed ->
     forall n' lvo', In (Level lvo') (onet.(onwPackets) n' n) ->
     NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
Admitted.

(* bfs_net_ok_notins_levels_bot *)
Lemma Tree_notins_levels_bot :
  forall net failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
  forall n, ~ In n failed ->
  forall n', ~ NSet.In n' (net.(onwState) n).(adjacent) ->
  NMap.find n' (net.(onwState) n).(levels) = None.
Proof.
Admitted.

(* bfs_net_ok_root_status_in_queue *)
Lemma Tree_root_incoming_level_0 :
  forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed -> 
    root n ->
    forall n' lvo', In (Level lvo') (net.(onwPackets) n n') ->
    lvo' = Some 0.
Proof.
Admitted.

Lemma Tree_root_broadcast_false :
    forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
   root n ->
   (net.(onwState) n).(broadcast) = false.
Proof.
Admitted.

(* bfs_net_ok_notin_adj_not_sent_status *)
Lemma Tree_notin_adjacent_not_sent_level :
  forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
    forall n', ~ NSet.In n' (net.(onwState) n).(adjacent) ->
    forall lvo', ~ In (Level lvo') (net.(onwPackets) n n').
Proof.
Admitted.

(* bfs_net_ok_notin_adj_find_none *)
Lemma Tree_notin_adjacent_find_none :
  forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
    forall n, ~ In n failed ->
    forall n', ~ In n' failed ->
    ~ NSet.In n' (net.(onwState) n).(adjacent) ->
    NMap.find n (net.(onwState) n').(levels) = None.
Proof.
Admitted.

(* bfs_net_ok_root_have_level *)
Lemma Tree_root_have_level :
  forall net failed tr,
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
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
    step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> 
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
   step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall lv', level (net.(onwState) n).(adjacent) (net.(onwState) n).(levels) = Some lv' ->
   lv' > 0.
Proof.
Admitted.

Lemma Tree_levels_some_in_adj :
 forall net failed tr,
   step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n' lv', NMap.find n' (net.(onwState) n).(levels) = Some lv' ->
   NSet.In n' (net.(onwState) n).(adjacent).
Proof.
Admitted.

(* status_0_in_queue_then_root *)
Lemma Tree_level_0_incoming_then_root : 
   forall net failed tr,
   step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n', In (Level (Some 0)) (net.(onwPackets) n' n) ->
   root n'.
Proof.
Admitted.

Lemma Tree_find_level_0_then_root :
   forall net failed tr,
   step_ordered_failure_star step_ordered_failure_init (failed, net) tr ->
   forall n, ~ In n failed ->
   forall n', NMap.find n' (net.(onwState) n).(levels) = Some 0 ->
   root n'.
Proof.
Admitted.

End Tree.
