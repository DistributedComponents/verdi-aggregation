(* merge sent and received into "balance" map? *)

(* at recovery time, send new to all existing neighbors *)
(* handle problem with unprocessed fail messages for recovery *)

(* higher-level language like ott/lem for protocols that exports to handlers? *)

(* path to liveness properties:

- handler monad must be able to output labels, e.g., return broadcast_level

- all labels must be decorated with the involved node names by the semantics

- labels must be removed at extraction time

- is strong local liveness warranted in practice? how can extraction guarantee it?
*)

(* must use rev 6b77fae28fb5f669861a7b2782e35fcd0fe1fbfa of https://scm.gforge.inria.fr/anonscm/git/coq-contribs/aac-tactics.git *)
Require Import Verdi.
Require Import HandlerMonad.
Require Import NameOverlay.

Require Import TotalMapSimulations.
Require Import PartialMapSimulations.
Require Import PartialExtendedMapSimulations.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import Sorting.Permutation.

Require Import AAC_tactics.AAC.

Require Import AggregationAux.
Require Import FailureRecorderStatic.

Set Implicit Arguments.

Module Aggregation (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import CFG : CommutativeFinGroup) (Import ANT : AdjacentNameType NT).

Module A := Adjacency NT NOT NSet ANT.
Import A.

Module FR := FailureRecorder NT NOT NSet ANT.

Module AX := AAux NT NOT NSet NOTC NMap CFG.
Import AX.

Import GroupScope.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Inductive Msg : Type := 
| Aggregate : m -> Msg
| Fail : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Input : Type :=
| Local : m -> Input
| SendAggregate : name -> Input
| AggregateRequest : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: name_eq_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data := mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : NS ; 
  sent : NM ; 
  received : NM 
}.

Definition InitData (n : name) := 
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     sent := init_map (adjacency n nodes) ;
     received := init_map (adjacency n nodes) |}.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match NMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := NMap.add src (m_src * m_msg) st.(received) |}                                                           
  end
| Fail => 
  match NMap.find src st.(sent), NMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>    
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 ;
           adjacent := NSet.remove src st.(adjacent) ;
           sent := NMap.remove src st.(sent) ;
           received := NMap.remove src st.(received) |}           
  | _, _ => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := NSet.remove src st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) |}
  end
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg ;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1 ;
         adjacent := st.(adjacent) ;
         sent := st.(sent) ;
         received := st.(received) |}
| SendAggregate dst => 
  when (NSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match NMap.find dst st.(sent) with
   | None => nop
   | Some m_dst =>        
     put {| local := st.(local) ;
            aggregate := 1 ;
            adjacent := st.(adjacent) ;
            sent := NMap.add dst (m_dst * st.(aggregate)) st.(sent) ;
            received := st.(received) |} ;; 
     send (dst, (Aggregate st.(aggregate)))
   end)
| Query =>
  write_output (AggregateResponse st.(aggregate))
end.

Instance Aggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance Aggregation_MultiParams : MultiParams Aggregation_BaseParams :=
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

Instance Aggregation_NameOverlayParams : NameOverlayParams Aggregation_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance Aggregation_FailMsgParams : FailMsgParams Aggregation_MultiParams :=
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

Lemma IOHandler_cases :
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = []) \/
      (exists dst m', i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(sent) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = NMap.add dst (m' * st.(aggregate)) st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(sent) = None /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) = 1 /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ ~ NSet.In dst st.(adjacent) /\ 
         st' = st /\ 
         out = [] /\ ms = []) \/
      (i = AggregateRequest /\ st' = st /\ out = [AggregateResponse (aggregate st)] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler.
case: i => [m_msg|dst|]; monad_unfold.
- rewrite /= => H_eq.
  injection H_eq => H_ms H_st H_out H_tt.
  rewrite -H_st /=.
  by left; exists m_msg.
- case H_mem: (NSet.mem _ _); case (m_eq_dec _ _) => H_dec; rewrite /sumbool_not //=.
  * apply NSetFacts.mem_2 in H_mem.
    move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left; exists dst.
  * apply NSetFacts.mem_2 in H_mem.
    case H_find: (NMap.find _ _) => [m'|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    + by right; left; exists dst; exists m'.
    + by right; right; left; exists dst.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply NSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply NSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
- move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
  by right; right; right; right; right.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ NMap.find src st.(received) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\     
     st'.(received) = NMap.add src (m_src * m_msg) st.(received) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ NMap.find src st.(received) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_snt m_rcd, msg = Fail /\ NMap.find src st.(sent) = Some m_snt /\ NMap.find src st.(received) = Some m_rcd /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(sent) = NMap.remove src st.(sent) /\
     st'.(received) = NMap.remove src st.(received) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (NMap.find src st.(sent) = None \/ NMap.find src st.(received) = None) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg|]; monad_unfold.
  case H_find: (NMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=; first by left; exists m_msg; exists  m_src.
  by right; left; exists m_msg.
case H_find: (NMap.find _ _) => [m_snt|]; case H_find': (NMap.find _ _) => [m_rcd|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
- right; right; left.
  by exists m_snt; exists m_rcd.
- right; right; right.
  split => //.
  split => //.
  by right.
- right; right; right.
  split => //.
  split => //.
  by left.
- right; right; right.
  split => //.
  split => //.
  by left.
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

Instance Aggregation_FailureRecorder_base_params_pt_map : BaseParamsPartialMap Aggregation_BaseParams FR.FailureRecorder_BaseParams :=
  {
    pt_map_data := fun d => FR.mkData d.(adjacent) ;
    pt_map_input := fun _ => None ;
    pt_map_output := fun _ => None
  }.

Instance Aggregation_FailureRecorder_name_params_tot_map : MultiParamsNameTotalMap Aggregation_MultiParams FR.FailureRecorder_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance Aggregation_FailureRecorder_multi_params_pt_map : MultiParamsPartialMap Aggregation_FailureRecorder_base_params_pt_map Aggregation_FailureRecorder_name_params_tot_map :=
  {
    pt_map_msg := fun m => match m with Fail => Some FR.Fail | _ => None end ;
  }.

Lemma pt_init_handlers_eq :  forall n,
  pt_map_data (init_handlers n) = init_handlers (tot_map_name n).
Proof. by []. Qed.

Lemma pt_net_handlers_some : forall me src m st m',
  pt_map_msg m = Some m' ->
  pt_mapped_net_handlers me src m st = net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st).
Proof.
move => me src.
case => // d.
case => H_eq.
rewrite /pt_mapped_net_handlers.
repeat break_let.
apply net_handlers_NetHandler in Heqp.
net_handler_cases => //.
- by rewrite /= /runGenHandler_ignore /= H4.
- by rewrite /= /runGenHandler_ignore /id /= H3.
- by rewrite /= /runGenHandler_ignore /id /= H3.
Qed.

Lemma pt_net_handlers_none : forall me src m st out st' ps,    
  pt_map_msg m = None ->
  net_handlers me src m st = (out, st', ps) ->
  pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = [].
Proof.
move => me src.
case => //.
move => m' d out d' ps H_eq H_eq'.
apply net_handlers_NetHandler in H_eq'.
net_handler_cases => //.
by rewrite /= H3.
Qed.

Lemma pt_input_handlers_some : forall me inp st inp',
  pt_map_input inp = Some inp' ->
  pt_mapped_input_handlers me inp st = input_handlers (tot_map_name me) inp' (pt_map_data st).
Proof. by []. Qed.

Lemma pt_input_handlers_none : forall me inp st out st' ps,
  pt_map_input inp = None ->
  input_handlers me inp st = (out, st', ps) ->
  pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = [].
Proof.
move => me.
case.
- move => m' d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  io_handler_cases => //.
  by rewrite /= H2.
- move => src d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  io_handler_cases => //.
  by rewrite /= H5.
- move => d out d' ps H_eq H_inp.
  apply input_handlers_IOHandler in H_inp.
  by io_handler_cases.
Qed.

Lemma fail_msg_fst_snd : pt_map_msg msg_fail = Some (msg_fail).
Proof. by []. Qed.

Lemma adjacent_to_fst_snd : 
  forall n n', adjacent_to n n' <-> adjacent_to (tot_map_name n) (tot_map_name n').
Proof. by []. Qed.

Theorem Aggregation_Failed_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_o_f_star _ _ _ Aggregation_FailMsgParams step_o_f_init (failed, net) tr ->
    exists tr', @step_o_f_star _ _ _ FR.FailureRecorder_FailMsgParams step_o_f_init (failed, pt_map_onet net) tr' /\
    pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
have H_sim := @step_o_f_pt_mapped_simulation_star_1 _ _ _  _ _ _ _ pt_init_handlers_eq pt_net_handlers_some pt_net_handlers_none pt_input_handlers_some pt_input_handlers_none Aggregation_NameOverlayParams FR.FailureRecorder_NameOverlayParams adjacent_to_fst_snd _ _ fail_msg_fst_snd.
rewrite /tot_map_name /= /id in H_sim.
move => onet failed tr H_st.
apply H_sim in H_st.
move: H_st => [tr' [H_st H_eq]].
rewrite map_id in H_st.
by exists tr'.
Qed.

Lemma in_msg_pt_map_msgs :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m0 l ->
    In m' (pt_map_msgs l).
Proof.
elim => //.
move => m1 l IH.
case.
case => //.
case: m1 => [m5|] H_eq H_in; last by left.
case: H_in => H_in //.
rewrite /=.
move: H_in.
exact: IH.
Qed.

Lemma in_pt_map_msgs_in_msg :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m' (pt_map_msgs l) ->
    In m0 l.
Proof.
elim => //.
move => m1 l IH.
case.
case => //.
case: m1 => [m5|] /= H_eq H_in; last by left.
right.
move: H_in.
exact: IH.
Qed.

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr n, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 ~ In n failed ->
 ~ NSet.In n (onwState net n).(adjacent).
Proof.
move => onet failed tr n H_st H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: FR.Failure_node_not_adjacent_self H_st' H_in_f.
Qed.

Lemma Aggregation_not_failed_no_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
  ~ In n failed ->
  ~ In Fail (onet.(onwPackets) n n').
Proof.
move => onet failed tr H_st n n' H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_not_failed_no_fail H_st' n n' H_in_f.
move => H_in.
case: H_inv'.
rewrite /= /id /=.
move: H_in.
exact: in_msg_pt_map_msgs.
Qed.

Lemma Aggregation_in_adj_adjacent_to :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    adjacent_to n' n.
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact (FR.Failure_in_adj_adjacent_to H_st' n H_in_f H_ins).
Qed.

Lemma Aggregation_in_adj_or_incoming_fail :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    ~ In n' failed \/ (In n' failed /\ In Fail (onet.(onwPackets) n' n)).
Proof.
move => net failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_adj_or_incoming_fail H_st' _ H_in_f H_ins.
case: H_inv' => H_inv'; first by left.
right.
move: H_inv' => [H_in_f' H_inv'].
split => //.
move: H_inv'.
exact: in_pt_map_msgs_in_msg.
Qed.

Lemma count_occ_pt_map_msgs_eq :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  count_occ msg_eq_dec (pt_map_msgs l) m' = count_occ Msg_eq_dec l m0.
Proof.
elim => //.
case => [m5|] l IH.
  case.
  case => //= H_eq.
  by rewrite (IH _ Fail).
case.
case => //= H_eq.
by rewrite (IH _ Fail).
Qed.

Lemma Aggregation_le_one_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    count_occ Msg_eq_dec (onet.(onwPackets) n' n) Fail <= 1.
Proof.
move => onet failed tr H_st n n' H_in_f.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_le_one_fail H_st' _ n' H_in_f.
rewrite /= /id /= in H_inv'.
by rewrite (count_occ_pt_map_msgs_eq _ Fail) in H_inv'.
Qed.

Lemma Aggregation_adjacent_to_in_adj :
forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    ~ In n' failed ->
    adjacent_to n' n ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_in_f' H_adj.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
exact: (FR.Failure_adjacent_to_in_adj H_st' H_in_f H_in_f' H_adj).
Qed.

Lemma Aggregation_in_queue_fail_then_adjacent : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    In Fail (onet.(onwPackets) n' n) ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_ins.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_in_queue_fail_then_adjacent H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_ins.
exact: in_msg_pt_map_msgs.
Qed.

Lemma hd_error_pt_map_msgs :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  hd_error l = Some m0 ->
  hd_error (pt_map_msgs l) = Some m'.
Proof.
elim => //.
by case => [m5|] l IH; case; case.
Qed.

Lemma Aggregation_first_fail_in_adj : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    head (onet.(onwPackets) n' n) = Some Fail ->
    NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H_st n n' H_in_f H_eq.
have [tr' [H_st' H_inv]] := Aggregation_Failed_pt_mapped_simulation_star_1 H_st.
have H_inv' := FR.Failure_first_fail_in_adj H_st' _ n' H_in_f.
apply: H_inv'.
rewrite /= /id /=.
move: H_eq.
exact: hd_error_pt_map_msgs.
Qed.

Lemma Aggregation_adjacent_failed_incoming_fail : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr -> 
  forall n n',
    ~ In n failed ->
    NSet.In n' (onet.(onwState) n).(adjacent) ->
    In n' failed ->
    In Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H_st n n' H_in_f H_adj H_in_f'.
have H_or := Aggregation_in_adj_or_incoming_fail H_st _ H_in_f H_adj.
case: H_or => H_or //.
by move: H_or => [H_in H_in'].
Qed.

Lemma Aggregation_in_set_exists_find_sent : 
forall net failed tr, 
 step_o_f_star step_o_f_init (failed, net) tr ->
 forall n, ~ In n failed ->
 forall n', NSet.In n' (net.(onwState) n).(adjacent) -> 
       exists m5 : m, NMap.find n' (net.(onwState) n).(sent) = Some m5.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}.
  rewrite H_init /=.
  move => n H_in_f n' H_ins.
  rewrite /init_map.
  case (init_map_str _) => mp H.
  have H' := H n'.
  apply H' in H_ins.
  by exists 1.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * move: H5 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H10 H11.
    rewrite H10 H9.
    exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H11.
    move => H_ins.
    have H_neq': n' <> from.
      move => H_eq.
      rewrite H_eq in H_ins.
      by apply NSetFacts.remove_1 in H_ins.
    apply NSetFacts.remove_3 in H_ins.
    rewrite /= in IHrefl_trans_1n_trace1.
    have [m5 IH'] := IHrefl_trans_1n_trace1 _ H3 _ H_ins.
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H13 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H8.
    move => H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  * move: H13 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H8.
    move => H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H6 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H6.
    rewrite H7 H8 /=.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H11.
    move => H_ins.
    case (name_eq_dec n' x) => H_dec'.
      rewrite H_dec'.
      exists (x0 * aggregate (onwState net h)).
      exact: NMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H7 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
- move => n H_in n' H_ins.
  have H_neq: ~ In n failed by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Lemma Aggregation_in_set_exists_find_received : 
forall net failed tr, 
 step_o_f_star step_o_f_init (failed, net) tr -> 
 forall n, ~ In n failed ->
 forall n', NSet.In n' (net.(onwState) n).(adjacent) -> 
    exists m5 : m, NMap.find n' (net.(onwState) n).(received) = Some m5.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}.
  rewrite H_init /=.
  move => n H_in_f n' H_ins.
  rewrite /init_map.
  case (init_map_str _) => mp H.
  have H' := H n'.
  apply H' in H_ins.
  by exists 1.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * move: H5 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H10 H11.
    rewrite H11 H9.
    move => H_ins.
    case (name_eq_dec n' from) => H_dec'.
      rewrite H_dec'.
      exists (x0 * x).
      exact: NMapFacts.add_eq_o.
    have IH' := IHrefl_trans_1n_trace1 _ H4 n'.
    rewrite /= H_dec in IH'.
    concludes.
    move: IH' => [m5 H_snt].
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_dec'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H5 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H5 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H12 H10.
    move => H_ins.
    have H_neq': n' <> from.
      move => H_eq.
      rewrite H_eq in H_ins.
      by apply NSetFacts.remove_1 in H_ins.
    apply NSetFacts.remove_3 in H_ins.
    rewrite /= in IHrefl_trans_1n_trace1.
    have [m5 IH'] := IHrefl_trans_1n_trace1 _ H3 _ H_ins.
    exists m5.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.remove_neq_mapsto_iff; first by move => H_eq; rewrite H_eq in H_neq'.
    by apply NMapFacts.find_mapsto_iff.
  * move: H13 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H9.
    move => H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
  * move: H13 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H7 H9.
    move => H_ins.
    apply NSetFacts.remove_3 in H_ins.
    exact: IHrefl_trans_1n_trace1.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //=.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H7 H8 H9 H6 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H8 H9 H6.
    rewrite H7 H9 /=.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    case: d H8 H9 H10 H11 H12 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H8 H9 H10 H11 H12.
    rewrite H10 H12.
    exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H4 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
  * move: H7 {H1}.
    rewrite /update /=.
    by case name_eq_dec => H_dec; exact: IHrefl_trans_1n_trace1.
- move => n H_in n' H_ins.
  have H_neq: ~ In n failed by move => H_in'; case: H_in; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Section SingleNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variable n : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (InitData n).

Hypothesis recv_aggregate : 
  forall onet failed tr n' m' m0,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NMap.find n' (onet.(onwState) n).(received) = Some m0 ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (NMap.add n' (m0 * m') (onet.(onwState) n).(received))).

Hypothesis recv_fail : 
  forall onet failed tr n' m_snt m_rcd,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NMap.find n' (onet.(onwState) n).(sent) = Some m_snt ->
    NMap.find n' (onet.(onwState) n).(received) = Some m_rcd ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m_snt * (m_rcd)^-1) (NSet.remove n' (onet.(onwState) n).(adjacent)) (NMap.remove n' (onet.(onwState) n).(sent)) (NMap.remove n' (onet.(onwState) n).(received))).

Hypothesis recv_local_weight : 
  forall onet failed tr m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  P (onet.(onwState) n) ->
  P (mkData m' ((onwState onet n).(aggregate) * m' * ((onwState onet n).(local))^-1) (onwState onet n).(adjacent) (onwState onet n).(sent) (onwState onet n).(received)).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n' m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    NSet.In n' (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    NMap.find n' (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add n' (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)).

Theorem P_inv_n : P (onwState onet n).
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case name_eq_dec => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2 to} in H0, H1, H2.
  net_handler_cases => //.
  * case: d H4 H5 H6 H7 H8 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H4 H5 H6 H7 H8.
    rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
    exact: (recv_aggregate _ H'_step1).
  * case: d H5 H6 H7 H8 H9 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
    exact: (recv_fail H'_step1).
  * case (In_dec name_eq_dec from failed) => H_in; first last.
      have H_fail := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      case: H_fail.
      rewrite H0.
      by left.
    have H_in': In Fail (onwPackets net from n) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ from H1 H_in'.    
    have [m5 H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * case (In_dec name_eq_dec from failed) => H_in; first last.
      have H_fail := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      case: H_fail.
      rewrite H0.
      by left.
    have H_in': In Fail (onwPackets net from n) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ from H1 H_in'.    
    have [m5 H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
- move => H_in_f.
  find_apply_lem_hyp input_handlers_IOHandler.
  rewrite /update /=.
  case name_eq_dec => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2} in H0 H1.
  io_handler_cases => //.
  * case: d H3 H4 H5 H6 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local_weight _ H'_step1).
  * case: d H5 H6 H7 H8 H9 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
    exact: (recv_send_aggregate H'_step1).
- move => H_in_f.
  apply: IHH'_step1.
  move => H'_in_f.
  case: H_in_f.
  by right.
Qed.

End SingleNodeInv.

Lemma collate_msg_for_notin :
  forall m' n h ns f,
    ~ In n ns ->
    collate h f (msg_for m' (adjacent_to_node h ns)) h n = f h n.
Proof.
move => m' n h ns f.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH.
    rewrite /update2.
    case (sumbool_and _ _) => H_and //.
    move: H_and => [H_and H_and'].
    rewrite H_and' in H_in.
    by case: H_in; left.
  move => H_in'.
  case: H_in.
  by right.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_msg_for_in_failed :
  forall m' n h ns f failed,
    In n failed ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m' n h ns f failed.
move: f.
elim: ns => //.
  move => n' ns IH f H_in.
  rewrite /=.
  case (in_dec _ _) => H_dec; first by rewrite IH.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'; last by rewrite IH.
rewrite /= IH //.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_in.
Qed.

Lemma collate_msg_for_not_adjacent :
  forall m' n h ns f,
    ~ adjacent_to h n ->
    collate h f (msg_for m' (adjacent_to_node h ns)) h n = f h n.
Proof.
move => m' n h ns f H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_neq :
  forall h n n' ns f,
    h <> n ->
    collate h f ns n n' = f n n'.
Proof.
move => h n n' ns f H_neq.
move: f.
elim: ns => //.
case.
move => n0 mg ms IH f.
rewrite /=.
rewrite IH.
rewrite /update2 /=.
case (sumbool_and _ _) => H_and //.
by move: H_and => [H_and H_and'].
Qed.

Lemma collate_msg_for_live_adjacent_alt :
  forall mg n h ns f,
    adjacent_to h n ->
    ~ In n ns ->
    collate h f (msg_for mg (adjacent_to_node h (n :: ns))) h n = f h n ++ [mg].
Proof.
move => mg n h ns f H_adj H_in /=.
case adjacent_to_dec => /= H_dec // {H_dec}.
move: f n h H_in H_adj.
elim: ns  => //=.
  move => f H_in n h.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and //.
  by case: H_and => H_and.
move => n' ns IH f n h H_in H_adj.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
have H_neq: n <> n' by move => H_eq; case: H_in; left.
case adjacent_to_dec => /= H_dec; last by rewrite IH.
rewrite {3}/update2.
case sumbool_and => H_and; first by move: H_and => [H_and H_and'].
have IH' := IH f.
rewrite collate_msg_for_notin //.
rewrite /update2.
case sumbool_and => H_and'; first by move: H_and' => [H_and' H_and'']; rewrite H_and'' in H_neq.
case sumbool_and => H_and'' //.
by case: H_and''.
Qed.

Lemma exclude_in : 
  forall n ns ns',
    In n (exclude ns' ns) ->
    In n ns.
Proof.
move => n.
elim => //=.
move => n' ns IH ns'.
case (in_dec _ _) => H_dec.
  move => H_in.
  right.
  move: H_in.
  exact: IH.
move => H_in.
case: H_in => H_in; first by left.
right.
move: H_in.
exact: IH.
Qed.

Lemma collate_msg_for_live_adjacent :
  forall m' n h ns f failed,
    ~ In n failed ->
    adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (msg_for m' (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [m'].
Proof.
move => m' n h ns f failed H_in H_adj.
move: f.
elim: ns => //.
move => n' ns IH f H_in' H_nd.
inversion H_nd; subst.
rewrite /=.
case (in_dec _ _) => H_dec.
  case: H_in' => H_in'; first by rewrite H_in' in H_dec.
  by rewrite IH.
case: H_in' => H_in'.
  rewrite H_in'.
  rewrite H_in' in H1.
  rewrite /=.
  case (adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_msg_for_notin //.
    rewrite /update2.
    case (sumbool_and _ _) => H_sumb //.
    by case: H_sumb.
  move => H_inn.
  by apply exclude_in in H_inn.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by move: H_sumb => [H_eq H_eq'].
by rewrite IH.
Qed.

Definition self_channel_empty (n : name) (onet : ordered_network) : Prop :=
onet.(onwPackets) n n = [].

Lemma Aggregation_self_channel_empty : 
forall onet failed tr, 
 step_o_f_star step_o_f_init (failed, onet) tr -> 
 forall n, ~ In n failed ->
   self_channel_empty n onet.
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init {failed}; first by rewrite H_init /step_o_f_init /=.
rewrite /self_channel_empty in IHrefl_trans_1n_trace1.
rewrite /self_channel_empty.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H2.
    by rewrite IHrefl_trans_1n_trace1 in H2.
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases; rewrite /collate /= //.
  * exact: IHrefl_trans_1n_trace1.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec' H_dec in H3.
    by have H_not := Aggregation_node_not_adjacent_self H H0 H3.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
- move => n H_in.
  rewrite collate_neq.
    apply: IHrefl_trans_1n_trace1.
    move => H_in'.
    case: H_in.
    by right.
  move => H_eq.
  by case: H_in; left.
Qed.

Lemma Aggregation_in_after_all_fail_aggregate : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall (n : name), ~ In n failed ->
 forall (n' : name) m', In_all_before (Aggregate m') Fail (onet.(onwPackets) n' n).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H1}.
  net_handler_cases => //=.
  * rewrite /update2.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H1 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; last by move: IH' => [H_neq H_bef].
    exact: not_in_all_before.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H1 H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; last by move: IH' => [H_neq H_bef].
    exact: not_in_all_before.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H1 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq' in H2.
    have IH' := IHrefl_trans_1n_trace1 _ H0 n' m'.
    rewrite H2 /= in IH'.
    case: IH' => IH'; first exact: not_in_all_before.
    by move: IH' => [H_neq H_bef].
- move {H1}. 
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * exact: IHrefl_trans_1n_trace1.
  * rewrite /= /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
    move: H_dec => [H_eq H_eq'].
    rewrite H_eq H_eq'.
    rewrite H_eq in H2.
    apply: append_before_all_not_in.
    exact: Aggregation_not_failed_no_fail H _ _ H2.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
  * exact: IHrefl_trans_1n_trace1.
- move {H1} => n0 H_in_f n' m'.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  move {H_in_f}.
  case (name_eq_dec h n') => H_dec; last first.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec in H_neq H2.
  rewrite H_dec {H_dec h}.
  case (adjacent_to_dec n' n0) => H_dec; last first.
    rewrite collate_msg_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  rewrite collate_msg_for_live_adjacent //.
  * apply: append_neq_before_all => //.
    exact: IHrefl_trans_1n_trace1.
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
  forall onet failed tr, 
    step_o_f_star step_o_f_init (failed, onet) tr ->
    forall n, ~ In n failed ->
     forall n' m5, In (Aggregate m5) (onet.(onwPackets) n' n) ->
     NSet.In n' (onet.(onwState) n).(adjacent).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init; first by rewrite H_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H1}.
  net_handler_cases => //=.
  * rewrite /= in IHrefl_trans_1n_trace1.
    move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H6 H7 H8 H9 H10.
      rewrite H8 -H_dec'.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H6 H7 H8 H9 H10.
      rewrite H8 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * rewrite /= in IHrefl_trans_1n_trace1.
    move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      rewrite H_eq'.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H2.
      move => H_in.
      have H_in': In (Aggregate m5) (onwPackets net n' n) by rewrite H2; right.
      move: H_in'.
      exact: IHrefl_trans_1n_trace1.
    + rewrite -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H4.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H1 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H7 H8 H9 H10 H11.
      rewrite H9.
      move => H_ins.
      apply NSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H12.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite -H_dec' H_eq in H2.
      move => H_in.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H0 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H4 H5 H6 H7 H8 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H4 H5 H6 H7 H8.
      rewrite H6.
      move => H_ins.
      apply NSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H12.
    rewrite /update2 /update /=.
    case (sumbool_and _ _ _ _) => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      move => H_in.
      rewrite -H_dec' H_eq in H2.
      have H_bef := Aggregation_in_after_all_fail_aggregate H _ H0 n' m5.
      rewrite H2 /= in H_bef.
      case: H_bef => H_bef //.
      by move: H_bef => [H_neq H_bef].
    + move: H_dec => [H_eq H_eq'].
      by rewrite H_eq' in H_dec'.
    + case: H_dec => H_dec; last by rewrite H_dec' in H_dec.
      case: d H4 H5 H6 H7 H8 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H4 H5 H6 H7 H8.
      rewrite H6.
      move => H_ins.
      apply NSetFacts.remove_2 => //.
      rewrite -H_dec'.
      move: H_ins.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
- move {H1}. 
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * move: H3.
    rewrite /update /=.
    case name_eq_dec => H_dec; last exact: IHrefl_trans_1n_trace1.
    move => H_in.
    case: d H6 H7 H8 H5 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H6 H7 H8 H5.
    rewrite H6 -H_dec.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update2 /update.
    case sumbool_and => H_dec; case name_eq_dec => H_dec'.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq' H_dec' in H1.
      rewrite H_dec' in H0.
      by have H_self := Aggregation_node_not_adjacent_self H H0.
    + move: H_dec => [H_eq H_eq'].
      rewrite H_eq' in H1.
      rewrite H_eq in H1.
      rewrite H_eq H_eq'.
      rewrite H_eq in H2.
      move => H_in.
      have H_adj := Aggregation_in_adj_adjacent_to H _ H2 H1.
      apply adjacent_to_symmetric in H_adj.
      by have H_adj' := Aggregation_adjacent_to_in_adj H H0 H2 H_adj.
    + case: d H7 H8 H9 H10 H11 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H7 H8 H9 H10 H11.
      rewrite H9 -H_dec'.
      exact: IHrefl_trans_1n_trace1.
    + exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H3.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
  * move: H6.
    rewrite /= /update.
    case (name_eq_dec _ _) => H_dec; first by rewrite -H_dec; exact: IHrefl_trans_1n_trace1.
    exact: IHrefl_trans_1n_trace1.
- move => n0 H_in_f n' m5 H_in {H1}.
  have H_neq: h <> n0 by move => H_eq; case: H_in_f; left.
  have H_in_f': ~ In n0 failed0 by move => H_in'; case: H_in_f; right.
  case (name_eq_dec h n') => H_dec; last first.
    move: H_in.
    rewrite collate_neq //.
    exact: IHrefl_trans_1n_trace1.
  rewrite H_dec {h H_dec H_in_f} in H_in H_neq H2.
  case (adjacent_to_dec n' n0) => H_dec; last first.
    move: H_in.
    rewrite collate_msg_for_not_adjacent //.
    exact: IHrefl_trans_1n_trace1.
  move: H_in.
  rewrite collate_msg_for_live_adjacent //.
  * move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in; last by case: H_in => H_in.
    move: H_in.
    exact: IHrefl_trans_1n_trace1.
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

Section SingleNodeInvOut.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_aggregate_neq_from :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n ->
  NMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (NMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq :
  forall onet failed tr from m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  from <> n ->
  NMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (NMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq_other_some :
  forall onet failed tr m' m0 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    NMap.find n (received (onet.(onwState) n')) = Some m0 ->
    onet.(onwPackets) n n' = Aggregate m' :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (onet.(onwState) n) ms.

Hypothesis recv_fail_neq_from :
  forall onet failed tr from m0 m1 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  from <> n ->
  NMap.find from (onwState onet n).(sent) = Some m0 ->
  NMap.find from (onwState onet n).(received) = Some m1 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(sent)) (NMap.remove from (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_fail_neq :
  forall onet failed tr from m0 m1 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  In from failed ->
  n <> n' ->
  from <> n ->
  NMap.find from (onwState onet n).(sent) = Some m0 ->
  NMap.find from (onwState onet n).(received) = Some m1 ->
  onet.(onwPackets) from n = Fail :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(sent)) (NMap.remove from (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

Hypothesis recv_local_eq_some :
  forall onet failed tr m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      n <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      NSet.In n' (onet.(onwState) n).(adjacent) ->
      NMap.find n' (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (NMap.add n' (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n' ++ [Aggregate (onet.(onwState) n).(aggregate)]).

Hypothesis recv_local_neq_some :
  forall onet failed tr to m',
      step_o_f_star step_o_f_init (failed, onet) tr ->
      ~ In n failed ->
      to <> n ->
      to <> n' ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      NSet.In to (onet.(onwState) n).(adjacent) ->
      NMap.find to (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (NMap.add to (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

Theorem P_inv_n_out : P (onet.(onwState) n) (onet.(onwPackets) n n').
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_f_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec in H H2 H4 H5 H6 H7 H8 H0 H1.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H6 H8 H0. 
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec.
        case: d H4 H5 H6 H7 H8 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8.
        rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
        exact: (recv_aggregate_neq_from H'_step1 _ H_dec H H0).
      case: d H4 H5 H6 H7 H8 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8.
      rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
      case (name_eq_dec from n) => H_dec'.
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1 _ H1) in H0.
      exact: (recv_aggregate_neq H'_step1 H1 H_dec H_dec' H H0).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' in H_dec.
    rewrite H_dec' {from H_dec' H'_step2} in H H8 H0.
    rewrite H_dec'' {H_dec'' to} in H H1 H2 H4 H5 H6 H7 H8 H0.
    exact: (recv_aggregate_neq_other_some H'_step1 _ H_dec H H0).
  * rewrite /update.
    case (name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H0.
      rewrite -H_dec.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec' //.
      move: H_dec' => [H_dec' H_dec''].
      rewrite -H_dec'' in H.
      rewrite H_dec' in H H0.
      by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' {H'_step2 to H_dec''} in H_dec H H1 H2 H0.
    rewrite H_dec' {H_dec' from} in H H2 H0.
    have H_in: In (Aggregate x) (onwPackets net n n') by rewrite H0; left.    
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 _ H1 _ _ H_in.
    have [m5 H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H2.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H4 H5 H6 H7 H8 H9.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      move {H'_step2 H_dec H1}.
      case: d H5 H6 H7 H8 H9 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.      
      case: H_dec' => H_dec'.
        case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_neq_from H'_step1 H_in_f H_in H_dec' H H4 H0).
        have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
        rewrite H0 in H_inl.
        by case: H_inl; left.
      case (name_eq_dec from n) => H_neq; first by rewrite H_neq (Aggregation_self_channel_empty H'_step1) in H0.
      case (In_dec name_eq_dec from failed) => H_in; first exact: (recv_fail_neq H'_step1 _ _ H_dec' _ _ H4 H0).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H H4 H5 H6 H7 H8 H9 H0.
    rewrite H_eq' in H_dec.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec in H H0 H5.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec' in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      rewrite -H_dec in H9.
      have H_in: In Fail (onwPackets net from n) by rewrite H0; left.
      have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H_in_f H_in.
      have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H_in_f H_ins.
      by rewrite H_snt in H9.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_eq H_eq'].
    rewrite H_eq H_eq' in H_dec H1 H0.
    have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
    rewrite H0 in H_f.
    by case: H_f; left.
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec in H0.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_eq H_eq'].
        rewrite H_eq in H0.
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      rewrite -H_dec in H9.
      have H_in: In Fail (onwPackets net from n) by rewrite H0; left.
      have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H_in_f H_in.
      have [m' H_rcd] := Aggregation_in_set_exists_find_received H'_step1 _ H_in_f H_ins.
      by rewrite H_rcd in H9.
   rewrite /update2 /=.
   case (sumbool_and _ _ _ _) => H_and.
     move: H_and => [H_eq H_eq'].
     rewrite H_eq' in H1.
     rewrite H_eq H_eq' in H0.
     have H_f := Aggregation_not_failed_no_fail H'_step1 _ n' H_in_f.
     rewrite H0 in H_f.
     by case: H_f; left.
   exact: H.               
- find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec H'_step2} in H3 H4 H5 H6 H0.
    case: d H3 H4 H5 H6 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local _ H'_step1).
  * rewrite /update /= /update2.
    case name_eq_dec => H_dec.
      rewrite -H_dec.
      rewrite -H_dec {h H_dec H'_step2} in H0 H1 H3 H4 H5 H6 H7 H8 H9.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_dec''].
        rewrite H_dec''.
        rewrite H_dec'' {x H_dec'' H_dec'} in H1 H3 H4 H8.
        case: d H4 H5 H6 H7 H8 H9 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8 H9.
        rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
        case (name_eq_dec n n') => H_dec.
          have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
          by rewrite {1}H_dec in H_self.
        exact: (recv_local_eq_some H'_step1 H0 H_dec H3 H1).
      case: H_dec' => H_dec' //.
      case: d H4 H5 H6 H7 H8 H9 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H5 H6 H7 H8 H9}.
      case (name_eq_dec x n) => H_dec.
        have H_self := Aggregation_node_not_adjacent_self H'_step1 H0.
        by rewrite -{1}H_dec in H_self.
      exact: (recv_local_neq_some H'_step1 H0 H_dec H_dec' H3 H1).
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec' in H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
- move => H_in.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_f: ~ In n failed by move => H_in'; case: H_in; right.
  rewrite collate_neq //.
  exact: IHH'_step1.
Qed.

End SingleNodeInvOut.

Section SingleNodeInvIn.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star step_o_f_init (failed, onet) tr.

Variables n n' : name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (InitData n) [].

Hypothesis recv_aggregate : 
  forall onet failed tr m' m0 ms,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  NMap.find n' (onet.(onwState) n).(received) = Some m0 ->
  onet.(onwPackets) n' n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (NMap.add n' (m0 * m') (onet.(onwState) n).(received))) ms.

Hypothesis recv_aggregate_other : 
  forall onet failed tr m' from m0,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  from <> n' ->
  NMap.find from (onwState onet n).(received) = Some m0 ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (NMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n' n).

Hypothesis recv_fail : 
  forall onet failed tr m0 m1 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In n' failed ->
    n <> n' ->
    NMap.find n' (onwState onet n).(sent) = Some m0 ->
    NMap.find n' (onwState onet n).(received) = Some m1 ->
    onet.(onwPackets) n' n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (NSet.remove n' (onet.(onwState) n).(adjacent)) (NMap.remove n' (onet.(onwState) n).(sent)) (NMap.remove n' (onet.(onwState) n).(received))) ms.

Hypothesis recv_fail_other : 
  forall onet failed tr from m0 m1 ms,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    In from failed ->
    from <> n' ->
    NMap.find from (onwState onet n).(sent) = Some m0 ->
    NMap.find from (onwState onet n).(received) = Some m1 ->
    onet.(onwPackets) from n = Fail :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m0 * m1^-1) (NSet.remove from (onet.(onwState) n).(adjacent)) (NMap.remove from (onet.(onwState) n).(sent)) (NMap.remove from (onet.(onwState) n).(received))) (onwPackets onet n' n).

Hypothesis recv_local : 
  forall onet failed tr m_local,
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n0 m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    n <> n' ->
    NSet.In n0 (onet.(onwState) n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    NMap.find n0 (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add n0 (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet failed tr to m',
    step_o_f_star step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    to <> n ->
    NSet.In to (onet.(onwState) n).(adjacent) ->
    (onet.(onwState) n).(aggregate) <> 1 ->
    NMap.find to (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (NMap.add to (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_neq :
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  (onet.(onwState) n').(aggregate) <> 1 ->
  NSet.In n (onet.(onwState) n').(adjacent) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n ++ [Aggregate (onet.(onwState) n').(aggregate)]).

Hypothesis recv_fail_neq :
  forall onet failed tr ms m m',
  step_o_f_star step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  n <> n' ->
  NMap.find n' (onet.(onwState) n).(sent) = Some m ->
  NMap.find n' (onet.(onwState) n).(received) = Some m' ->
  onwPackets onet n' n = Fail :: ms ->
  P (onwState onet n) (onwPackets onet n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m * m'^-1) (NSet.remove n' ((onet.(onwState) n).(adjacent))) (NMap.remove n' (onet.(onwState) n).(sent)) (NMap.remove n' (onet.(onwState) n).(received))) ms.

Hypothesis fail_adjacent :
  forall onet failed tr,
step_o_f_star step_o_f_init (failed, onet) tr ->
~ In n failed ->
~ In n' failed ->
n' <> n ->
adjacent_to n' n ->
P (onwState onet n) (onwPackets onet n' n) ->
P (onwState onet n) (onwPackets onet n' n ++ [Fail]).

Theorem P_inv_n_in : P (onet.(onwState) n) (onet.(onwPackets) n' n).
Proof.
move: onet failed tr H_step not_failed.
clear onet failed not_failed tr H_step.
move => onet' failed' tr H'_step.
have H_eq_f: failed' = fst (failed', onet') by [].
have H_eq_o: onet' = snd (failed', onet') by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2 3}H_eq_o {H_eq_o}.
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /step_o_f_init /= => H_in_f.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move => H_in_f.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.   
  * rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite -H_dec in H H1 H4 H5 H6 H7 H8 H0.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H8 H0.
        case: d H4 H5 H6 H7 H8 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H4 H5 H6 H7 H8.
        rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
        case (name_eq_dec n n') => H_dec'.
          rewrite -H_dec' in H0.
          by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
        exact: (recv_aggregate H'_step1 H1 H_dec' H H0).
      case: H_dec => H_dec //.
      case: d H4 H5 H6 H7 H8 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H5 H6 H7 H8.
      rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
      exact: (recv_aggregate_other _ H'_step1).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec'' in H_dec.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.    
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_rcd in H2.
  * rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec.
      move: H_dec => [H_eq H_eq'].
      rewrite H_eq H_eq' in H0 H H4 H5 H6 H7 H8.
      case (In_dec name_eq_dec n' failed) => H_in.
        rewrite /update /=.
        case name_eq_dec => H_dec; last by rewrite H_eq' in H_dec.
        rewrite -H_dec H_eq in H9.
        have H_neq: n <> n' by move => H_eq_n; rewrite -H_eq_n in H_in.
        move {H'_step2}.
        case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
        move => H5 H6 H7 H8 H9.
        rewrite H5 H6 H7 H8 H9.
        exact: (recv_fail H'_step1).
      have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
      rewrite H0 in H_inl.
      by case: H_inl; left.
    rewrite /update /=.
    case name_eq_dec => H_dec'; last exact: H2.
    rewrite -H_dec' in H_dec.
    case: H_dec => H_dec //.
    rewrite -H_dec' {H_dec'} in H H0 H4 H5 H6 H7 H8 H9.
    case (In_dec name_eq_dec from failed) => H_in.
      move {H'_step2}.
      case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
      move => H5 H6 H7 H8 H9.
      rewrite H5 H6 H7 H8 H9 {H5 H6 H7 H8 H9 local0 aggregate0 adjacent0 sent0 received0}.
      exact: (recv_fail_other H'_step1 _ _ _ _ _ H0).          
    have H_inl := Aggregation_not_failed_no_fail H'_step1 _ n H_in.
    rewrite H0 in H_inl.
    by case: H_inl; left.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H1 H_in.
    have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H'_step1 _ _ H1 H_in.
    have [m' H_snt] := Aggregation_in_set_exists_find_received H'_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
- move {H'_step2}.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec} in H0 H3 H4 H1 H5 H6.
    case: d H3 H4 H5 H6 => /= local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6.
    rewrite H3 H4 H5 H6 {aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6}.
    exact: (recv_local _ H'_step1).
  - rewrite /update /=.
    case name_eq_dec => H_dec.
      rewrite /update2 /=.
      case (sumbool_and _ _ _ _) => H_dec'.
        move: H_dec' => [H_dec' H_eq].
        rewrite H_eq -H_dec in H1.
        contradict H1.
        exact: (Aggregation_node_not_adjacent_self H'_step1).
      case: H_dec' => H_dec'.
        rewrite -H_dec in H_dec'.
        rewrite -H_dec {H_dec h} in H1 H3 H4 H5 H0 H7 H8 H9.
        case: d H6 H5 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 receive0.
        move => H6 H5 H7 H8 H9.
        rewrite H6 H5 H7 H8 H9 {local0 aggregate0 adjacent0 sent0 receive0 H6 H5 H7 H8 H9}.
        exact: (recv_send_aggregate H'_step1).
      rewrite -H_dec {H_dec h} in H1 H0 H3 H4 H5 H7 H8 H9.
      case: d H6 H5 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 receive0.
      move => H6 H5 H7 H8 H9.
      rewrite H6 H5 H7 H8 H9 {H6 H5 H7 H8 H9 local0 aggregate0 adjacent0 sent0 receive0}.
      exact: (recv_send_aggregate_other H'_step1).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec' in H_dec H H1 H4 H3 H5 H6 H7 H0 H8 H9.
    rewrite H_dec' {H_dec' h}.
    rewrite H_dec'' in H4 H8 H1.
    rewrite H_dec'' {H_dec'' x}.
    exact: (recv_send_aggregate_neq H'_step1).
  * have [m' H_snt] := Aggregation_in_set_exists_find_sent H'_step1 _ H0 H.
    by rewrite H_snt in H4.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
  * rewrite /update /=.
    by case name_eq_dec => H_dec; first by rewrite -H_dec.
- move => H_in_f {H'_step2}.
  have H_neq: h <> n by move => H_neq'; case: H_in_f; left.
  have H_in_f': ~ In n failed by move => H_in; case: H_in_f; right.
  have IH := IHH'_step1 H_in_f'.
  rewrite /= in IH.
  case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
  rewrite H_dec.
  rewrite H_dec {H_dec h H_in_f} in H0 H_neq.
  case (adjacent_to_dec n' n) => H_dec; last by rewrite collate_msg_for_not_adjacent.
  rewrite collate_msg_for_live_adjacent //.
  * exact: (fail_adjacent H'_step1).
  * exact: all_names_nodes.
  * exact: no_dup_nodes.
Qed.

End SingleNodeInvIn.

Instance AggregationData_Data : AggregationData Data :=
  {
    local := local ;
    aggregate := aggregate ;
    adjacent := adjacent ;
    sent := sent ;
    received := received
  }.

Lemma Aggregation_conserves_node_mass : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 forall n, ~ In n failed -> conserves_node_mass (onet.(onwState) n).
Proof.
move => onet failed tr H.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  move => n.
  rewrite H_init /conserves_node_mass /InitData /= => H_in.
  by rewrite sumM_init_map_1; gsimpl.
move => n.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move {H1}.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //=.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {H_dec to H3} in H1 H5 H6 H7 H8 H9 H2.
    case: d H5 H6 H7 H8 H9 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H8 H9.
    rewrite H5 H6 H7 H8 H9 {H5 H6 H7 H8 H9 local0 aggregate0 adjacent0 sent0 received0}.
    rewrite /conserves_node_mass /=.
    have H_ins: NSet.In from (net.(onwState) n).(adjacent).
      have H_in: In (Aggregate x) (net.(onwPackets) from n) by rewrite H2; left.
      exact: Aggregation_aggregate_msg_dst_adjacent_src H _ H0 _ _ H_in.
    rewrite IH sumM_add_map //; gsimpl.
    suff H_eq: (net.(onwState) n).(aggregate) * x * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * x^-1 * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
     (net.(onwState) n).(aggregate) * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 * (x * x^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H2; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H _ H3 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H _ H3 H_ins.
    by rewrite H_rcd in H1.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {H_dec to H3} in H1 H5 H6 H7 H8 H9 H10 H2.
    case: d H6 H7 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H6 H7 H8 H9 H10.
    rewrite H6 H7 H8 H9 H10 {H6 H7 H8 H9 H10 local0 aggregate0 adjacent0 sent0 received0}.
    rewrite /conserves_node_mass /= IH.
    have H_in: In Fail (net.(onwPackets) from n) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H0 H_in.
    rewrite (sumM_remove_remove H_ins H1) (sumM_remove_remove H_ins H5); gsimpl.
    suff H_eq: 
      (net.(onwState) n).(aggregate) * x * x0^-1 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * x^-1 * x0 * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
      (net.(onwState) n).(aggregate) * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 * (x * x^-1) * (x0 * x0^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have H_in: In Fail (net.(onwPackets) from to) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H3 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_sent H _ H3 H_ins.
    by rewrite H_rcd in H11.
  * have H_in: In Fail (net.(onwPackets) from to) by rewrite H2; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H _ _ H3 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H _ H3 H_ins.
    by rewrite H_rcd in H11.
- move {H1}.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases => //.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec} in H5 H2 H6 H7 H4.
    case: d H5 H6 H7 H4 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H5 H6 H7 H4.
    rewrite /conserves_node_mass /= H5 H6 H7 H4 {H5 H6 H7 H4 aggregate0 adjacent0 sent0 received0}.
    rewrite IH; gsimpl.
    suff H_eq: 
        (net.(onwState) n).(aggregate) * local0 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent))^-1 * (net.(onwState) n).(aggregate)^-1 * sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1 = 
        local0 * ((net.(onwState) n).(aggregate) * (net.(onwState) n).(aggregate)^-1) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(sent))^-1) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received) * (sumM (net.(onwState) n).(adjacent) (net.(onwState) n).(received))^-1) by rewrite H_eq; gsimpl.
    by aac_reflexivity.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /conserves_node_mass /= {IHrefl_trans_1n_trace1} in IH.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    rewrite -H_dec {h H_dec} in H1 H2 H4 H5 H6 H8 H9 H10.
    case: d H7 H6 H8 H9 H10 => /= local0 aggregate0 adjacent0 sent0 received0.
    move => H7 H6 H8 H9 H10.
    rewrite /conserves_node_mass /= H7 H6 H8 H9 H10 {H7 H6 H8 H9 H10 aggregate0 adjacent0 sent0 received0}.
    rewrite IH sumM_add_map; gsimpl.
    by aac_reflexivity.
  * have [m5 H_rcd] := Aggregation_in_set_exists_find_sent H _ H2 H1.
    by rewrite H_rcd in H5.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /= in IH.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    by rewrite -H_dec.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    by rewrite -H_dec.
  * have IH := IHrefl_trans_1n_trace1 _ H0.
    rewrite /update /=.
    case name_eq_dec => H_dec //.
    by rewrite -H_dec.
- move => H_in_f.
  have H_in_f': ~ In n failed0 by move => H_in; case: H_in_f; right.
  exact: IHrefl_trans_1n_trace1.
Qed.

Definition Nodes_data (ns : list name) (state : name -> Data) : list Data :=
fold_right (fun (n : name) (l' : list Data) => n.(state) :: l') [] ns.

Lemma Aggregation_conserves_node_mass_all : 
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_node_mass_all (Nodes_data (exclude failed nodes) onet.(onwState)).
Proof.
move => onet failed tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data.
elim: nodes => //=.
move => n l IH.
move => d.
case (in_dec _ _ _) => H_dec; first exact: IH.
move => H_or.
case: H_or => H_or.
  rewrite -H_or.
  exact: (Aggregation_conserves_node_mass H_st).
exact: IH.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet failed tr,
 step_o_f_star step_o_f_init (failed, onet) tr ->
 conserves_mass_globally (Nodes_data (exclude failed nodes) onet.(onwState)).
Proof.
move => onet failed tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

Definition aggregate_sum_fold (msg : Msg) (partial : m) : m :=
match msg with
| Aggregate m' => partial * m'
| _ => partial
end.

Definition sum_aggregate_msg := fold_right aggregate_sum_fold 1.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed -> sum_aggregate_msg (onet.(onwPackets) n n) = 1.
Proof.
move => onet failed tr H_step n H_in_f.
by rewrite (Aggregation_self_channel_empty H_step).
Qed.

(* given n, sum aggregate messages for all its incoming channels *)
Definition sum_aggregate_msg_incoming (ns : list name) (packets : name -> name -> list Msg) (n : name) : m := 
fold_right (fun (n' : name) (partial : m) => 
  partial * if In_dec Msg_eq_dec Fail (packets n' n) then 1 else sum_aggregate_msg (packets n' n)) 1 ns.

(* given list of active names and all names, sum all incoming channels for all active *)
Definition sum_aggregate_msg_incoming_active (allns : list name) (actns : list name)  (packets : name -> name -> list Msg) : m :=
fold_right (fun (n : name) (partial : m) => partial * sum_aggregate_msg_incoming allns packets n) 1 actns.

Definition sum_fail_map (l : list Msg) (from : name) (adj : NS) (map : NM) : m :=
if In_dec Msg_eq_dec Fail l && NSet.mem from adj then sum_fold map from 1 else 1.

Definition sum_fail_map_incoming (ns : list name) (packets : name -> name -> list Msg) (n : name) (adj : NS) (map : NM) : m :=
fold_right (fun (n' : name) (partial : m) => partial * sum_fail_map (packets n' n) n' adj map) 1 ns.

Definition sum_fail_sent_incoming_active (allns : list name) (actns : list name) (packets : name -> name -> list Msg) (state : name -> Data) : m :=
fold_right (fun (n : name) (partial : m) => 
  partial * sum_fail_map_incoming allns packets n n.(state).(adjacent) n.(state).(sent)) 1 actns.

Definition sum_fail_received_incoming_active (allns : list name) (actns : list name) (packets : name -> name -> list Msg) (state : name -> Data) : m :=
fold_right (fun (n : name) (partial : m) => 
  partial * sum_fail_map_incoming allns packets n n.(state).(adjacent) n.(state).(received)) 1 actns.

Definition conserves_network_mass (actns : list name) (allns : list name) (packets : name -> name -> list Msg) (state : name -> Data) : Prop :=
sum_local (Nodes_data actns state) = 
  sum_aggregate (Nodes_data actns state) * sum_aggregate_msg_incoming_active allns actns packets * 
  sum_fail_sent_incoming_active allns actns packets state * (sum_fail_received_incoming_active allns actns packets state)^-1.

Lemma sum_aggregate_msg_incoming_step_o_init :
  forall ns n, sum_aggregate_msg_incoming ns step_o_init.(onwPackets) n = 1.
Proof.
move => ns n.
rewrite /sum_aggregate_msg_incoming /= {n}.
elim: ns => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_all_step_o_init :
  forall actns allns, sum_aggregate_msg_incoming_active allns actns (fun _ _ => []) = 1.
Proof.
rewrite /sum_aggregate_msg_incoming_active /=.
elim => [|a l IH] l' //=.
rewrite IH sum_aggregate_msg_incoming_step_o_init.
by gsimpl.
Qed.

Lemma sum_local_step_o_init :
  forall ns, sum_local (Nodes_data ns init_handlers) = 1.
Proof.
rewrite /Nodes_data /step_o_init /=.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_step_o_init :
  forall ns, sum_aggregate (Nodes_data ns init_handlers) = 1.
Proof.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_local_split :
  forall ns0 ns1 state n,
    sum_local (Nodes_data (ns0 ++ n :: ns1) state) =
    n.(state).(local) * sum_local (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => /=; first by move => ns1 state n; aac_reflexivity.
move => n ns IH ns1 state n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma sum_aggregate_split :
  forall ns0 ns1 state n,
    sum_aggregate (Nodes_data (ns0 ++ n :: ns1) state) =
    n.(state).(aggregate) * sum_aggregate (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => /=; first by move => ns1 state n; aac_reflexivity.
move => n ns IH ns1 state n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma nodup_notin : 
  forall (A : Type) (a : A) (l l' : list A),
    NoDup (l ++ a :: l') ->
    ~ In a (l ++ l').
Proof.
move => A a.
elim => /=; first by move => l' H_nd; inversion H_nd; subst.
move => a' l IH l' H_nd.
inversion H_nd; subst.
move => H_in.
case: H_in => H_in.
  case: H1.
  apply in_or_app.
  by right; left.
contradict H_in.
exact: IH.
Qed.

Lemma Nodes_data_not_in : 
forall n' d state ns,
~ In n' ns ->
fold_right
  (fun (n : name) (l : list Data) =>
     (match name_eq_dec n n' with
      | left _ => d 
      | right _ => n.(state) 
      end) :: l) [] ns = Nodes_data ns state.
Proof.
move => n' d state.
elim => //.
move => a l IH H_in.
rewrite /=.
case name_eq_dec => H_dec; first by case: H_in; left.
rewrite IH => //.
move => H_in'.
by case: H_in; right.
Qed.

(* with failed nodes - don't add their incoming messages, but add their outgoing channels to non-failed nodes *)

Lemma sum_aggregate_msg_neq_from :
forall from to n packets ms ns,
~ In from ns ->
fold_right
  (fun (n' : name) (partial : m) => 
     partial * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns =
fold_right
  (fun (n' : name) (partial : m) => 
     partial * sum_aggregate_msg (packets n' n)) 1 ns.
Proof.
move => from to n packets ms.
elim => //.
move => n0 ns IH H_in.
rewrite /= IH /=; last by move => H_in'; case: H_in; right.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_dec H_dec'].
case: H_in.
by left.
Qed.

Lemma sum_aggregate_msg_n_neq_from :
forall from to n packets ms ns,
to <> n ->
fold_right
  (fun (n' : name) (partial : m) => 
     partial * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns =
fold_right
  (fun (n' : name) (partial : m) => 
     partial * sum_aggregate_msg (packets n' n)) 1 ns.
Proof.
move => from to n packets ms ns H_neq.
elim: ns => //.
move => n' l IH.
rewrite /= IH /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
by move: H_dec => [H_dec H_dec'].
Qed.

Lemma sum_aggregate_msg_neq_to :
forall from to packets ms ns1 ns0,
~ In to ns1 ->
fold_right
  (fun (n : name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns0) 1 ns1 = 
fold_right
  (fun (n : name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (packets n' n)) 1 ns0) 1 ns1.
Proof.
move => from to packets ms.
elim => //=.
move => n l IH ns H_in.
rewrite IH /=; last by move => H_in'; case: H_in; right.
have H_neq: to <> n by move => H_eq; case: H_in; left.
by rewrite sum_aggregate_msg_n_neq_from.
Qed.

Lemma sum_aggregate_msg_incoming_neq_eq :
  forall ns n f from to ms,
  n <> to ->
  sum_aggregate_msg_incoming ns (update2 f from to ms) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //.
move => n ns IH n' f from to ms H_neq.
rewrite /= IH //.
rewrite /update2 /=.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_aggregate_msg_incoming_active_not_in_eq :
  forall ns ns' from to ms f,
    ~ In to ns ->
    sum_aggregate_msg_incoming_active ns' ns (update2 f from to ms) =
    sum_aggregate_msg_incoming_active ns' ns f.
Proof.
elim => //=.
move => n ns IH ns' from to ms f H_in.
have H_not_in: ~ In to ns by move => H_in'; case: H_in; right.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_not_in_eq :
forall ns ns0 f from to ms,
~ In to ns0 ->
fold_right
     (fun (n0 : name) (partial : m) =>
      partial * sum_aggregate_msg_incoming ns (update2 f from to ms) n0) 1 ns0 =
fold_right
     (fun (n0 : name) (partial : m) =>
      partial * sum_aggregate_msg_incoming ns f n0) 1 ns0.
Proof.
move => ns ns0 f from to ms.
elim: ns0 => //.
move => n ns' IH.
rewrite /=.
move => H_in.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_in': ~ In to ns' by move => H_in'; case: H_in; right.
rewrite IH //.
set m1 := sum_aggregate_msg_incoming _ _ _.
set m2 := sum_aggregate_msg_incoming _ _ _.
suff H_suff: m1 = m2 by rewrite H_suff.
move {IH ns' H_in' H_in}.
rewrite /m1 /m2 {m1 m2}.
elim: ns => //.
move => n' ns IH.
rewrite /= IH.
suff H_suff: update2 f from to ms n' n = f n' n by rewrite H_suff.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_aggregate_msg_fold_split :
forall ns0 ns1 ns2 from to ms packets,
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns0) 1 (ns1 ++ ns2) = 
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns0) 1 ns1 * 
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns0) 1 ns2.
Proof.
move => ns0 ns1 ns2 from to ms packets.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split_folded :
forall ns0 ns1 from to n packets ms,
fold_right (fun (n' : name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 (ns0 ++ ns1) = 
fold_right (fun (n' : name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns0 *
fold_right (fun (n' : name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 packets from to ms n' n)) 1 ns1.
Proof.
move => ns0 ns1 from to n onet ms.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH /=.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_split :
  forall ns0 ns1 packets n,
    sum_aggregate_msg_incoming (ns0 ++ ns1) packets n = 
    sum_aggregate_msg_incoming ns0 packets n *
    sum_aggregate_msg_incoming ns1 packets n.
Proof.
move => ns0 ns1 packets n.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_split :
  forall ns0 ns1 ns2 packets,
    sum_aggregate_msg_incoming_active ns0 (ns1 ++ ns2) packets = 
    sum_aggregate_msg_incoming_active ns0 ns1 packets *
    sum_aggregate_msg_incoming_active ns0 ns2 packets.
Proof.
move => ns0 ns1 ns2 packets.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_fail_sent_incoming_active_split :
  forall ns0 ns1 ns2 packets state,
    sum_fail_sent_incoming_active ns0 (ns1 ++ ns2) packets state = 
    sum_fail_sent_incoming_active ns0 ns1 packets state *
    sum_fail_sent_incoming_active ns0 ns2 packets state.
Proof.
move => ns0 ns1 ns2 packets state.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_fail_received_incoming_active_split :
  forall ns0 ns1 ns2 packets state,
    sum_fail_received_incoming_active ns0 (ns1 ++ ns2) packets state = 
    sum_fail_received_incoming_active ns0 ns1 packets state *
    sum_fail_received_incoming_active ns0 ns2 packets state.
Proof.
move => ns0 ns1 ns2 packets state.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split : 
  forall l1 l2,
    sum_aggregate_msg (l1 ++ l2) = sum_aggregate_msg l1 * sum_aggregate_msg l2.
Proof.
elim => //= [|msg l' IH] l2; first by gsimpl.
rewrite IH.
rewrite /aggregate_sum_fold /=.
by case: msg => [m'|]; aac_reflexivity.
Qed.

Lemma fold_right_update_id :
forall ns h state,
fold_right 
  (fun (n : name) (l' : list Data) =>
     update state h (state h) n :: l') [] ns =
fold_right 
  (fun (n : name) (l' : list Data) =>
     (state n) :: l') [] ns.
Proof.
elim => //.
move => n l IH h state.
rewrite /= IH.
rewrite /update /=.
case name_eq_dec => H_dec //.
by rewrite H_dec.
Qed.

(* take Fail messages into account when summing up Aggregate messages *)

Lemma In_n_exclude : 
  forall n ns ns',
    ~ In n ns' ->
    In n ns ->
    In n (exclude ns' ns).
Proof.
move => n.
elim => //=.
move => n' ns IH ns' H_in H_in'.
case: H_in' => H_in'.
  rewrite H_in'.
  case (in_dec _ _) => H_dec //.
  by left.
case (in_dec _ _) => H_dec; first exact: IH.
right.
exact: IH.
Qed.

Lemma nodup_exclude : 
  forall ns ns', 
    NoDup ns ->
    NoDup (exclude ns' ns).
Proof.
elim => //.
move => n ns IH ns' H_nd.
rewrite /=.
inversion H_nd.
case (in_dec _ _) => H_dec; first exact: IH.
apply NoDup_cons.
  move => H_in.
  case: H1.
  move: H_in.
  exact: exclude_in.
exact: IH.
Qed.

Lemma sum_aggregate_msg_incoming_update2_eq :
  forall ns f from to ms n,
  ~ In from ns ->
  sum_aggregate_msg_incoming ns (update2 f from to ms) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n l IH f from to ms n' H_in.
have H_in' : ~ In from l by move => H_in'; case: H_in; right.
rewrite IH //.
have H_neq: n <> from by move => H_eq; case: H_in; left.
rewrite /update2 /=.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq in H_neq.
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    ~ In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to * (m')^-1.
Proof.
elim => //.
move => n ns IH f from to ms m' H_in H_nd H_f H_eq.
case: H_in => H_in.  
  rewrite H_in /=.
  case (in_dec _ _) => H_dec; case (in_dec _ _) => H_dec' //=.
    rewrite H_eq in H_dec'.
    case: H_dec'.
    right.    
    move: H_dec.
    rewrite /update2.
    by case (sumbool_and _ _ _ _) => H_dec.
  rewrite H_eq /=.
  gsimpl.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec''; last by case: H_dec''.
  rewrite H_in in H_nd.
  inversion H_nd.
  by rewrite sum_aggregate_msg_incoming_update2_eq.
rewrite /=.
inversion H_nd.
rewrite (IH f from to ms m') //.
have H_neq: n <> from by move => H_eq'; rewrite H_eq' in H1.
case (in_dec _ _) => H_dec; case (in_dec _ _) => H_dec' //=.
- by gsimpl.
- case: H_dec'.
  move: H_dec.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
- case: H_dec.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
- rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec0; first by move: H_dec0 => [H_eq0 H_eq1]; rewrite H_eq0 in H_neq.
  by aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_sent_neq_eq :
  forall ns packets state from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (adjacent (match name_eq_dec n to with left _ => d | right_ => state n end))
    (sent (match name_eq_dec n to with left _ => d |right _ => state n end)) =
  sum_fail_map_incoming ns packets n (adjacent (state n)) (sent (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms n0 d H_neq.
rewrite IH //.
case name_eq_dec => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_map_incoming_received_neq_eq :
  forall ns packets state from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (adjacent (match name_eq_dec n to with left _ => d | right_ => state n end))
    (received (match name_eq_dec n to with left _ => d |right _ => state n end)) =
  sum_fail_map_incoming ns packets n (adjacent (state n)) (received (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms n0 d H_neq.
rewrite IH //.
case name_eq_dec => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq :
  forall ns0 ns1 packets state from to ms d,
    ~ In to ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 
      (update2 packets from to ms) 
      (fun nm : name => match name_eq_dec nm to with left _ => d | right _ => state nm end) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms d H_in.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_sent_neq_eq //.
rewrite -/(sum_fail_sent_incoming_active _ _ _ _).
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 packets state from to ms d H_in'.
by rewrite IH' /=.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt :
forall ns1 ns0 packets state h d,
  ~ In h ns1 ->
  sum_fail_sent_incoming_active ns0 ns1 packets (update state h d) =
  sum_fail_sent_incoming_active ns0 ns1 packets state.
Proof.
elim => //=.
move => n ns1 IH ns0 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns1 by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq :
  forall ns0 ns1 packets state from to ms d,
    ~ In to ns0 ->
    sum_fail_received_incoming_active ns1 ns0 (update2 packets from to ms)
     (fun nm : name => match name_eq_dec nm to with left _ => d | right _ => state nm end) =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms d H_in.
rewrite /sum_fail_received_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_received_neq_eq //.
rewrite -/(sum_fail_received_incoming_active _ _ _ _).
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 packets state from to ms d H_in'.
by rewrite IH'.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt :
forall ns packets state h d,
  ~ In h ns ->
  sum_fail_received_incoming_active nodes ns packets (update state h d) =
  sum_fail_received_incoming_active nodes ns packets state.
Proof.
elim => //=.
move => n ns IH packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_map_incoming_not_in_eq :
  forall ns f from to n ms adj map,
    ~ In from ns ->
    sum_fail_map_incoming ns (update2 f from to ms) n adj map =
    sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n' ns IH f from to n ms adj map H_in.
have H_neq: n' <> from by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq H_eq'].
by rewrite H_eq in H_neq.
Qed.

Lemma sum_fail_map_incoming_collate_not_in_eq :
  forall l ns h n f adj map,
  ~ In h ns ->
  sum_fail_map_incoming ns (collate h f l) n adj map =
  sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
case => n0 mg l IH ns h n f adj map H_in.
rewrite IH //.
by rewrite sum_fail_map_incoming_not_in_eq.
Qed.

Lemma no_fail_sum_fail_map_incoming_eq :
  forall ns mg f from to ms adj map,  
  In from ns ->
  NoDup ns ->
  f from to = mg :: ms ->
  ~ In Fail (f from to) ->
  sum_fail_map_incoming ns (update2 f from to ms) to adj map =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH mg f from to ms adj map.
case => H_in H_eq H_in'.
  rewrite H_in.
  rewrite H_in in H_eq.
  rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  inversion H_eq.
  move => H_not_in.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite {2}/sum_fail_map.
  case (in_dec _ _) => /= H_dec' //.
  rewrite H_in' in H_not_in.
  have H_not_in': ~ In Fail ms by move => H_inn; case: H_not_in; right.
  rewrite {1}/sum_fail_map.
  by case (in_dec _ _) => /= H_dec''.
inversion H_eq.
move => H_inn.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
rewrite {2}/update2 /=.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1].
by rewrite (IH mg f from to ms adj map H_in).
Qed.

Lemma sum_fail_map_incoming_add_not_in_eq :
  forall ns f m' from to adj map,
  ~ In from ns ->
  sum_fail_map_incoming ns f to adj (NMap.add from m' map) =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f m' from to adj map H_in.
have H_neq: from <> n by move => H_eq; case: H_in; left.
have H_not_in: ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /sum_fail_map /sum_fold.
case H_find: (NMap.find _ _) => [m0|]; case H_find': (NMap.find _ _) => [m1|] //.
- apply NMapFacts.find_mapsto_iff in H_find.
  apply NMapFacts.add_neq_mapsto_iff in H_find => //.
  apply NMapFacts.find_mapsto_iff in H_find.
  rewrite H_find in H_find'.
  by inversion H_find'.
- apply NMapFacts.find_mapsto_iff in H_find.
  apply NMapFacts.add_neq_mapsto_iff in H_find => //.
  apply NMapFacts.find_mapsto_iff in H_find.
  by rewrite H_find in H_find'.
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply (NMapFacts.add_neq_mapsto_iff _ m' _ H_neq) in H_find'.
  apply NMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find in H_find'.
Qed.

Lemma no_fail_sum_fail_map_incoming_add_eq :
  forall ns mg m' f from to ms adj map,  
  In from ns ->
  NoDup ns ->
  f from to = mg :: ms ->
  ~ In Fail (f from to) ->
  sum_fail_map_incoming ns (update2 f from to ms) to adj (NMap.add from m' map) =
  sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH mg m' f from to ms adj map.
case => H_in H_eq H_in'.
  rewrite H_in.
  rewrite H_in in H_eq.
  rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  inversion H_eq.
  move => H_not_in.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite {2}/sum_fail_map.
  case (in_dec _ _) => /= H_dec' //.
  rewrite H_in' in H_not_in.
  have H_not_in': ~ In Fail ms by move => H_inn; case: H_not_in; right.
  rewrite {1}/sum_fail_map /=.
  case (in_dec _ _) => /= H_dec'' //.
  by rewrite sum_fail_map_incoming_add_not_in_eq.
move => H_inn.
inversion H_eq.
rewrite (IH _ _ _ _ _ _ _ _ H_in H2 H_in' H_inn).
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq0 H_eq1].
rewrite /sum_fail_map.
case (in_dec _ _) => /= H_dec' //.
case (NSet.mem _ _) => //.
rewrite /sum_fold.
case H_find: (NMap.find _ _) => [m0|]; case H_find': (NMap.find _ _) => [m1|] //.
- apply NMapFacts.find_mapsto_iff in H_find.
  apply NMapFacts.add_neq_mapsto_iff in H_find => //.
  apply NMapFacts.find_mapsto_iff in H_find.
  rewrite H_find in H_find'.
  by inversion H_find'.
- apply NMapFacts.find_mapsto_iff in H_find.
  apply NMapFacts.add_neq_mapsto_iff in H_find => //.
  apply NMapFacts.find_mapsto_iff in H_find.
  by rewrite H_find in H_find'.
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply (NMapFacts.add_neq_mapsto_iff _ m' _ H_neq) in H_find'.
  apply NMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find in H_find'.
Qed.

Lemma sum_aggregate_msg_incoming_update2_fail_eq : 
  forall ns f from to ms m',
    In from ns ->
    NoDup ns ->
    In Fail (f from to) ->
    f from to = Aggregate m' :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
elim => //=.
move => n ns IH f from to ms m' H_in H_nd H_in' H_eq.
case: H_in => H_in.
  inversion H_nd.
  rewrite H_in.
  rewrite H_in {H_in l x H H0 n H_nd} in H1.
  have H_in'' := H_in'.
  rewrite H_eq in H_in''.
  case: H_in'' => H_in'' //.
  case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
  - by rewrite sum_aggregate_msg_incoming_update2_eq.
  - case: H_dec.
    rewrite /update2.
    by case (sumbool_and _ _ _ _) => H_dec_s.
inversion H_nd => {x l H H0}.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec'.
- by rewrite (IH _ _ _ _ m').
- case: H_dec'.
  move: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- case: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- rewrite {2}/update2 /=.
  case (sumbool_and _ _ _ _) => H_dec_s; first by move: H_dec_s => [H_eq' H_eq''].
  by rewrite (IH _ _ _ _ m').
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate_in_fail_add :
  forall ns f from to ms m' x x0 adj map,
    NSet.In from adj ->
    In from ns ->
    NoDup ns ->
    In Fail (f from to) -> 
    f from to = Aggregate m' :: ms ->
    NMap.find from map = Some x0 ->
    sum_fail_map_incoming ns (update2 f from to ms) to adj (NMap.add from (x0 * x) map) =
    sum_fail_map_incoming ns f to adj map * x.
Proof.
elim => //=.
move => n ns IH f from to ms m' x x0 adj map H_ins H_in H_nd H_in' H_eq H_find.
case: H_in => H_in.
  inversion H_nd.
  rewrite H_in.
  rewrite H_in {H_in l x1 H H0 n H_nd} in H1.
  have H_in'' := H_in'.
  rewrite H_eq in H_in''.
  case: H_in'' => H_in'' //.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite /sum_fail_map.
  case (in_dec _ _) => H_dec' //=.
  case (in_dec _ _) => H_dec'' //=.
  case H_mem: (NSet.mem _ _).
    rewrite /sum_fold.
    case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|].
    - rewrite H_find'' in H_find.
      injection H_find => H_eq'.
      rewrite H_eq'.
      rewrite NMapFacts.add_eq_o // in H_find'.
      injection H_find' => H_eq''.
      rewrite -H_eq''.
      by gsimpl.
    - by rewrite H_find'' in H_find.
    - by rewrite NMapFacts.add_eq_o in H_find'.
    - by rewrite H_find'' in H_find.
  apply NSetFacts.mem_1 in H_ins.
  by rewrite H_ins in H_mem.
inversion H_nd.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ _ H_eq) //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
rewrite /sum_fail_map /sum_fold.
case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|] //.
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  injection H_find'' => H_eq'.
  rewrite H_eq'.
  by aac_reflexivity.
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.  
- apply NMapFacts.find_mapsto_iff in H_find''.
  apply (NMapFacts.add_neq_mapsto_iff _ (x0 * x) _ H_neq) in H_find''.
  apply NMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find' in H_find''.
- by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_update2_aggregate_in_fail :
  forall ns f from to ms m' adj map,
    In from ns ->
    NoDup ns ->
    f from to = Aggregate m' :: ms ->
    sum_fail_map_incoming ns (update2 f from to ms) to adj map =
    sum_fail_map_incoming ns f to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms m' adj map H_in H_nd H_eq.
inversion H_nd => {x l H H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  rewrite H_eq.
  rewrite /sum_fail_map.
  by case (in_dec _ _ _) => /= H_dec'; case (in_dec _ _ _) => /= H_dec''.
have H_neq: from <> n by move => H_eq'; rewrite -H_eq' in H1.
rewrite (IH _ _ _ _ _ _ _ _ _ H_eq) //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
Qed.

Lemma sum_fail_map_incoming_update2_remove_eq :
  forall ns f from to ms adj map,
  ~ In from ns ->
  sum_fail_map_incoming ns (update2 f from to ms) to (NSet.remove from adj) (NMap.remove from map) =
  sum_fail_map_incoming ns (update2 f from to ms) to adj map.
Proof.
elim => //=.
move => n ns IH f from to ms adj map H_in.
have H_neq: from <> n by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite {2 4}/update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and' //.
- rewrite /sum_fold.
  case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|] //.
  * apply NMapFacts.find_mapsto_iff in H_find'.
    apply NMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply NMapFacts.find_mapsto_iff in H_find'.
    rewrite H_find' in H_find''.
    injection H_find'' => H_eq'.
    rewrite H_eq'.
    by aac_reflexivity.
  * apply NMapFacts.find_mapsto_iff in H_find'.
    apply NMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply NMapFacts.find_mapsto_iff in H_find'.
    by rewrite H_find' in H_find''.
  * apply NMapFacts.find_mapsto_iff in H_find''.
    apply (NMapFacts.remove_neq_mapsto_iff _ m1 H_neq) in H_find''.
    apply NMapFacts.find_mapsto_iff in H_find''.
    by rewrite H_find' in H_find''.
- move: H_and =>  [H_dec' H_mem].
  case: H_and'.
  split => //.
  apply NSetFacts.mem_2 in H_mem.
  apply NSetFacts.mem_1.
  by apply NSetFacts.remove_3 in H_mem.
- move: H_and' => [H_dec' H_mem].
  apply NSetFacts.mem_2 in H_mem.
  case: H_and.
  split => //.
  apply NSetFacts.mem_1.
  by apply NSetFacts.remove_2.
Qed.

Lemma sum_fail_map_incoming_fail_remove_eq :
  forall ns f from to ms x adj map,
    In from ns ->
    NoDup ns ->
    NSet.In from adj ->
    f from to = Fail :: ms ->
    ~ In Fail ms ->
    NMap.find from map = Some x ->
    sum_fail_map_incoming ns (update2 f from to ms) to (NSet.remove from adj) (NMap.remove from map) =
    sum_fail_map_incoming ns f to adj map * x^-1.
Proof.
elim => //=.
move => n ns IH f from to ms x adj map H_in H_nd H_ins H_eq H_in' H_find.
inversion H_nd.
move {x0 H0 l H H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1.
  rewrite sum_fail_map_incoming_update2_remove_eq //.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  rewrite /sum_fail_map.
  case: andP => H_and; case: andP => H_and'.
  - move: H_and => [H_f H_mem].
    move: H_f.
    by case (in_dec _ _) => /= H_f.
  - move: H_and => [H_f H_mem].
    move: H_f.
    by case (in_dec _ _) => /= H_f.
  - rewrite sum_fail_map_incoming_not_in_eq //.
    rewrite /sum_fold.
    case H_find': (NMap.find _ _) => [m0|]; last by rewrite H_find' in H_find.
    rewrite H_find in H_find'.
    inversion H_find'.
    by gsimpl.
  - case: H_and'.
    split; first by rewrite H_eq.
    exact: NSetFacts.mem_1.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
rewrite (IH _ _ _ _ x) //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq' H_eq''].
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and'.
- rewrite /sum_fold.
  case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|].
  * apply NMapFacts.find_mapsto_iff in H_find'.
    apply NMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply NMapFacts.find_mapsto_iff in H_find'.
    rewrite H_find' in H_find''.
    injection H_find'' => H_eq'.
    rewrite H_eq'.
    by aac_reflexivity.
  * apply NMapFacts.find_mapsto_iff in H_find'.
    apply NMapFacts.remove_neq_mapsto_iff in H_find' => //.
    apply NMapFacts.find_mapsto_iff in H_find'.
    by rewrite H_find' in H_find''.
  * apply NMapFacts.find_mapsto_iff in H_find''.
    apply (NMapFacts.remove_neq_mapsto_iff _ m1 H_neq) in H_find''.
    apply NMapFacts.find_mapsto_iff in H_find''.
    by rewrite H_find' in H_find''.
  * by gsimpl.
- move: H_and => [H_f H_mem].
  case: H_and'.
  split => //.
  apply NSetFacts.mem_2 in H_mem.
  apply NSetFacts.remove_3 in H_mem.
  exact: NSetFacts.mem_1.
- move: H_and' => [H_f H_mem].
  case: H_and.
  split => //.
  apply NSetFacts.mem_2 in H_mem.
  apply NSetFacts.mem_1.
  exact: NSetFacts.remove_2.
- by gsimpl.
Qed.

Lemma sum_aggregate_ms_no_aggregate_1 : 
  forall ms,
  (forall m' : m, ~ In (Aggregate m') ms) -> 
  sum_aggregate_msg ms = 1.
Proof.
elim => //.
move => mg ms IH.
case: mg; first by move => m' H_in; case (H_in m'); left.
move => H_in /=.
rewrite IH //.
move => m' H_in'.
case (H_in m').
by right.
Qed.

Lemma sum_aggregate_msg_incoming_fail_update2_eq :
  forall ns f from to ms,
    (forall m', In_all_before (Aggregate m') Fail (f from to)) ->
    In from ns ->
    NoDup ns ->
    ~ In Fail ms ->
    f from to = Fail :: ms ->
    sum_aggregate_msg_incoming ns (update2 f from to ms) to =
    sum_aggregate_msg_incoming ns f to.
Proof.
elim => //=.
move => n ns IH f from to ms H_bef H_in H_nd H_in' H_eq.
inversion H_nd => {x H l H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {n H_in} in H1. 
  case (in_dec _ _ _) => /= H_dec; case (in_dec _ _ _) => /= H_dec' //.
  - move: H_dec.
    rewrite {1}/update2.
    case (sumbool_and _ _ _ _) => H_s //.
    by case: H_s.
  - rewrite H_eq in H_dec'.
    by case: H_dec'; left.
  - rewrite {2}/update2.
    case (sumbool_and _ _ _ _) => H_s; last by case: H_s.
    rewrite sum_aggregate_msg_incoming_update2_eq //.
    have H_not_in: forall m', ~ In (Aggregate m') ms.
      move => m'.
      apply (@head_before_all_not_in _ _ _ Fail) => //.
      rewrite -H_eq.
      exact: H_bef.
    by rewrite sum_aggregate_ms_no_aggregate_1.
  - rewrite H_eq in H_dec'.
    by case: H_dec'; left.
have H_neq: from <> n by move => H_eq'; rewrite H_eq' in H_in.
case (in_dec _ _ _) => /= H_dec; case (in_dec _ _ _) => /= H_dec' //.
- by rewrite IH.
- move: H_dec.
  rewrite {1}/update2.
  by case (sumbool_and _ _ _ _) => H_dec.
- case: H_dec.
  rewrite {1}/update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq' H_eq''].
- rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_s //.
  by move: H_s => [H_eq' H_eq''].
Qed.

Lemma Nodes_data_split :
  forall ns0 ns1 state,
    Nodes_data (ns0 ++ ns1) state =
    Nodes_data ns0 state ++ Nodes_data ns1 state.
Proof.
elim => //.
move => n ns0 IH ns1 state.
rewrite /=.
by rewrite IH.
Qed.

Lemma Nodes_data_not_in_eq :
  forall ns state to d,
    ~ In to ns ->
    Nodes_data ns (update state to d) =
    Nodes_data ns state.
Proof.
elim => //.
move => n ns IH state to d H_in.
rewrite /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite {1}/update /=.
case name_eq_dec => H_dec //.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma sum_sent_distr : 
  forall dl dl',
    sum_sent (dl ++ dl') = sum_sent dl * sum_sent dl'.
Proof.
elim => /=; first by move => dl'; gsimpl.
move => d dl IH dl'.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_received_distr : 
  forall dl dl',
    sum_received (dl ++ dl') = sum_received dl * sum_received dl'.
Proof.
elim => /=; first by move => dl'; gsimpl.
move => d dl IH dl'.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma in_not_in_exclude : 
  forall ns ns' n,
    In n ns' ->
    ~ In n (exclude ns' ns).
Proof.
elim => //=; first by move => ns' n H_in H_n.
move => n ns IH ns' n' H_in.
case (in_dec _ _) => H_dec; first exact: IH.
move => H_in'.
case: H_in' => H_in'; first by rewrite H_in' in H_dec.
contradict H_in'.
exact: IH.
Qed.

Lemma sum_fail_map_incoming_sent_neq_eq_alt :
  forall ns packets state from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (adjacent (update state h d n))
    (sent (update state h d n)) =
  sum_fail_map_incoming ns packets n (adjacent (state n)) (sent (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update.
case (name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt2 :
  forall ns0 ns1 packets state from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 (update2 packets from to ms) (update state h d) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms h d H_in H_in'.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
rewrite sum_fail_map_incoming_sent_neq_eq_alt //.
rewrite -/(sum_fail_sent_incoming_active _ _ _ _).
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
have IH' := IH ns1 packets state from to ms h d H_inn H_inn'.
by rewrite IH'.
Qed.

Lemma sum_fail_map_incoming_received_neq_eq_alt :
  forall ns packets state from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (adjacent (update state h d n))
    (received (update state h d n)) =
  sum_fail_map_incoming ns packets n (adjacent (state n)) (received (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update.
case (name_eq_dec _ _) => H_dec //=.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec' => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt2 :
  forall ns0 ns1 packets state from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_received_incoming_active ns1 ns0 (update2 packets from to ms) (update state h d) =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms h d H_in H_in'.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
rewrite sum_fail_map_incoming_received_neq_eq_alt //.
rewrite -/(sum_fail_received_incoming_active _ _ _ _).
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
have IH' := IH ns1 packets state from to ms h d H_inn H_inn'.
by rewrite -IH'.
Qed.

(* FIXME *)
Lemma sum_fail_map_incoming_update2_not_eq :
  forall ns f h n ms adj map,
      h <> n ->
      sum_fail_map_incoming ns (update2 f h n ms) h adj map =
      sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n0 l IH f h n ms adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_map_incoming_add_aggregate_eq :
  forall ns f x h x0 m' adj map,
    h <> x ->
    In x ns ->
    NoDup ns ->
    In Fail (f x h) ->
    NMap.find x map = Some x0 ->
    NSet.In x adj ->
    sum_fail_map_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) h adj (NMap.add x (x0 * m') map) =
    sum_fail_map_incoming ns f h adj map * m'.
Proof.
elim => //.
move => n ns IH f x h x0 m' adj map H_neq H_in H_nd H_in' H_find H_ins.
rewrite /=.
inversion H_nd => {x1 H l H0}.
case: H_in => H_in.
  rewrite -H_in.
  rewrite -H_in {H_in x} in H_in' H_neq H_find H_ins.
  rewrite sum_fail_map_incoming_update2_not_eq //.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite /sum_fail_map.
  case (in_dec _ _ _) => /= H_dec' //=.
  case H_mem: (NSet.mem _ _); last by rewrite NSetFacts.mem_1 in H_mem.
  rewrite /sum_fold.
  case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|].
  - rewrite NMapFacts.add_eq_o // in H_find'.
    inversion H_find'.
    rewrite H_find'' in H_find.
    inversion H_find.
    by gsimpl.
  - by rewrite H_find'' in H_find.
  - by rewrite NMapFacts.add_eq_o // in H_find'.
  - by rewrite H_find'' in H_find.
rewrite IH //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec //; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
have H_neq': x <> n by move => H_eq; rewrite H_eq in H_in.
rewrite /sum_fail_map.
rewrite /sum_fold.
case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|].
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  inversion H_find''.
  by case: andP => H_and; gsimpl; aac_reflexivity.  
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.
- apply NMapFacts.find_mapsto_iff in H_find''.
  apply (NMapFacts.add_neq_mapsto_iff _ (x0 * m') _ H_neq') in H_find''.
  apply NMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find'' in H_find'.
- by gsimpl; aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_not_in_fail_add_update2_eq :
  forall ns f h x ms m' adj map,
    h <> x ->
    In x ns ->
    NoDup ns ->
    ~ In Fail (f x h) ->
    sum_fail_map_incoming ns (update2 f h x ms) h adj (NMap.add x m' map) =
    sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n ns IH f h x ms m' adj map H_neq H_in H_nd H_in'.
inversion H_nd => {l H0 x0 H H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {n H_in} in H1.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq'].
  rewrite sum_fail_map_incoming_add_not_in_eq //.
  rewrite sum_fail_map_incoming_update2_not_eq //.
  rewrite /sum_fail_map.
  by case (in_dec _ _) => /= H_dec'.
have H_neq': x <> n by move => H_eq; rewrite H_eq in H_in.
rewrite IH //.
rewrite /update2.
case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite /sum_fail_map /sum_fold.
case H_find': (NMap.find _ _) => [m0|]; case H_find'': (NMap.find _ _) => [m1|].
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  rewrite H_find' in H_find''.
  inversion H_find''.
  by case: andP => H_and; gsimpl; aac_reflexivity.  
- apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  by rewrite H_find' in H_find''.
- apply NMapFacts.find_mapsto_iff in H_find''.
  apply (NMapFacts.add_neq_mapsto_iff _ m' _ H_neq') in H_find''.
  apply NMapFacts.find_mapsto_iff in H_find''.
  by rewrite H_find'' in H_find'.
- by gsimpl; aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_not_in_fail_update2_eq :
  forall ns f h x ms adj map,
    h <> x ->
    sum_fail_map_incoming ns (update2 f h x ms) h adj map =
    sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n ns IH f h x ms adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_update_not_in_eq :
  forall ns0 ns1 packets state h d,
    ~ In h ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 packets (update state h d) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_update_not_in_eq :
  forall ns0 ns1 packets state h d,
    ~ In h ns0 ->
    sum_fail_received_incoming_active ns1 ns0 packets (update state h d) =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_map_incoming_update2_app_eq : 
  forall ns f h x n m' adj map,
    sum_fail_map_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) n adj map = 
    sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n ns IH f h x n0 m' adj map.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _ _ _) => /= H_dec //.
rewrite /sum_fail_map.
case: andP => H_and; case: andP => H_and' //.
  move: H_dec => [H_eq H_eq'].
  rewrite H_eq H_eq' {h x H_eq H_eq'} in H_and H_and'.
  move: H_and => [H_dec' H_mem].
  move: H_dec'.
  case (in_dec _ _) => /= H_dec' H_eq //.
  apply in_app_or in H_dec'.
  case: H_dec' => H_dec'; last by case: H_dec'.
  case: H_and'.
  split => //.
  by case (in_dec _ _).
move: H_dec => [H_eq H_eq'].
rewrite H_eq H_eq' {h x H_eq H_eq'} in H_and H_and'.
move: H_and' => [H_dec' H_mem].
move: H_dec'.
case (in_dec _ _) => /= H_dec' H_eq //.
case: H_and.
case (in_dec _ _) => /= H_dec //.
split => //.
case: H_dec.
apply in_or_app.
by left.
Qed.

Lemma sum_fail_sent_incoming_active_update2_app_eq :
  forall ns0 ns1 packets state h x m',
    sum_fail_sent_incoming_active ns1 ns0 (update2 packets h x (packets h x ++ [Aggregate m'])) state =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h x m'.
rewrite IH //.
by rewrite sum_fail_map_incoming_update2_app_eq.
Qed.

Lemma sum_fail_received_incoming_active_update2_app_eq :
  forall ns0 ns1 packets state h x m',
    sum_fail_received_incoming_active ns1 ns0 (update2 packets h x (packets h x ++ [Aggregate m'])) state =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h x m'.
rewrite IH //.
by rewrite sum_fail_map_incoming_update2_app_eq.
Qed.

Lemma sum_sent_step_o_init : 
  forall ns, sum_sent ((Nodes_data ns) init_handlers) = 1.
Proof.
elim => //=.
move => n ns IH.
rewrite IH sumM_init_map_1.
by gsimpl.
Qed.

Lemma sum_received_step_o_init : 
  forall ns, sum_received ((Nodes_data ns) init_handlers) = 1.
Proof.
elim => //=.
move => n ns IH.
rewrite IH sumM_init_map_1.
by gsimpl.
Qed.

Lemma sum_fail_map_incoming_init : 
  forall ns1 ns0 n,
    sum_fail_map_incoming ns1 (fun _ _ : name => []) n (adjacency n ns0) (init_map (adjacency n ns0)) = 1.
Proof.
elim => //=.
move => n ns IH ns0 n0.
rewrite IH.
rewrite /sum_fail_map.
case: andP => H_and; last by gsimpl.
move: H_and => [H_eq H_eq'].
by contradict H_eq.
Qed.

Lemma sum_fail_sent_incoming_active_step_o_init :
  forall ns0 ns1, sum_fail_sent_incoming_active ns1 ns0 (fun _ _ => []) init_handlers = 1.
Proof.
elim => //=.
move => n ns0 IH ns1.
rewrite IH sum_fail_map_incoming_init.
by gsimpl.
Qed.

Lemma sum_fail_received_incoming_active_step_o_init :
  forall ns0 ns1, sum_fail_received_incoming_active ns1 ns0 (fun _ _ => []) init_handlers = 1.
Proof.
elim => //=.
move => n ns0 IH ns1.
rewrite IH sum_fail_map_incoming_init.
by gsimpl.
Qed.

Lemma nodup_in_not_in_right : 
  forall ns0 ns1 (x : name),
    NoDup (ns0 ++ ns1) -> In x ns0 -> ~ In x ns1.
Proof.
elim => //=.
move => n ns0 IH ns1 x H_nd H_in.
inversion H_nd => {l H0 x0 H}.
case: H_in => H_in; last exact: IH.
rewrite H_in in H1.
move => H_in'.
case: H1.
apply in_or_app.
by right.
Qed.

Lemma nodup_in_not_in_left : 
  forall ns0 ns1 (x : name),
    NoDup (ns0 ++ ns1) -> In x ns1 -> ~ In x ns0.
Proof.
elim => [|n ns0 IH] ns1 x H_nd H_in //.
inversion H_nd => {l H0 x0 H}.
move => H_in'.
case: H_in' => H_in'.
  rewrite H_in' in H1.
  case: H1.
  apply in_or_app.
  by right.
contradict H_in'.
exact: (IH _ _ H2).
Qed.

Lemma nodup_app_split_left : 
  forall (ns0 ns1 : list name), 
    NoDup (ns0 ++ ns1) -> NoDup ns0.
Proof.
elim => [|n ns0 IH] ns1 H_nd; first exact: NoDup_nil.
inversion H_nd => {l H0 x H}.
apply NoDup_cons.
  move => H_in.
  case: H1.
  apply in_or_app.
  by left.
move: H2.
exact: IH.
Qed.

Lemma nodup_app_split_right : 
  forall (ns0 ns1 : list name), 
    NoDup (ns0 ++ ns1) -> NoDup ns1.
Proof.
elim => [|n ns0 IH] ns1 H_nd //.
inversion H_nd => {l H0 x H}.
exact: IH.
Qed.

Lemma sum_aggregate_msg_incoming_app_aggregate_eq :
  forall ns f h x m',
    In h ns ->
    NoDup ns ->
    ~ In Fail (f h x) ->
    sum_aggregate_msg_incoming ns (update2 f h x (f h x ++ [Aggregate m'])) x =
    sum_aggregate_msg_incoming ns f x * m'.
Proof.
elim => //.
move => n ns IH f h x m' H_in H_nd H_in'.
inversion H_nd => {x0 H H0 l H_nd}.
case: H_in => H_in.
  rewrite H_in in H1.
  rewrite H_in {H_in n}.
  rewrite /=.
  rewrite sum_aggregate_msg_incoming_update2_eq //.
  case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
    case: H_dec'.
    move: H_dec.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move => H_in.
    apply in_app_or in H_in.
    case: H_in => H_in //.
    by case: H_in.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_and; last by case: H_and.
  rewrite sum_aggregate_msg_split /=.
  by gsimpl.
rewrite /= IH //.
have H_neq: h <> n by move => H_eq; rewrite H_eq in H_in.
case (in_dec _ _) => /= H_dec; case (in_dec _ _) => /= H_dec' //.
- by aac_reflexivity.
- case: H_dec'.
  move: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq H_eq'].
- case: H_dec.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by move: H_dec => [H_eq H_eq'].
- rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_eq H_eq'].
  by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_in_update2_app_eq :
  forall ns0 ns1 f x h m',
    NoDup ns0 ->
    NoDup ns1 ->
    In x ns0 ->
    In h ns1 ->
    ~ In h ns0 ->
    ~ In Fail (f h x) ->
    sum_aggregate_msg_incoming_active ns1 ns0 (update2 f h x (f h x ++ [Aggregate m'])) =
    sum_aggregate_msg_incoming_active ns1 ns0 f * m'.
Proof.
elim => //=.
move => n ns0 IH ns1 f x h m' H_nd H_nd' H_in H_inn H_in' H_f.
have H_neq: h <> n by move => H_neq; case: H_in'; left.
have H_nin: ~ In h ns0 by move => H_nin; case: H_in'; right.
move {H_in'}.
inversion H_nd => {l x0 H H0 H_nd}.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in {H_in n} in H1 H_neq.
  rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
  rewrite sum_aggregate_msg_incoming_app_aggregate_eq //.
  by gsimpl.
have H_neq': n <> x by move => H_eq; rewrite -H_eq in H_in.
rewrite IH //.
rewrite sum_aggregate_msg_incoming_neq_eq //.
by aac_reflexivity.
Qed.

Lemma exclude_failed_not_in :
  forall ns h failed,
    ~ In h ns ->
    exclude (h :: failed) ns = exclude failed ns.
Proof.
elim => //.
move => n ns IH h failed H_in.
have H_neq: h <> n by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite /=.
case name_eq_dec => H_dec //.
case (in_dec _ _) => H_dec'; first exact: IH.
by rewrite IH.
Qed.

Lemma exclude_in_app : 
  forall ns ns0 ns1 h failed, 
  NoDup ns ->
  exclude failed ns = ns0 ++ h :: ns1 -> 
  exclude (h :: failed) ns = ns0 ++ ns1.
Proof.
elim; first by case.
move => n ns IH ns0 ns1 h failed H_nd.
inversion H_nd => {x H0 l H H_nd}.
rewrite /=.
case (in_dec _ _) => H_dec; case name_eq_dec => H_dec' H_eq.
- exact: IH.
- exact: IH.
- rewrite -H_dec' {n H_dec'} in H_eq H1 H_dec.
  case: ns0 H_eq.
    rewrite 2!app_nil_l.
    move => H_eq.
    inversion H_eq.
    by rewrite exclude_failed_not_in.
  move => x ns' H_eq.
  inversion H_eq => {H_eq}.
  rewrite H0 {h H0} in H1 H_dec.
  have H_in: In x (exclude failed ns).
    rewrite H3.
    apply in_or_app.
    by right; left.
  by apply exclude_in in H_in.
- case: ns0 H_eq.
    rewrite app_nil_l.
    move => H_eq.
    inversion H_eq.
    by rewrite H0 in H_dec'.
  move => n' ns0 H_eq.
  inversion H_eq.
  by rewrite (IH _ _ _ _ _ H3).
Qed.

Lemma sum_sent_Nodes_data_distr : 
  forall ns0 ns1 state,
    sum_sent (Nodes_data ns0 state) * sum_sent (Nodes_data ns1 state) =
    sum_sent (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => [|n ns0 IH] ns1 net /=; first by gsimpl.
rewrite -IH.
by aac_reflexivity.
Qed.

Lemma sum_received_Nodes_data_distr : 
  forall ns0 ns1 state,
    (sum_received (Nodes_data ns1 state))^-1 * (sum_received (Nodes_data ns0 state))^-1 = 
    (sum_received (Nodes_data (ns0 ++ ns1) state))^-1.
Proof.
elim => [|n ns0 IH] ns1 state /=; first by gsimpl.
gsimpl.
rewrite -IH.
by aac_reflexivity.
Qed.

(* FIXME *)
Lemma adjacent_to_node_self_eq :
  forall ns0 ns1 h,
  adjacent_to_node h (ns0 ++ h :: ns1) = adjacent_to_node h (ns0 ++ ns1).
Proof.
elim => [|n ns0 IH] ns1 h /=.
  case (adjacent_to_dec _ _) => /= H_dec //.
  by apply adjacent_to_irreflexive in H_dec.
case (adjacent_to_dec _ _) => /= H_dec //.
by rewrite IH.
Qed.

Lemma exclude_in_split_eq :
  forall ns0 ns1 ns failed h,
    exclude (h :: failed) (ns0 ++ h :: ns1) = ns ->
    exclude (h :: failed) (h :: ns0 ++ ns1) = ns.
Proof.
elim => //.
move => n ns IH ns1 ns' failed h.
rewrite /=.
case name_eq_dec => H_dec; case name_eq_dec => H_dec' //.
  move => H_ex.
  apply IH in H_ex.
  move: H_ex.
  rewrite /=.
  by case name_eq_dec.
case (in_dec _ _ _) => H_dec''.
  move => H_ex.
  apply IH in H_ex.
  move: H_ex.
  rewrite /=.
  by case name_eq_dec.
move => H_ex.
case: ns' H_ex => //.
move => a ns' H_ex.
inversion H_ex.
rewrite H1.
apply IH in H1.
move: H1.
rewrite /=.
case name_eq_dec => H_ex_dec //.
move => H.
by rewrite H.
Qed.

Lemma permutation_split : 
  forall (ns : list name) ns' n,
  Permutation (n :: ns) ns' ->
  exists ns0, exists ns1, ns' = ns0 ++ n :: ns1.
Proof.
move => ns ns' n H_pm.
have H_in: In n (n :: ns) by left. 
have H_in': In n ns'.
  move: H_pm H_in. 
  exact: Permutation_in.
by apply In_split in H_in'.
Qed.

Lemma sum_aggregate_msg_incoming_permutation_eq :
  forall ns1 ns1' f h,
  Permutation ns1 ns1' ->
  sum_aggregate_msg_incoming ns1 f h =
  sum_aggregate_msg_incoming ns1' f h.
Proof.
elim => //=.
  move => ns1' f h H_eq.
  apply Permutation_nil in H_eq.
  by rewrite H_eq.
move => n ns IH ns1' f h H_pm.
have H_pm' := H_pm.
apply permutation_split in H_pm.
move: H_pm => [ns0 [ns1 H_eq]].
rewrite H_eq in H_pm'.
rewrite H_eq {H_eq ns1'}.
apply Permutation_cons_app_inv in H_pm'.
rewrite (IH _ _ _ H_pm').
rewrite 2!sum_aggregate_msg_incoming_split /=.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_permutation_eq :
  forall ns1 ns1' ns0 state,
  Permutation ns1 ns1' ->
  sum_aggregate_msg_incoming_active ns1 ns0 state =
  sum_aggregate_msg_incoming_active ns1' ns0 state.
Proof.
move => ns1 ns1' ns0.
move: ns0 ns1 ns1'.
elim => //=.
move => n ns IH ns1 ns1' net H_pm.
rewrite (IH _ _ _ H_pm).
by rewrite (sum_aggregate_msg_incoming_permutation_eq _ _ H_pm).
Qed.

Lemma sum_fail_map_incoming_split : 
  forall ns0 ns1 f h adj map,
    sum_fail_map_incoming (ns0 ++ ns1) f h adj map =
    sum_fail_map_incoming ns0 f h adj map * sum_fail_map_incoming ns1 f h adj map.
Proof.
elim => [|n ns0 IH] ns1 f h adj map; first by gsimpl.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_fail_map_incoming_permutation_eq :
  forall ns1 ns1' f h adj map,
  Permutation ns1 ns1' ->
  sum_fail_map_incoming ns1 f h adj map =
  sum_fail_map_incoming ns1' f h adj map.
Proof.
elim => //=.
  move => ns1' f h adj map H_eq.
  apply Permutation_nil in H_eq.
  by rewrite H_eq.
move => n ns IH ns1' f h adj map H_pm.
have H_pm' := H_pm.
apply permutation_split in H_pm.
move: H_pm => [ns0 [ns1 H_eq]].
rewrite H_eq in H_pm'.
rewrite H_eq {H_eq ns1'}.
apply Permutation_cons_app_inv in H_pm'.
rewrite (IH _ _ _ _ _ H_pm').
rewrite 2!sum_fail_map_incoming_split /=.
by gsimpl.
Qed.

Lemma sum_fail_sent_incoming_active_permutation_eq :
  forall ns1 ns1' ns packets state,
  Permutation ns1 ns1' ->
  sum_fail_sent_incoming_active ns1 ns packets state =
  sum_fail_sent_incoming_active ns1' ns packets state.
Proof.
move => ns1 ns1' ns.
elim: ns ns1 ns1' => [|n ns IH] ns1 ns1' packets state H_pm //=.
rewrite (IH _ _ _ _ H_pm).
by rewrite (sum_fail_map_incoming_permutation_eq _ _ _ _ H_pm).
Qed.

Lemma sum_fail_received_incoming_active_permutation_eq :
  forall ns1 ns1' ns packets state,
  Permutation ns1 ns1' ->
  sum_fail_received_incoming_active ns1 ns packets state =
  sum_fail_received_incoming_active ns1' ns packets state.
Proof.
move => ns1 ns1' ns.
elim: ns ns1 ns1' => [|n ns IH] ns1 ns1' packets state H_pm //=.
rewrite (IH _ _ _ _ H_pm).
by rewrite (sum_fail_map_incoming_permutation_eq _ _ _ _ H_pm).
Qed.

Lemma sumM_sumM_active_eq : 
  forall (ns : list name) (adj adj' : NS) (map : NM) (f : name -> name -> list Msg) (n : name),
  NoDup ns ->
  (forall n', In Fail (f n' n) -> ~ In n' ns) ->
  (forall n', NSet.In n' adj' -> NSet.In n' adj /\ ~ In Fail (f n' n)) ->
  (forall n', NSet.In n' adj -> NSet.In n' adj' \/ In Fail (f n' n)) ->
  (forall n', NSet.In n' adj -> exists m', NMap.find n' map = Some m') ->
  (forall n', NSet.In n' adj -> (In n' ns \/ In Fail (f n' n))) ->
  sumM adj' map = sumM_active adj map ns.
Proof.
elim => [|n' ns IH] adj adj' map f n H_nd H_f H_and H_or H_ex_map H_ex_nd /=.
- case H_emp: (NSet.is_empty adj').
    apply NSet.is_empty_spec in H_emp. 
    rewrite /sumM sumM_fold_right.
    apply NSetProps.elements_Empty in H_emp.
    by rewrite H_emp.
  have H_not: ~ NSet.Empty adj'.
    move => H_not.
    apply NSet.is_empty_spec in H_not. 
    by rewrite H_emp in H_not. 
  rewrite /NSet.Empty in H_not.
  contradict H_not.
  move => n' H_ins.
  apply H_and in H_ins as [H_ins H_q'].
  apply H_ex_nd in H_ins.
  by case: H_ins => H_ins.
- inversion H_nd; subst.
  rewrite /= /sum_active_fold /sum_fold.
  case H_mem: (NSet.mem n' adj).
    apply NSetFacts.mem_2 in H_mem.
    case H_find: (NMap.find n' map) => [m'|]; last first.
      apply H_ex_map in H_mem as [m' H_find'].
      by rewrite H_find in H_find'.
    have H_or' :=  H_mem.
    apply H_or in H_or'.
    case: H_or' => H_or'; last first.
      apply (H_f n') in H_or'.
      contradict H_or'.
      by left.
    have ->: sumM adj' map = sumM adj' map * m'^-1 * m' by gsimpl.
    rewrite -(sumM_remove H_or' H_find).
    rewrite (sumM_active_remove_eq _ _ _ _ H1).
    rewrite (IH (NSet.remove n' adj) _ map f n H2) //.
    * move => n0 H_in.
      apply H_f in H_in.
      move => H_in'.
      by case: H_in; right.
    * move => n0 H_ins.
      have H_neq: n' <> n0.
        move => H_eq'.
        rewrite H_eq' in H_ins. 
        by apply NSetFacts.remove_1 in H_ins.
      apply NSetFacts.remove_3 in H_ins.
      apply H_and in H_ins as [H_ins' H_not].
      split => //.
      by apply NSetFacts.remove_2.
    * move => n0 H_ins.
      have H_ins' := H_ins.
      apply NSetFacts.remove_3 in H_ins'.
      have H_neq: n' <> n0.
        move => H_eq'.
        rewrite H_eq' in H_ins. 
        by apply NSetFacts.remove_1 in H_ins.
      apply H_or in H_ins'.
      case: H_ins' => H_ins'; last by right.
      left.
      by apply NSetFacts.remove_2.
    * move => n0 H_ins.
      apply NSetFacts.remove_3 in H_ins.
      by apply H_ex_map.
    * move => n0 H_ins.
      have H_ins': NSet.In n0 adj by apply NSetFacts.remove_3 in H_ins.
      case (H_ex_nd n0 H_ins') => H_or''; last by right.
      have H_neq: n' <> n0.
        move => H_eq'.
        rewrite H_eq' in H_ins. 
        by apply NSetFacts.remove_1 in H_ins. 
      case: H_or'' => H_or'' //.
      by left.
  have H_ins: ~ NSet.In n' adj by move => H_ins; apply NSetFacts.mem_1 in H_ins; rewrite H_ins in H_mem.
  rewrite (IH adj adj' map f n H2) //.
    move => n0 H_f'.
    apply H_f in H_f'.
    move => H_in.
    by case: H_f'; right.
  move => n0 H_ins'. 
  case (H_ex_nd n0 H_ins') => H_or'; last by right.
  have H_neq: n' <> n0.
    move => H_eq'.
    by rewrite H_eq' in H_ins.
  case: H_or' => H_or' //.
  by left.
Qed.

Lemma sum_fail_map_incoming_remove_not_in_eq :
  forall ns f adj map n n',
  ~ In n' ns ->
  sum_fail_map_incoming ns f n (NSet.remove n' adj) map =
  sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n0 ns IH f adj map n n' H_in.
have H_neq: n' <> n0 by move => H_eq; case: H_in; left.
have H_in': ~ In n' ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /sum_fail_map.
case in_dec => /= H_adj //.
case: ifP => H_mem; case: ifP => H_mem' //.
  apply NSetFacts.mem_2 in H_mem.
  have H_ins: ~ NSet.In n0 adj.
    move => H_ins.
    apply NSetFacts.mem_1 in H_ins.
    by rewrite H_mem' in H_ins.
  by apply NSetFacts.remove_3 in H_mem.
apply NSetFacts.mem_2 in H_mem'.
have H_ins: ~ NSet.In n0 (NSet.remove n' adj).
  move => H_ins.
  apply NSetFacts.mem_1 in H_ins.
  by rewrite H_ins in H_mem.
case: H_ins.
exact: NSetFacts.remove_2.
Qed.

Lemma sumM_remove_fail_ex_eq : 
  forall ns f adj map n,
    NoDup ns ->
    (forall n', NSet.In n' adj -> In n' ns) ->
    (forall n', NSet.In n' adj -> exists m', NMap.find n' map = Some m') ->
    exists adj', 
      sumM adj map * (sum_fail_map_incoming ns f n adj map)^-1 = sumM adj' map /\
      (forall n', NSet.In n' adj' -> (NSet.In n' adj /\ ~ In Fail (f n' n))) /\
      (forall n', NSet.In n' adj -> (NSet.In n' adj' \/ In Fail (f n' n))).
Proof.
elim => [|n' ns IH] /= f adj map n H_nd H_in_tot H_ex.
  exists adj.
  split; first by gsimpl.
  by split => n' H_ins; apply H_in_tot in H_ins.
inversion H_nd => {l x H H0 H_nd}.
have H_in_tot': forall n0, NSet.In n0 (NSet.remove n' adj) -> In n0 ns.
  move => n0 H_ins.
  have H_neq: n' <> n0 by move => H_eq; rewrite H_eq in H_ins; apply NSetFacts.remove_1 in H_ins.
  apply NSetFacts.remove_3 in H_ins.
  apply H_in_tot in H_ins.
  by case: H_ins => H_ins.
have H_ex': forall n0, NSet.In n0 (NSet.remove n' adj) -> exists m', NMap.find n0 map = Some m'.
  move => n0 H_ins.
  apply: H_ex.
  by apply NSetFacts.remove_3 in H_ins.
have [adj' [H_eq [H_and H_or]]] := IH f (NSet.remove n' adj) map n H2 H_in_tot' H_ex'.
move {IH H_in_tot' H_ex'}.
rewrite /sum_fail_map.
case: in_dec => /= H_in.
  case: ifP => H_mem.
    apply NSetFacts.mem_2 in H_mem.
    have [m' H_find] := H_ex _ H_mem.
    exists adj'; split.
      rewrite -H_eq.    
      rewrite (sumM_remove H_mem H_find).
      gsimpl.
      rewrite /sum_fold.
      case H_find': (NMap.find _ _) => [m0|]; last by rewrite H_find in H_find'.
      rewrite H_find in H_find'.
      inversion H_find'.
      gsimpl.
      by rewrite sum_fail_map_incoming_remove_not_in_eq.
    split.
      move => n0 H_ins.
      apply H_and in H_ins.
      move: H_ins => [H_ins H_in'].
      by apply NSetFacts.remove_3 in H_ins.
    move => n0 H_ins.
    have H_ins' := H_ins.
    apply H_in_tot in H_ins'.
    case: H_ins' => H_ins'; first by rewrite -H_ins'; right.
    have H_neq: n' <> n0 by move => H_eq'; rewrite -H_eq' in H_ins'.
    have H_ins_n0: NSet.In n0 (NSet.remove n' adj) by apply NSetFacts.remove_2.
    by apply H_or in H_ins_n0.
  move/negP: H_mem => H_mem.
  have H_ins: ~ NSet.In n' adj by move => H_ins; case: H_mem; apply NSetFacts.mem_1.
  move {H_mem}.
  exists adj'.
  split.
    gsimpl.
    rewrite -H_eq.
    have H_equ: NSet.Equal adj (NSet.remove n' adj).
      split => H_ins'.
        have H_neq: n' <> a by move => H_eq'; rewrite -H_eq' in H_ins'.
        by apply NSetFacts.remove_2.
      by apply NSetFacts.remove_3 in H_ins'.
    rewrite -(sumM_eq _ H_equ).
    by rewrite sum_fail_map_incoming_remove_not_in_eq.
  split.
    move => n0 H_ins'.
    apply H_and in H_ins'.
    move: H_ins' => [H_ins' H_in'].
    by apply NSetFacts.remove_3 in H_ins'.
  move => n0 H_ins'.
  have H_ins_n0 := H_ins'.
  apply H_in_tot in H_ins_n0.
  case: H_ins_n0 => H_ins_n0; first by rewrite -H_ins_n0; right.
  have H_neq: n' <> n0 by move => H_eq'; rewrite -H_eq' in H_ins'.
  have H_insr: NSet.In n0 (NSet.remove n' adj) by apply NSetFacts.remove_2.
  by apply H_or in H_insr.
case H_mem: (NSet.mem n' adj).
  apply NSetFacts.mem_2 in H_mem.
  have H_find := H_mem.
  apply H_ex in H_find.
  move: H_find => [m' H_find].
  rewrite (sumM_remove H_mem H_find) in H_eq.
  exists (NSet.add n' adj').
  split.
    gsimpl.
    have H_ins: ~ NSet.In n' adj'.
      move => H_ins.
      apply H_and in H_ins.
      move: H_ins => [H_ins H_f].
      by apply NSetFacts.remove_1 in H_ins.
    rewrite (sumM_add H_ins H_find).
    rewrite -H_eq.
    rewrite sum_fail_map_incoming_remove_not_in_eq //.
    set s1 := sumM _ _.
    set s2 := sum_fail_map_incoming _ _ _ _ _.
    suff H_suff: s1 * s2^-1 = s1 * s2^-1 * m' * m'^-1 by rewrite H_suff; aac_reflexivity.
    by gsimpl.    
  split.
    move => n0 H_ins.
    case (name_eq_dec n' n0) => H_dec; first by rewrite -H_dec.
    apply NSetFacts.add_3 in H_ins => //.
    apply H_and in H_ins.
    move: H_ins => [H_ins H_f].
    by apply NSetFacts.remove_3 in H_ins.
  move => n0 H_ins.
  case (name_eq_dec n' n0) => H_dec; first by left; rewrite H_dec; apply NSetFacts.add_1.
  have H_ins': NSet.In n0 (NSet.remove n' adj) by apply NSetFacts.remove_2.
  apply H_or in H_ins'.
  case: H_ins' => H_ins'; last by right.
  left.
  exact: NSetFacts.add_2.
move/negP: H_mem => H_mem.
have H_ins: ~ NSet.In n' adj by move => H_ins; case: H_mem; apply NSetFacts.mem_1.
move {H_mem}.
exists adj'.
split.
  gsimpl.
  rewrite -H_eq.
  have H_equ: NSet.Equal adj (NSet.remove n' adj).
    split => H_ins'.
      have H_neq: n' <> a by move => H_eq'; rewrite -H_eq' in H_ins'.
      by apply NSetFacts.remove_2.
    by apply NSetFacts.remove_3 in H_ins'.
  rewrite -(sumM_eq _ H_equ).
  by rewrite sum_fail_map_incoming_remove_not_in_eq.
split.
  move => n0 H_ins'.
  apply H_and in H_ins'.
  move: H_ins' => [H_ins' H_and'].
  by apply NSetFacts.remove_3 in H_ins'.
move => n0 H_ins'.
have H_neq: n' <> n0 by move => H_eq'; rewrite -H_eq' in H_ins'.
have H_ins_n0: NSet.In n0 (NSet.remove n' adj) by apply NSetFacts.remove_2.
apply H_or in H_ins_n0.
case: H_ins_n0 => H_ins_n0; last by right.
by left.
Qed.

Lemma sumM_sent_fail_active_eq_with_self : 
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed ->
   sumM (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) * 
     (sum_fail_map_incoming nodes onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent))^-1 =
   sumM_active (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (exclude failed nodes).
Proof.
move => onet failed tr H_st n H_f.
have H_ex_map := Aggregation_in_set_exists_find_sent H_st _ H_f.
have H_ex_nd := Aggregation_in_adj_or_incoming_fail H_st _ H_f.
assert (H_adj_in: forall (n' : name), NSet.In n' (adjacent (onwState onet n)) -> In n' nodes).
  by move => n' H_ins; exact: all_names_nodes.
have H := sumM_remove_fail_ex_eq onet.(onwPackets) n _ H_adj_in H_ex_map.
have [adj' [H_eq [H_and H_or]]] := H no_dup_nodes.
rewrite H_eq.
have H_nd: NoDup (exclude failed nodes) by apply nodup_exclude; apply no_dup_nodes.
have H_eq' := sumM_sumM_active_eq _ _ H_nd _ H_and H_or H_ex_map.
rewrite H_eq' //.
  move => n' H_f' H_in.
  contradict H_f'.
  apply: (Aggregation_not_failed_no_fail H_st).
  move => H_in'.
  contradict H_in.
  exact: in_not_in_exclude.
move => n' H_ins.
apply H_or in H_ins.
case: H_ins => H_ins; last by right.
apply H_and in H_ins.
move: H_ins => [H_ins H_f'].
left.
apply: In_n_exclude; last exact: all_names_nodes.
apply H_ex_nd in H_ins.
case: H_ins => H_ins //.
by move: H_ins => [H_ins H_ins'].
Qed.

Lemma sumM_received_fail_active_eq_with_self : 
  forall onet failed tr,
   step_o_f_star step_o_f_init (failed, onet) tr ->
   forall n, ~ In n failed ->
   sumM (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received) * 
     (sum_fail_map_incoming nodes onet.(onwPackets) n (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received))^-1 =
   sumM_active (onet.(onwState) n).(adjacent) (onet.(onwState) n).(received) (exclude failed nodes).
Proof.
move => onet failed tr H_st n H_f.
have H_ex_map := Aggregation_in_set_exists_find_received H_st _ H_f.
have H_ex_nd := Aggregation_in_adj_or_incoming_fail H_st _ H_f.
assert (H_adj_in: forall n', NSet.In n' (adjacent (onwState onet n)) -> In n' nodes). 
  by move => n' H_ins; exact: all_names_nodes.
have H := sumM_remove_fail_ex_eq onet.(onwPackets) n _ H_adj_in H_ex_map.
have [adj' [H_eq [H_and H_or]]] := H no_dup_nodes.
rewrite H_eq.
have H_nd: NoDup (exclude failed nodes) by apply nodup_exclude; apply no_dup_nodes.
have H_eq' := sumM_sumM_active_eq _ _ H_nd _ H_and H_or H_ex_map.
rewrite H_eq' //.
  move => n' H_f' H_in.
  contradict H_f'.
  apply: (Aggregation_not_failed_no_fail H_st).
  move => H_in'.
  contradict H_in.
  exact: in_not_in_exclude.
move => n' H_ins.
apply H_or in H_ins.
case: H_ins => H_ins; last by right.
apply H_and in H_ins.
move: H_ins => [H_ins H_f'].
left.
apply: In_n_exclude; last exact: all_names_nodes.
apply H_ex_nd in H_ins.
case: H_ins => H_ins //.
by move: H_ins => [H_ins H_ins'].
Qed.

Lemma sum_fail_sent_incoming_active_empty_1 : 
  forall ns packets state,
  sum_fail_sent_incoming_active [] ns packets state = 1.
Proof.
elim => [|n ns IH] packets state //=.
rewrite IH.
by gsimpl.
Qed.

Lemma sum_fail_sent_incoming_active_all_head_eq : 
  forall ns ns' packets state n,
  sum_fail_sent_incoming_active (n :: ns) ns' packets state = 
  sum_fail_sent_incoming_active [n] ns' packets state * sum_fail_sent_incoming_active ns ns' packets state.
Proof.
move => ns ns'.
elim: ns' ns => /=.
  move => ns packets state.
  by gsimpl.
move => n ns IH ns' packets state n'.
rewrite IH.
gsimpl.
by aac_reflexivity.
Qed.

Lemma sum_fail_received_incoming_active_empty_1 : 
  forall ns packets state,
  sum_fail_received_incoming_active [] ns packets state = 1.
Proof.
elim => [|n ns IH] packets state //=.
rewrite IH.
by gsimpl.
Qed.

Lemma sum_fail_received_incoming_active_all_head_eq : 
  forall ns ns' packets state n,
  sum_fail_received_incoming_active (n :: ns) ns' packets state = 
  sum_fail_received_incoming_active [n] ns' packets state * sum_fail_received_incoming_active ns ns' packets state.
Proof.
move => ns ns'.
elim: ns' ns => /=.
  move => ns packets state.
  by gsimpl.
move => n ns IH ns' packets state n'.
rewrite IH.
gsimpl.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_all_head_eq :
  forall ns ns' packets n,  
  sum_aggregate_msg_incoming_active (n :: ns) ns' packets = 
  sum_aggregate_msg_incoming_active [n] ns' packets * sum_aggregate_msg_incoming_active ns ns' packets.
Proof.
move => ns ns'.
elim: ns' ns => /=.
  move => ns packets.
  by gsimpl.
move => n ns IH ns' packets n'.
rewrite IH.
gsimpl.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_active_singleton_neq_update2_eq :
  forall ns f h n n' ms,
    h <> n ->
    sum_aggregate_msg_incoming_active [n] ns f =
    sum_aggregate_msg_incoming_active [n] ns (update2 f h n' ms).
Proof.
elim => //=.
move => n0 ns IH f h n n' ms H_neq.
gsimpl.
case in_dec => /= H_dec; case in_dec => /= H_dec'.
- by rewrite -IH.
- case: H_dec'.
  rewrite /update2.
  by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
- contradict H_dec'.
  rewrite /update2.
  by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
- rewrite -IH //.
  rewrite /update2.
  by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_aggregate_msg_incoming_active_singleton_neq_collate_eq :
  forall ns f h n,
  h <> n ->
  sum_aggregate_msg_incoming_active [n] ns f =  
  sum_aggregate_msg_incoming_active [n] ns (collate h f (msg_for Fail (adjacent_to_node h ns))).
Proof.
elim => //=.
move => n' ns IH f h n H_neq.
gsimpl.
case in_dec => /= H_dec; case adjacent_to_dec => H_dec'.
- case in_dec => /= H_in.
    rewrite collate_neq // in H_in.
    rewrite -IH //.
    gsimpl.
    by rewrite -sum_aggregate_msg_incoming_active_singleton_neq_update2_eq.
  case: H_in.
  rewrite collate_neq //.
  rewrite /update2.
  by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
- case in_dec => /= H_dec''; first by rewrite -IH.
  case: H_dec''.
  by rewrite collate_neq.
- case in_dec => /= H_dec''.
    rewrite collate_neq // in H_dec''.
    contradict H_dec''.
    rewrite /update2.
    by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
  rewrite collate_neq //.
  rewrite -IH //.
  rewrite {2}/update2.
  case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
  by rewrite -sum_aggregate_msg_incoming_active_singleton_neq_update2_eq.
- case in_dec => /= H_dec''; first by contradict H_dec''; rewrite collate_neq.
  rewrite collate_neq //.
  by rewrite -IH.
Qed.

Lemma sum_fail_sent_incoming_active_singleton_neq_update2_eq :
  forall ns f g h n n' ms,
    h <> n ->
    sum_fail_sent_incoming_active [n] ns f g =
    sum_fail_sent_incoming_active [n] ns (update2 f h n' ms) g.
Proof.
elim => //=.
move => n0 ns IH f g h n n' ms H_neq.
gsimpl.
rewrite -IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_fail_sent_incoming_active_singleton_neq_collate_eq :
  forall ns f g h n,
  h <> n ->
  sum_fail_sent_incoming_active [n] ns f g = 
  sum_fail_sent_incoming_active [n] ns (collate h f (msg_for Fail (adjacent_to_node h ns))) g.
Proof.
elim => //=.
move => n' ns IH f g h n H_neq.
gsimpl.
case adjacent_to_dec => H_dec.
  rewrite -IH //.
  rewrite collate_neq //.
  by rewrite -sum_fail_sent_incoming_active_singleton_neq_update2_eq.
rewrite -IH //.
by rewrite collate_neq.
Qed.

Lemma sum_fail_received_incoming_active_singleton_neq_update2_eq :
  forall ns f g h n n' ms,
    h <> n ->
    sum_fail_received_incoming_active [n] ns f g =
    sum_fail_received_incoming_active [n] ns (update2 f h n' ms) g.
Proof.
elim => //=.
move => n0 ns IH f g h n n' ms H_neq.
gsimpl.
rewrite -IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_fail_received_incoming_active_singleton_neq_collate_eq :
  forall ns f g h n,
  h <> n ->
  sum_fail_received_incoming_active [n] ns f g =
  sum_fail_received_incoming_active [n] ns (collate h f (msg_for Fail (adjacent_to_node h ns))) g.
Proof.
elim => //=.
move => n' ns IH f g h n H_neq.
gsimpl.
case adjacent_to_dec => H_dec.
  rewrite -IH //.
  rewrite collate_neq //.
  by rewrite -sum_fail_received_incoming_active_singleton_neq_update2_eq.
rewrite -IH //.
by rewrite collate_neq.
Qed.

Lemma sum_fail_map_incoming_not_adjacent_collate_eq :
  forall ns ns' f h n adj map,
  ~ adjacent_to h n ->
  sum_fail_map_incoming ns (collate h f (msg_for Fail (adjacent_to_node h ns'))) n adj map =
  sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n' ns IH ns' f h n adj map H_adj.
rewrite IH //.
case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
rewrite -H_dec.
by rewrite (collate_msg_for_not_adjacent _ _ _ H_adj).
Qed.

Lemma sum_aggregate_msg_incoming_not_adjacent_collate_eq :
  forall ns ns' f h n,
  ~ adjacent_to h n ->
  sum_aggregate_msg_incoming ns (collate h f (msg_for Fail (adjacent_to_node h ns'))) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n' ns IH ns' f h n H_adj.
rewrite IH //.
case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
rewrite -H_dec.
by rewrite collate_msg_for_not_adjacent.
Qed.

Lemma sum_aggregate_msg_incoming_active_eq_not_in_eq :
forall ns ns' from to ms f,
  ~ In to ns ->
  sum_aggregate_msg_incoming_active ns' ns (update2 f from to ms) =
  sum_aggregate_msg_incoming_active ns' ns f.
Proof.
elim => //=.
move => n ns IH ns' from to ms f H_in.
have H_not_in: ~ In to ns by move => H_in'; case: H_in; right.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma collate_f_any_eq :
  forall  f g h n n' l,
  f n n' = g n n' ->
  collate h f l n n' = collate h g l n n'.
Proof.
move => f g h n n' l.
elim: l f g => //.
case => n0 m l IH f g H_eq.
rewrite /=.
set f' := update2 _ _ _ _.
set g' := update2 _ _ _ _.
rewrite (IH f' g') //.
rewrite /f' /g' {f' g'}.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq_h H_eq_n].
rewrite -H_eq_h -H_eq_n in H_eq.
by rewrite H_eq.
Qed.

Lemma sum_aggregate_msg_incoming_collate_update2_eq :
  forall ns h n n' f l ms,
  n' <> n ->
  sum_aggregate_msg_incoming ns (collate h (update2 f h n ms) l) n' =
  sum_aggregate_msg_incoming ns (collate h f l) n'.
Proof.
elim => //=.
move => n0 ns IH h n n' f l ms H_neq.
set f1 := update2 _ _ _ _.
have H_eq: f1 n0 n' = f n0 n'.
  rewrite /f1.
  rewrite /update2.
  by case sumbool_and => /= H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite (collate_f_any_eq _ _ _ _ _ _ H_eq) {H_eq}.
rewrite /f1 {f1}.
by case in_dec => /= H_dec; rewrite IH.
Qed.
  
Lemma sum_aggregate_msg_incoming_active_collate_update2_eq :
  forall ns ns' h n f l ms,
    ~ In n ns ->
    sum_aggregate_msg_incoming_active ns' ns (collate h (update2 f h n ms) l) =
    sum_aggregate_msg_incoming_active ns' ns (collate h f l).
Proof.
elim => //=.
move => n' ns IH ns' h n f l ms H_in.
have H_neq: n' <> n by move => H_in'; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_collate_update2_eq.
Qed.

Lemma in_collate_in :
  forall ns n h f mg,
  ~ In n ns ->
  In mg ((collate h f (msg_for mg (adjacent_to_node h ns))) h n) ->
  In mg (f h n).
Proof.
elim => //=.
move => n' ns IH n h f mg H_in.
have H_neq: n' <> n by move => H_eq; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
case adjacent_to_dec => H_dec; last exact: IH.
rewrite /=.
set up2 := update2 _ _ _ _.
have H_eq_f: up2 h n = f h n.
  rewrite /up2 /update2.
  by case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
rewrite (collate_f_any_eq _ _ _ _ _ _ H_eq_f).
exact: IH.
Qed.

Lemma collate_in_in :
  forall l h n n' f mg,
    In mg (f n' n) ->
    In mg ((collate h f l) n' n).
Proof.
elim => //=.
case => n0 mg' l IH h n n' f mg H_in.
apply IH.
rewrite /update2.
case sumbool_and => H_dec //.
move: H_dec => [H_eq H_eq'].
apply in_or_app.
left.
by rewrite H_eq H_eq'.
Qed.

Lemma sum_aggregate_msg_collate_fail_eq :
  forall l f h n n',
    sum_aggregate_msg (collate h f (msg_for Fail l) n' n) =
    sum_aggregate_msg (f n' n).
Proof.
elim => //=.
move => n0 l IH f h n n'.
rewrite IH.
rewrite /update2.
case sumbool_and => H_and //.
move: H_and => [H_eq H_eq'].
rewrite H_eq H_eq' sum_aggregate_msg_split /=.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_collate_msg_for_notin_eq :
  forall ns ns' h n f,
  ~ In n ns' ->
  sum_aggregate_msg_incoming ns (collate h f (msg_for Fail (adjacent_to_node h ns'))) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n' ns IH ns' h n f H_in.
case in_dec => /= H_dec; case in_dec => /= H_dec'.
- by rewrite IH.
- case (name_eq_dec h n') => H_eq; last by rewrite collate_neq in H_dec.
  case: H_dec'.
  rewrite -H_eq.
  rewrite -H_eq {H_eq} in H_dec.
  by apply in_collate_in in H_dec.
- case: H_dec.
  exact: collate_in_in.
- rewrite IH //.
  by rewrite sum_aggregate_msg_collate_fail_eq.
Qed.
  
Lemma sum_aggregate_msg_incoming_collate_update2_notin_eq :
  forall ns h n f n' l ms,
    ~ In h ns ->
    sum_aggregate_msg_incoming ns (collate h (update2 f h n' ms) l) n =
    sum_aggregate_msg_incoming ns (collate h f l) n.
Proof.
elim => //=.
move => n0 ns IH h n f n' l ms H_in.
have H_neq: h <> n0 by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
case in_dec => /= H_dec; case in_dec => /= H_dec'.
- by rewrite IH.
- rewrite IH //.
  rewrite collate_neq // in H_dec.
  case: H_dec'.
  move: H_dec.
  rewrite /update2.
  case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  exact: collate_in_in.
- case: H_dec.
  set up2 := update2 _ _ _ _.
  have H_eq_f: up2 n0 n = f n0 n by rewrite /up2 /update2; case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  by rewrite (collate_f_any_eq _ _ _ _ _ _ H_eq_f).
- rewrite IH //.
  set up2 := update2 _ _ _ _.
  have H_eq_f: up2 n0 n = f n0 n by rewrite /up2 /update2; case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  by rewrite (collate_f_any_eq _ _ _ _ _ _ H_eq_f).
Qed.

Lemma sum_fail_map_incoming_collate_update2_eq :
  forall ns h n n' f l ms adj map,
  n' <> n ->
  sum_fail_map_incoming ns (collate h (update2 f h n ms) l) n' adj map =
  sum_fail_map_incoming ns (collate h f l) n' adj map.
Proof.
elim => //=.
move => n0 ns IH h n n' f l ms adj map H_neq.
set f1 := update2 _ _ _ _.
have H_eq: f1 n0 n' = f n0 n'.
  rewrite /f1.
  rewrite /update2.
  by case sumbool_and => /= H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite (collate_f_any_eq _ _ _ _ _ _ H_eq) {H_eq}.
rewrite /f1 {f1}.
by rewrite IH.
Qed.

Lemma sum_fail_sent_incoming_active_collate_update2_eq :
  forall ns ns' h n f g l ms,
  ~ In n ns ->
  sum_fail_sent_incoming_active ns' ns (collate h (update2 f h n ms) l) g =
  sum_fail_sent_incoming_active ns' ns (collate h f l) g.
Proof.
elim => //=.
move => n' ns IH ns' h n f g l ms H_in.
have H_neq: n' <> n by move => H_in'; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
rewrite IH //.
by rewrite sum_fail_map_incoming_collate_update2_eq.
Qed.

Lemma sum_fail_received_incoming_active_collate_update2_eq :
  forall ns ns' h n f g l ms,
  ~ In n ns ->
  sum_fail_received_incoming_active ns' ns (collate h (update2 f h n ms) l) g =
  sum_fail_received_incoming_active ns' ns (collate h f l) g.
Proof.
elim => //=.
move => n' ns IH ns' h n f g l ms H_in.
have H_neq: n' <> n by move => H_in'; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
rewrite IH //.
by rewrite sum_fail_map_incoming_collate_update2_eq.
Qed.

Lemma sum_fail_map_incoming_update2_not_eq_alt :
  forall ns f from to ms n adj map,
      to <> n ->
      sum_fail_map_incoming ns (update2 f from to ms) n adj map =
      sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n' ns IH f from to ms n adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt_alt :
  forall ns0 ns1 from to ms f g,
  ~ In to ns0 ->
  sum_fail_sent_incoming_active ns1 ns0 (update2 f from to ms) g =
  sum_fail_sent_incoming_active ns1 ns0 f g.
Proof.
elim => //.
move => n ns IH ns1 from to ms f g H_in.
have H_neq: to <> n by move => H_eq; case: H_in; left.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
rewrite /= IH //.
by rewrite sum_fail_map_incoming_update2_not_eq_alt.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt_alt :
  forall ns0 ns1 from to ms f g,
  ~ In to ns0 ->
  sum_fail_received_incoming_active ns1 ns0 (update2 f from to ms) g =
  sum_fail_received_incoming_active ns1 ns0 f g.
Proof.
elim => //.
move => n ns IH ns1 from to ms f g H_in.
have H_neq: to <> n by move => H_eq; case: H_in; left.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
rewrite /= IH //.
by rewrite sum_fail_map_incoming_update2_not_eq_alt.
Qed.

Lemma Aggregation_sent_received_eq : 
  forall net failed tr,
    step_o_f_star step_o_f_init (failed, net) tr ->
    forall n n' m0 m1,
     ~ In n failed ->
     ~ In n' failed ->
    NSet.In n' (net.(onwState) n).(adjacent) ->
    NSet.In n (net.(onwState) n').(adjacent) ->
    NMap.find n (net.(onwState) n').(sent) = Some m0 ->
    NMap.find n' (net.(onwState) n).(received) = Some m1 ->
    m0 = sum_aggregate_msg (net.(onwPackets) n' n) * m1.
Proof.
move => onet failed tr H_st.
have H_eq_f: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {3 4 5 6 7}H_eq_o {H_eq_o}.
remember step_o_f_init as y in *.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => /= H_init.
  rewrite H_init /= {H_init}.
  move => n n' m0 m1 H_in H_in'.
  rewrite /init_map /=.
  case init_map_str => map H_init_map.
  case init_map_str => map' H_init_map'.
  move => H_ins H_ins' H_find H_find'.
  apply H_init_map in H_ins'.
  apply H_init_map' in H_ins.
  rewrite H_ins in H_find'.
  rewrite H_ins' in H_find.
  inversion H_find'.
  inversion H_find.
  by gsimpl.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- move {H_st2}.
  rewrite /= in IHH_st1.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => /=.
  * move: H4 H5 H6 H7 H.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H11 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H3.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H11 H13 H_dec.
      rewrite /update2.
      case sumbool_and => H_and; last first.
        case: H_and => H_and //.
        move => H_ins H_ins' H_find H_find' H_find''.
        rewrite NMapFacts.add_neq_o // in H_find'.
        exact: IHH_st1.
      move: H_and => [H_eq H_eq'].
      rewrite -H_eq.
      rewrite H_dec in H2.
      rewrite -H_eq in H3.
      move => H_ins H_ins' H_find H_find' H_find''.
      have IH := IHH_st1 _ _ _ _ H2 H3 H_ins H_ins' H_find H_find''.
      rewrite H0 /= in IH.
      rewrite IH.
      rewrite NMapFacts.add_eq_o // in H_find'.
      inversion H_find'.
      gsimpl.
      by aac_reflexivity.            
    + rewrite H11 H12 H_dec'.
      rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_dec.
      move => H_ins H_ins' H_find H_find' H_find''.
      exact: IHH_st1.
    + rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_dec.
      move => H_ins H_ins' H_find H_find' H_find''.
      exact: IHH_st1.    
  * have H_agg := Aggregation_aggregate_msg_dst_adjacent_src H_st1 _ H1 from x.
    rewrite H0 in H_agg.
    suff H_suff: NSet.In from (adjacent (onwState net to)).
      have [m' H_ex] := Aggregation_in_set_exists_find_received H_st1 _ H1 H_suff.
      by rewrite H_ex in H2.
    apply: H_agg.
    by left.
  * move: H4 H5 H6 H7.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H12 -H_dec'.
      move => H_ins.
      apply NSetFacts.remove_3 in H_ins.
      contradict H_ins.
      move: H_st1 H3.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H12 H14 H_dec.
      rewrite /update2.
      case sumbool_and => H_and; last first.
        case: H_and => H_and //.
        move => H_ins H_ins' H_find H_find'.
        apply NSetFacts.remove_3 in H_ins.
        rewrite NMapFacts.remove_neq_o // in H_find'.
        exact: IHH_st1.
      move: H_and => [H_eq H_eq'].
      rewrite H_eq in H0.
      have H_in_f: In Fail (onwPackets net n' to) by rewrite H0; left.
      contradict H_in_f.
      exact: (Aggregation_not_failed_no_fail H_st1).
    + rewrite H12 H13 H_dec'.
      move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_dec.
      rewrite -H_dec' in H0.
      have H_neq': from <> n.
        move => H_eq.
        rewrite H_eq in H0 H2.
        have H_in_f: In Fail (onwPackets net n n') by rewrite H0; left.
        contradict H_in_f.
        exact: (Aggregation_not_failed_no_fail H_st1).
      apply NSetFacts.remove_3 in H_ins'.
      rewrite NMapFacts.remove_neq_o // in H_find.
      exact: IHH_st1.
    + rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_dec.
      exact: IHH_st1.
  * have H_f := Aggregation_in_queue_fail_then_adjacent H_st1 to from H1.
    rewrite H0 in H_f.
    suff H_suff: NSet.In from (adjacent (onwState net to)).
      have [m' H_ex] := Aggregation_in_set_exists_find_sent H_st1 _ H1 H_suff.
      by rewrite H_ex in H9.
    apply: H_f.
    by left.
  * have H_f := Aggregation_in_queue_fail_then_adjacent H_st1 to from H1.
    rewrite H0 in H_f.
    suff H_suff: NSet.In from (adjacent (onwState net to)).
      have [m' H_ex] := Aggregation_in_set_exists_find_received H_st1 _ H1 H_suff.
      by rewrite H_ex in H9.
    apply: H_f.
    by left.
- move {H_st2}.
  rewrite /= in IHH_st1.
  find_apply_lem_hyp input_handlers_IOHandler.
  io_handler_cases.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H9 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H9 H11 -H_dec.
      exact: IHH_st1.
    + rewrite H9 H10 -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H12 -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite H12 H14 H_dec.
      move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq in H_dec'.
      exact: IHH_st1.
      rewrite H12 H13 -H_dec'.
      move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; last first.
        case: H_and => H_and //.
        apply NMapFacts.find_mapsto_iff in H_find.
        apply NMapFacts.add_neq_mapsto_iff in H_find => //.
        apply NMapFacts.find_mapsto_iff in H_find.
        exact: IHH_st1.
      move: H_and => [H_eq H_eq'].
      rewrite H_eq'.
      rewrite H_eq' -H_dec' in H9 H_find.
      have IH := IHH_st1 _ _ _ _ H H2 H_ins H_ins' H9 H_find'.
      rewrite IH in H_find.
      rewrite sum_aggregate_msg_split /=.
      rewrite NMapFacts.add_eq_o // in H_find.
      inversion H_find.
      gsimpl.
      by aac_reflexivity.
    + move => H_ins H_ins' H_find H_find'.
      rewrite /update2.
      case sumbool_and => H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq in H_dec'.
      exact: IHH_st1.
  * have [m' H_ex] := Aggregation_in_set_exists_find_sent H_st1 _ H0 H.
    by rewrite H_ex in H9.
  * rewrite /=.
    move: H3 H4 H5 H6.
    rewrite /update.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H0.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * move: H3 H4 H5 H6.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H2.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
  * move: H6 H7 H8 H9.
    rewrite /update /=.
    case name_eq_dec => H_dec; case name_eq_dec => H_dec'.
    + rewrite -H_dec'.
      move => H_ins.
      contradict H_ins.
      move: H_st1 H5.
      exact: Aggregation_node_not_adjacent_self.
    + rewrite -H_dec.
      exact: IHH_st1.
    + rewrite -H_dec'.
      exact: IHH_st1.
    + exact: IHH_st1.
- move {H_st2}.
  rewrite /= in IHH_st1.
  move => n n' m0 m1 H_f H_f' H_ins H_ins' H_find H_find'.
  rewrite sum_aggregate_msg_collate_fail_eq.
  have H_in: ~ In n failed0 by move => H_in; case: H_f; right.
  have H_in': ~ In n' failed0 by move => H_in'; case: H_f'; right.
  exact: IHH_st1.
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall onet failed tr,
  step_o_f_star step_o_f_init (failed, onet) tr ->
  conserves_network_mass (exclude failed nodes) nodes onet.(onwPackets) onet.(onwState).
Proof.
move => onet failed tr H_step.
rewrite /conserves_network_mass.
have H_cons := Aggregation_conserves_node_mass_all H_step.
apply global_conservation in H_cons.
rewrite /conserves_mass_globally in H_cons.
rewrite H_cons {H_cons}.
suff H_suff: @sum_sent _ AggregationData_Data (Nodes_data (exclude failed nodes) onet.(onwState)) * (@sum_received _ AggregationData_Data (Nodes_data (exclude failed nodes) onet.(onwState)))^-1 =
             sum_aggregate_msg_incoming_active nodes (exclude failed nodes) onet.(onwPackets) *
             sum_fail_sent_incoming_active nodes (exclude failed nodes) onet.(onwPackets) onet.(onwState) *
             (sum_fail_received_incoming_active nodes (exclude failed nodes) onet.(onwPackets) onet.(onwState))^-1 by aac_rewrite H_suff; aac_reflexivity.
remember step_o_f_init as y in *.
have ->: failed = fst (failed, onet) by [].
have H_eq_o: onet = snd (failed, onet) by [].
rewrite {2 4 6 8 9 11 12} H_eq_o {H_eq_o}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init {H_init} /=.
  rewrite sum_aggregate_msg_incoming_all_step_o_init.
  rewrite sum_sent_step_o_init.
  rewrite sum_received_step_o_init.
  rewrite sum_fail_sent_incoming_active_step_o_init.
  rewrite sum_fail_received_incoming_active_step_o_init.
  by gsimpl.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  move {H_step2}.
  have H_in_from : In from nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In to (exclude failed0 nodes).
    have H_inn := all_names_nodes to.
    exact: In_n_exclude _ _ _ H1 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := nodup_exclude failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_to_nin: ~ In to ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In to ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2 5}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq //.
  rewrite Nodes_data_not_in_eq //.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.  
  gsimpl.
  move => IH.  
  net_handler_cases => //=.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    rewrite sumM_add_map //.
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H5 H6 H7 {H3 H4 H5 H6 H7}.
    case (In_dec Msg_eq_dec Fail (net.(onwPackets) from to)) => H_in_fail.
      rewrite (sum_aggregate_msg_incoming_update2_fail_eq _ _ _ _ no_dup_nodes _ H0) //.
      rewrite (sum_aggregate_msg_incoming_update2_aggregate_in_fail_add _ _ _ H_ins _ no_dup_nodes _ H0) //.
      rewrite (sum_aggregate_msg_incoming_update2_aggregate_in_fail _ _ _ _ _ _ no_dup_nodes H0) //.    
      gsimpl.
      by aac_reflexivity.
    rewrite (sum_aggregate_msg_incoming_update2_aggregate _ _ _ H_in_from no_dup_nodes H_in_fail H0).
    rewrite (no_fail_sum_fail_map_incoming_eq _ _ _ _ _ (all_names_nodes from) no_dup_nodes H0 H_in_fail).
    rewrite (no_fail_sum_fail_map_incoming_add_eq _ _ _ _ _ _ (all_names_nodes from) no_dup_nodes H0 H_in_fail).
    by aac_reflexivity.
  * have H_in: In (Aggregate x) (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ H1 _ _ H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H_step1 _ H1 H_ins.
    by rewrite H_rcd in H.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_in': ~ In Fail ms.
      have H_le := Aggregation_le_one_fail H_step1 _ from H1.
      rewrite H0 /= in H_le.
      move: H_le.
      case H_cnt: (count_occ _ _ _) => H_le; last by omega.
      by apply count_occ_not_In in H_cnt.      
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    rewrite (sumM_remove_remove H_ins H).
    rewrite (sumM_remove_remove H_ins H3).
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_sent_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin).
    rewrite (sum_fail_received_incoming_active_not_in_eq _ _ _ _ _ _ _ _ H_to_nin').
    have H_bef := Aggregation_in_after_all_fail_aggregate H_step1 _ H1 from.
    rewrite (sum_aggregate_msg_incoming_fail_update2_eq _ _ _ H_bef _ no_dup_nodes) //.
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H6 H7 H8.
    rewrite (sum_fail_map_incoming_fail_remove_eq _ _ _ no_dup_nodes H_ins _ H_in' H) //.
    rewrite (sum_fail_map_incoming_fail_remove_eq _ _ _ no_dup_nodes H_ins _ H_in' H3) //.
    gsimpl.
    by aac_reflexivity.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    have [m5 H_snt] := Aggregation_in_set_exists_find_sent H_step1 _ H1 H_ins.
    by rewrite H_snt in H9.
  * have H_in: In Fail (onwPackets net from to) by rewrite H0; left.
    have H_ins := Aggregation_in_queue_fail_then_adjacent H_step1 _ _ H1 H_in.
    have [m5 H_rcd] := Aggregation_in_set_exists_find_received H_step1 _ H1 H_ins.
    by rewrite H_rcd in H9.
- find_apply_lem_hyp input_handlers_IOHandler.
  move {H_step2}.
  have H_in_from : In h nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (exclude failed0 nodes).
    have H_inn := all_names_nodes h.
    exact: In_n_exclude _ _ _ H0 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].  
  have H_nd := nodup_exclude failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_h_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_h_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  rewrite H_inn.
  rewrite 2!Nodes_data_split /=.
  rewrite {2 5}/update.
  case (name_eq_dec _ _) => H_dec {H_dec} //.
  rewrite Nodes_data_not_in_eq //.
  rewrite Nodes_data_not_in_eq //.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.
  gsimpl.
  move => IH.
  io_handler_cases => //=.
  * rewrite sum_fail_sent_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_sent_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_received_incoming_active_not_in_eq_alt //.
    rewrite sum_fail_received_incoming_active_not_in_eq_alt //.
    rewrite /update.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    by rewrite H3 H4 H5.
  * have H_x_Nodes: In x nodes by exact: all_names_nodes.
    have H_neq: h <> x by move => H_eq; have H_self := Aggregation_node_not_adjacent_self H_step1 H0; rewrite {1}H_eq in H_self.
    rewrite (sumM_add_map _ H H3).
    gsimpl.
    aac_rewrite IH.
    move {IH}.
    rewrite sum_aggregate_msg_incoming_neq_eq //.
    rewrite {5 6 7 8}/update /=.
    case (name_eq_dec _ _) => H_dec {H_dec} //.
    rewrite H6 H8.
    case (In_dec name_eq_dec x failed0) => H_dec.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H0 H.
      case: H_or => H_or //.
      move: H_or => [H_dec' H_in] {H_dec'}.
      have H_x_ex: ~ In x (exclude failed0 nodes) by exact: in_not_in_exclude.
      rewrite H_inn in H_x_ex.
      have H_x_nin: ~ In x ns0 by move => H_x_in; case: H_x_ex; apply in_or_app; left.
      have H_x_nin': ~ In x ns1 by move => H_x_in; case: H_x_ex; apply in_or_app; right; right.
      rewrite sum_fail_sent_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_sent_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_received_incoming_active_not_in_eq_alt2 //.
      rewrite sum_fail_received_incoming_active_not_in_eq_alt2 //.
      rewrite /update /=.
      case name_eq_dec => H_eq //.
      rewrite H6 H7.
      rewrite (sum_fail_map_incoming_add_aggregate_eq _ _ _ _ no_dup_nodes) //.
      rewrite sum_fail_map_incoming_update2_not_eq //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
      by aac_reflexivity.
    have H_in := Aggregation_not_failed_no_fail H_step1 _ x H0.
    have H_in' := Aggregation_not_failed_no_fail H_step1 _ h H_dec.
    rewrite sum_fail_sent_incoming_active_update_not_in_eq //.
    rewrite sum_fail_sent_incoming_active_update_not_in_eq //.   
    rewrite sum_fail_received_incoming_active_update_not_in_eq //.
    rewrite sum_fail_received_incoming_active_update_not_in_eq //.
    rewrite sum_fail_sent_incoming_active_update2_app_eq //.
    rewrite sum_fail_sent_incoming_active_update2_app_eq //.
    rewrite sum_fail_received_incoming_active_update2_app_eq //.
    rewrite sum_fail_received_incoming_active_update2_app_eq //.
    rewrite /update /=.
    case name_eq_dec => H_eq //.
    rewrite H6 H7.
    rewrite (sum_fail_map_incoming_not_in_fail_add_update2_eq _ _ _ _ _ _ _ no_dup_nodes) //.    
    rewrite (sum_fail_map_incoming_not_in_fail_update2_eq _ _ _ _ _ H_neq).
    have H_in_x: In x (exclude failed0 nodes) by exact: In_n_exclude.
    rewrite H_inn in H_in_x.
    apply in_app_or in H_in_x.
    case: H_in_x => H_in_x.
      have H_nin_x: ~ In x ns1.
        move => H_nin_x.
        apply NoDup_remove_1 in H_nd.
        contradict H_nin_x.
        move: H_in_x.
        exact: nodup_in_not_in_right.
      have H_nd': NoDup ns0 by move: H_nd; exact: nodup_app_split_left.
      rewrite (sum_aggregate_msg_incoming_active_not_in_eq ns1) //.
      rewrite (sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ no_dup_nodes) //.
      by aac_reflexivity.
    case: H_in_x => H_in_x //.
    have H_nin_x: ~ In x ns0.
      move => H_nin_x.
      apply NoDup_remove_1 in H_nd.
      contradict H_nin_x.
      move: H_in_x.
      exact: nodup_in_not_in_left.
    have H_nd': NoDup ns1.
      apply nodup_app_split_right in H_nd.
      by inversion H_nd.
    rewrite sum_aggregate_msg_incoming_active_not_in_eq //.
    rewrite (sum_aggregate_msg_incoming_active_in_update2_app_eq _ _ _ _ _ no_dup_nodes) //.
    by aac_reflexivity.
  * have [m' H_snt] := Aggregation_in_set_exists_find_sent H_step1 _ H0 H.
    by rewrite H_snt in H3.
  * rewrite update_nop.
    by rewrite update_nop_ext.
  * rewrite update_nop.
    by rewrite update_nop_ext.
  * rewrite update_nop.
    by rewrite update_nop_ext.
- move {H_step2}.
  have H_in_from : In h nodes by exact: all_names_nodes.
  rewrite /= in IHH_step1.
  have H_inn : In h (exclude failed0 nodes).
    have H_inn := all_names_nodes h.
    exact: In_n_exclude _ _ _ H0 H_inn.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  have H_nd := nodup_exclude failed0 no_dup_nodes.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  have H_to_nin: ~ In h ns0 by move => H_in; case: H_nin; apply in_or_app; left.
  have H_to_nin': ~ In h ns1 by move => H_in; case: H_nin; apply in_or_app; right.
  move: IHH_step1.
  have H_ex := exclude_in_app ns0 ns1 h failed0 no_dup_nodes H_inn.
  rewrite (exclude_in_app ns0 ns1 _ _ no_dup_nodes) //.
  rewrite H_inn.
  have H_nd': NoDup ns0 by move: H_nd; exact: nodup_app_split_left.
  have H_nd'': NoDup ns1 by apply nodup_app_split_right in H_nd; inversion H_nd.
  rewrite 2!Nodes_data_split /=.  
  rewrite 2!sum_sent_distr 2!sum_received_distr /=.
  rewrite 2!sum_aggregate_msg_incoming_active_split /=.
  rewrite 2!sum_fail_sent_incoming_active_split /=.
  rewrite 2!sum_fail_received_incoming_active_split /=.
  gsimpl.
  move => IH.
  rewrite /Net.adjacent_to_node -/(adjacent_to_node _ _).
  rewrite adjacent_to_node_self_eq.
  set l := collate _ _ _.
  have H_eq: sum_sent (Nodes_data ns0 (onwState net)) * 
   sum_sent (Nodes_data ns1 (onwState net)) *
   sumM (adjacent (onwState net h)) (sent (onwState net h)) *
   (sumM (adjacent (onwState net h)) (received (onwState net h)))^-1 *
   (sum_received (Nodes_data ns1 (onwState net)))^-1 *
   (sum_received (Nodes_data ns0 (onwState net)))^-1 =
   (sum_received (Nodes_data (ns0 ++ ns1) (onwState net)))^-1 *
   sum_sent (Nodes_data (ns0 ++ ns1) (onwState net)) *    
   sumM (adjacent (onwState net h)) (sent (onwState net h)) *
   (sumM (adjacent (onwState net h)) (received (onwState net h)))^-1.
    rewrite sum_sent_Nodes_data_distr.
    aac_rewrite (sum_received_Nodes_data_distr ns0 ns1 (onwState net)).
    gsimpl.
    set sr := sum_received _.
    set ss := sum_sent _.
    by aac_reflexivity.
  rewrite H_eq {H_eq} in IH.
  rewrite sum_sent_Nodes_data_distr.  
  aac_rewrite (sum_received_Nodes_data_distr ns0 ns1 (onwState net)).
  move: IH.
  rewrite -2!sum_aggregate_msg_incoming_active_split.
  move => IH.
  have ->: sum_aggregate_msg_incoming_active nodes (ns0 ++ ns1) l *
   sum_fail_sent_incoming_active nodes ns0 l (onwState net) *
   sum_fail_sent_incoming_active nodes ns1 l (onwState net) *
   (sum_fail_received_incoming_active nodes ns1 l (onwState net))^-1 *
   (sum_fail_received_incoming_active nodes ns0 l (onwState net))^-1 =
   sum_aggregate_msg_incoming_active nodes (ns0 ++ ns1) l *
   sum_fail_sent_incoming_active nodes (ns0 ++ ns1) l (onwState net) *
   (sum_fail_received_incoming_active nodes (ns0 ++ ns1) l (onwState net))^-1.
    rewrite sum_fail_sent_incoming_active_split.
    rewrite sum_fail_received_incoming_active_split.
    by gsimpl.
  move: IH.
  have ->: sum_aggregate_msg_incoming_active nodes (ns0 ++ ns1) (onwPackets net) *
   sum_aggregate_msg_incoming nodes (onwPackets net) h *
   sum_fail_sent_incoming_active nodes ns0 (onwPackets net) (onwState net) *
   sum_fail_sent_incoming_active nodes ns1 (onwPackets net) (onwState net) *
   sum_fail_map_incoming nodes (onwPackets net) h
     (adjacent (onwState net h)) (sent (onwState net h)) *
   (sum_fail_map_incoming nodes (onwPackets net) h
      (adjacent (onwState net h)) (received (onwState net h)))^-1 *
   (sum_fail_received_incoming_active nodes ns1 (onwPackets net) (onwState net))^-1 *
   (sum_fail_received_incoming_active nodes ns0 (onwPackets net) (onwState net))^-1 =
   sum_aggregate_msg_incoming_active nodes (ns0 ++ ns1) (onwPackets net) *
   sum_aggregate_msg_incoming nodes (onwPackets net) h *
   sum_fail_sent_incoming_active nodes (ns0 ++ ns1) (onwPackets net) (onwState net) *
   sum_fail_map_incoming nodes (onwPackets net) h (adjacent (onwState net h)) (sent (onwState net h)) *
   (sum_fail_received_incoming_active nodes (ns0 ++ ns1) (onwPackets net) (onwState net))^-1 *
   (sum_fail_map_incoming nodes (onwPackets net) h (adjacent (onwState net h)) (received (onwState net h)))^-1.
    rewrite sum_fail_sent_incoming_active_split.
    rewrite sum_fail_received_incoming_active_split.
    gsimpl.
    by aac_reflexivity.
  set sums := sumM _ _.
  set sumr := sumM _ _.
  set sr := sum_received _.
  set ss := sum_sent _.
  move => IH.
  set sam := sum_aggregate_msg_incoming_active _ _ _.  
  set sfsi := sum_fail_sent_incoming_active _ _ _ _.
  set sfri := sum_fail_received_incoming_active _ _ _ _.
  suff H_suff: sr^-1 * ss * sums * sums^-1 * sumr^-1 * sumr =
               sam * sfsi * sfri^-1.
    move: H_suff.
    by gsimpl.
  aac_rewrite IH.
  move {IH}.
  rewrite /sums /sumr /sr /ss /sam /sfsi /sfri {sums sumr sr ss sam sfsi sfri}.
  rewrite /l {l}.
  have H_acs := sumM_sent_fail_active_eq_with_self H_step1 _ H0.
  have H_acr := sumM_received_fail_active_eq_with_self H_step1 _ H0.
  have H_pmn: Permutation (h :: ns0 ++ ns1) (exclude failed0 nodes) by rewrite H_inn; exact: Permutation_middle.
  rewrite -(sumM_active_eq_sym _ _ H_pmn) /= /sum_active_fold in H_acs.
  rewrite -(sumM_active_eq_sym _ _ H_pmn) /= /sum_active_fold in H_acr.
  move: H_acs H_acr {H_pmn}.
  case: ifP => H_mem; first by apply NSetFacts.mem_2 in H_mem; contradict H_mem; exact: (Aggregation_node_not_adjacent_self H_step1).
  set s1 := sum_fail_map_incoming _ _ _ _ _.
  set s2 := sum_fail_map_incoming _ _ _ _ _.
  move => H_acs H_acr {H_mem}.  
  aac_rewrite H_acr.  
  move {H_acr}.
  rewrite /s2 {s2}.
  have H_acs': 
    (sumM (adjacent (onwState net h)) (sent (onwState net h)))^-1 * s1 =
    (sumM_active (adjacent (onwState net h)) (sent (onwState net h)) (ns0 ++ ns1))^-1.
    rewrite -H_acs.
    gsimpl.
    by aac_reflexivity.
  aac_rewrite H_acs'.
  move {H_acs H_acs' s1}.
  apply NoDup_remove_1 in H_nd.
  move: H_nd H_nin H_ex.
  set ns := ns0 ++ ns1.
  move => H_nd H_nin H_ex.
  move {H_to_nin H_to_nin' H_nd' H_nd'' H_inn}.
  move {H_nin H_nd}.
  have H_nd := no_dup_nodes.
  move: ns H_ex => ns H_ex {ns0 ns1}.
  apply in_split in H_in_from.
  move: H_in_from => [ns0 [ns1 H_in_from]].
  rewrite H_in_from in H_ex.
  rewrite H_in_from in H_nd.
  have H_nin: ~ In h (ns0 ++ ns1) by exact: nodup_notin.
  apply NoDup_remove_1 in H_nd.
  apply exclude_in_split_eq in H_ex.
  move: H_ex.
  rewrite /=.
  case name_eq_dec => H_dec {H_dec} //.
  move => H_ex.
  have H_pm: Permutation nodes (h :: ns0 ++ ns1).
    rewrite H_in_from.
    apply Permutation_sym.
    exact: Permutation_middle.  
  move {H_in_from}.
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_permutation_eq _ _ H_pm).
  rewrite (sum_fail_sent_incoming_active_permutation_eq _ _ _ H_pm).
  rewrite (sum_fail_received_incoming_active_permutation_eq _ _ _ H_pm).
  rewrite (sum_aggregate_msg_incoming_active_permutation_eq _ _ H_pm).
  rewrite (sum_fail_sent_incoming_active_permutation_eq _ _ _ H_pm).
  rewrite (sum_fail_received_incoming_active_permutation_eq _ _ _ H_pm).
  move: H_nd H_nin ns H_ex {H_pm}.
  set ns' := ns0 ++ ns1.
  elim: ns' => /=; rewrite (Aggregation_self_channel_empty H_step1) //=; first by move => H_nd H_in ns H_eq; rewrite -H_eq /=; gsimpl.
  move => n ns' IH H_nd H_in ns.
  inversion H_nd => {x H l H1}.
  have H_neq: h <> n by move => H_eq; case: H_in; left.
  have H_in': ~ In h ns' by move => H_in'; case: H_in; right.
  move {H_in H_nd}.
  case name_eq_dec => H_dec //=.
  case (in_dec _ _ _) => H_dec'.
    move {H_dec}.
    move => H_ex.
    have IH' := IH H3 H_in' _ H_ex.
    move {IH}.
    move: IH'.
    gsimpl.
    move => IH.
    case in_dec => /= H_dec; case H_mem: (NSet.mem n (net.(onwState) h).(adjacent)).
    - apply NSetFacts.mem_2 in H_mem.
      gsimpl.
      rewrite sum_fail_received_incoming_active_all_head_eq.
      rewrite sum_fail_received_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_received_incoming_active_all_head_eq ns').
      rewrite (sum_fail_received_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_received_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_received_incoming_active_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite sum_fail_sent_incoming_active_all_head_eq.
      rewrite sum_fail_sent_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_sent_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
      move: IH.
      gsimpl.
      move => IH.
      aac_rewrite IH.
      move {IH}.
      gsimpl.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
      rewrite -(sum_fail_sent_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      rewrite -(sum_fail_received_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      by aac_reflexivity.
    - move/negP: H_mem => H_mem.
      case: H_mem.
      apply NSetFacts.mem_1.
      exact: (Aggregation_in_queue_fail_then_adjacent H_step1).
    - apply NSetFacts.mem_2 in H_mem.
      have H_or := Aggregation_in_adj_or_incoming_fail H_step1 _ H0 H_mem.
      case: H_or => H_or //.
      by move: H_or => [H_or H_f].
    - move/negP: H_mem => H_mem.
      have H_notin: forall m', ~ In (Aggregate m') (onwPackets net n h).
        move => m' H_in.
        case: H_mem.
        apply NSetFacts.mem_1.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1 _ _ _ m').
      rewrite (sum_aggregate_ms_no_aggregate_1 _ H_notin).
      gsimpl.
      rewrite sum_fail_received_incoming_active_all_head_eq.
      rewrite sum_fail_received_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_received_incoming_active_all_head_eq ns').
      rewrite (sum_fail_received_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_received_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_received_incoming_active_all_head_eq ns').
      rewrite sum_aggregate_msg_incoming_active_all_head_eq.
      rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
      rewrite sum_fail_sent_incoming_active_all_head_eq.
      rewrite sum_fail_sent_incoming_active_all_head_eq in IH.
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns') in IH.
      rewrite (sum_fail_sent_incoming_active_all_head_eq (n :: ns')).
      rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
      move: IH.
      gsimpl.
      move => IH.
      aac_rewrite IH.
      move {IH}.
      gsimpl.
      rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
      rewrite -(sum_fail_sent_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      rewrite -(sum_fail_received_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
      by aac_reflexivity.
  move {H_dec}.
  case: ns IH H2 H3 H_in' => //.
  move => n' ns IH H_in H_nd H_nin H_ex.
  have H_ex': exclude (h :: failed0) ns' = ns by inversion H_ex.
  have H_eq: n = n' by inversion H_ex.
  rewrite -H_eq {n' H_eq H_ex}.
  have IH' := IH H_nd H_nin _ H_ex'.
  move {IH}.
  rewrite /=.
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  rewrite {1 3}/sum_fail_map /=.
  rewrite /sum_active_fold.
  gsimpl.
  case (adjacent_to_dec _ _) => H_Adj; last first.
    rewrite /=.
    gsimpl.
    have H_Adj': ~ adjacent_to n h by move => H_Adj'; apply adjacent_to_symmetric in H_Adj'.
    case: ifP => H_dec.
      apply NSetFacts.mem_2 in H_dec.
      case: H_Adj'.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; exact: (Aggregation_not_failed_no_fail H_step1).
    move {H_dec}.
    case in_dec => /= H_dec; first by contradict H_dec; rewrite collate_neq // (Aggregation_self_channel_empty H_step1).
    move {H_dec}.
    have H_ins: ~ NSet.In h (net.(onwState) n).(adjacent).
      move => H_ins.
      case: H_Adj.
      move: H_ins.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    have H_ins': ~ NSet.In n (net.(onwState) h).(adjacent).
      move => H_ins'.
      case: H_Adj'.
      move: H_ins'.
      exact: (Aggregation_in_adj_adjacent_to H_step1).
    case in_dec => /= H_dec; first by rewrite collate_msg_for_not_adjacent // in H_dec; case: H_ins; exact: (Aggregation_in_queue_fail_then_adjacent H_step1).
    move {H_dec}.
    rewrite (collate_msg_for_not_adjacent _ _ _ H_Adj).
    rewrite (collate_neq _ _ _ H_neq) //.
    rewrite (Aggregation_self_channel_empty H_step1) //=.
    rewrite {3 6}/sum_fail_map /=.
    have H_emp_hn: onwPackets net h n = [].
      have H_in_agg: forall m', ~ In (Aggregate m') (net.(onwPackets) h n).
        move => m' H_in_agg.
        case: H_ins.
        move: H_in_agg.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1).
      have H_in_f: ~ In Fail (net.(onwPackets) h n) by exact: (Aggregation_not_failed_no_fail H_step1).
      move: H_in_agg H_in_f.
      elim: (onwPackets net h n) => //.
      case => [m'|] l H_in_f H_in_agg H_in_m; first by case (H_in_agg m'); left.
      by case: H_in_m; left.      
    have H_emp_nh: onwPackets net n h = [].
      have H_in_agg: forall m', ~ In (Aggregate m') (net.(onwPackets) n h).
        move => m' H_in_agg.
        case: H_ins'.
        move: H_in_agg.
        exact: (Aggregation_aggregate_msg_dst_adjacent_src H_step1).
      have H_in_f: ~ In Fail (net.(onwPackets) n h) by exact: (Aggregation_not_failed_no_fail H_step1).
      move: H_in_agg H_in_f.
      elim: (onwPackets net n h) => //.
      case => [m'|] l H_in_f H_in_agg H_in_m; first by case (H_in_agg m'); left.
      by case: H_in_m; left.      
    rewrite H_emp_hn H_emp_nh /sum_fail_map /=.
    gsimpl.
    rewrite sum_fail_received_incoming_active_all_head_eq.
    rewrite sum_fail_received_incoming_active_all_head_eq in IH'.
    rewrite (sum_fail_received_incoming_active_all_head_eq ns').
    rewrite (sum_fail_received_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_fail_received_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_fail_received_incoming_active_all_head_eq ns').
    rewrite sum_aggregate_msg_incoming_active_all_head_eq.
    rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
    rewrite sum_fail_sent_incoming_active_all_head_eq.
    rewrite sum_fail_sent_incoming_active_all_head_eq in IH'.
    rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
    rewrite (sum_fail_sent_incoming_active_all_head_eq ns') in IH'.
    rewrite (sum_fail_sent_incoming_active_all_head_eq (n :: ns')).
    rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
    move: IH'.
    gsimpl.
    move => IH.
    aac_rewrite IH.
    move {IH}.
    rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
    rewrite -(sum_fail_sent_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
    rewrite -(sum_fail_received_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
    rewrite 2!(sum_fail_map_incoming_not_adjacent_collate_eq _ _ _ _ _ H_Adj).
    rewrite (sum_aggregate_msg_incoming_not_adjacent_collate_eq _ _ _ H_Adj).
    by aac_reflexivity.
  rewrite /=.
  gsimpl.
  have H_adj': adjacent_to n h by apply adjacent_to_symmetric in H_Adj.
  have H_ins: NSet.In h (net.(onwState) n).(adjacent) by exact: (Aggregation_adjacent_to_in_adj H_step1).
  have H_ins': NSet.In n (net.(onwState) h).(adjacent) by exact: (Aggregation_adjacent_to_in_adj H_step1).
  case: ifP => H_mem; last by move/negP: H_mem => H_mem; case: H_mem; apply NSetFacts.mem_1.
  move {H_mem}.
  have H_in_f: ~ In Fail (net.(onwPackets) h n) by exact: (Aggregation_not_failed_no_fail H_step1).
  have H_in_f': ~ In Fail (net.(onwPackets) n h) by exact: (Aggregation_not_failed_no_fail H_step1).
  case in_dec => /= H_dec_f //.
  move {H_dec_f}.
  case in_dec => /= H_dec_f //.
  move {H_dec_f}.
  rewrite (collate_neq _ _ _ H_neq) //.    
  case in_dec => /= H_dec_f.
    contradict H_dec_f.
    rewrite /update2.
    case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
    by rewrite (Aggregation_self_channel_empty H_step1).
  move {H_dec_f}.
  have H_in_n: ~ In n ns.
    move => H_in_n.
    rewrite -H_ex' in H_in_n.
    by apply exclude_in in H_in_n.
  case in_dec => /= H_dec_f; last first.
    case: H_dec_f.
    have H_a := collate_msg_for_live_adjacent_alt Fail _ _ H_Adj H_in_n.
    move: H_a.
    rewrite /=.
    case adjacent_to_dec => /= H_dec // {H_dec}.
    rewrite /=.
    move => H_a.
    by rewrite H_a; first by apply in_or_app; right; left.
  move {H_dec_f}.
  rewrite {3}/update2.
  case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  move {H_and}.
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  rewrite {5}/update2.
  case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  move {H_and}.
  have [m0 H_snt] := Aggregation_in_set_exists_find_sent H_step1 _ H0 H_ins'.
  have [m1 H_rcd] := Aggregation_in_set_exists_find_received H_step1 _ H0 H_ins'.
  rewrite /sum_fold.
  case H_snt': NMap.find => [m'0|]; last by rewrite H_snt in H_snt'.
  rewrite H_snt in H_snt'.
  injection H_snt' => H_eq_snt.
  rewrite -H_eq_snt {m'0 H_snt' H_eq_snt}.
  case H_rcd': NMap.find => [m'1|]; last by rewrite H_rcd in H_rcd'.
  rewrite H_rcd in H_rcd'.
  injection H_rcd' => H_eq_rcd.
  rewrite -H_eq_rcd {m'1 H_rcd' H_eq_rcd}.
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  rewrite {3}/sum_fail_map /=.
  rewrite {7}/update2.
  case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  rewrite (Aggregation_self_channel_empty H_step1) //=.
  rewrite {5}/sum_fail_map /=.
  gsimpl.
  rewrite sum_fail_received_incoming_active_all_head_eq.
  rewrite sum_fail_received_incoming_active_all_head_eq in IH'.
  rewrite (sum_fail_received_incoming_active_all_head_eq ns').
  rewrite (sum_fail_received_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_fail_received_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_fail_received_incoming_active_all_head_eq ns').
  rewrite sum_aggregate_msg_incoming_active_all_head_eq.
  rewrite sum_aggregate_msg_incoming_active_all_head_eq in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_aggregate_msg_incoming_active_all_head_eq ns').
  rewrite sum_fail_sent_incoming_active_all_head_eq.
  rewrite sum_fail_sent_incoming_active_all_head_eq in IH'.
  rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
  rewrite (sum_fail_sent_incoming_active_all_head_eq ns') in IH'.
  rewrite (sum_fail_sent_incoming_active_all_head_eq (n :: ns')).
  rewrite (sum_fail_sent_incoming_active_all_head_eq ns').
  move: IH'.
  gsimpl.
  move => IH.
  aac_rewrite IH.
  move {IH}.
  set u2 := update2 _ _ _ _.
  set cl := collate _ _ _.
  rewrite -(sum_aggregate_msg_incoming_active_singleton_neq_collate_eq _ _ H_neq).
  rewrite -(sum_fail_sent_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
  rewrite -(sum_fail_received_incoming_active_singleton_neq_collate_eq _ _ _ H_neq).
  rewrite /sum_fail_map.
  case in_dec => /= H_dec // {H_dec}.
  case in_dec => /= H_dec; last first.
    case: H_dec.
    rewrite /cl /u2.
    have H_a := collate_msg_for_live_adjacent_alt Fail _ _ H_Adj H_in_n.
    move: H_a.
    rewrite /=.
    case adjacent_to_dec => /= H_dec // {H_dec}.
    rewrite /=.
    move => H_a.
    rewrite H_a.
    by apply in_or_app; right; left.
  move {H_dec}.
  case: ifP => H_mem; last by move/negP: H_mem => H_mem; case: H_mem; exact: NSetFacts.mem_1.
  move {H_mem}.
  rewrite /sum_fold.
  have [m2 H_snt_n] := Aggregation_in_set_exists_find_sent H_step1 _ H_dec' H_ins.
  have [m3 H_rcd_n] := Aggregation_in_set_exists_find_received H_step1 _ H_dec' H_ins.
  case H_snt': NMap.find => [m'2|]; last by rewrite H_snt_n in H_snt'.
  rewrite H_snt_n in H_snt'.
  injection H_snt' => H_eq_snt.
  rewrite -H_eq_snt {m'2 H_snt' H_eq_snt}.
  case H_rcd': NMap.find => [m'3|]; last by rewrite H_rcd_n in H_rcd'.
  rewrite H_rcd_n in H_rcd'.
  injection H_rcd' => H_eq_rcd.
  rewrite -H_eq_rcd {m'3 H_rcd' H_eq_rcd}.
  gsimpl.
  rewrite sum_aggregate_msg_incoming_active_eq_not_in_eq //.
  rewrite {1}/cl {1}/u2.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite sum_aggregate_msg_incoming_active_collate_update2_eq //.
  rewrite {1}/cl /u2.
  rewrite sum_aggregate_msg_incoming_collate_update2_notin_eq //.
  rewrite sum_aggregate_msg_incoming_collate_msg_for_notin_eq //.
  have H_sr := Aggregation_sent_received_eq H_step1 H_dec' H0 H_ins H_ins' H_snt H_rcd_n.
  have H_rs := Aggregation_sent_received_eq H_step1 H0 H_dec' H_ins' H_ins H_snt_n H_rcd.
  rewrite H_sr H_rs {H_sr H_rs}.  
  gsimpl.
  have H_agg: sum_aggregate_msg (onwPackets net h n) * (sum_aggregate_msg (onwPackets net h n))^-1 = 1 by gsimpl.
  aac_rewrite H_agg.
  move {H_agg}.
  gsimpl.
  rewrite {1 2}/cl /u2.
  rewrite sum_fail_map_incoming_collate_not_in_eq //.
  rewrite sum_fail_map_incoming_collate_not_in_eq //.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite sum_fail_map_incoming_not_in_eq //.
  rewrite sum_fail_sent_incoming_active_collate_update2_eq //.
  rewrite sum_fail_sent_incoming_active_collate_update2_eq //.
  rewrite sum_fail_received_incoming_active_collate_update2_eq //.
  rewrite sum_fail_received_incoming_active_collate_update2_eq //.
  rewrite sum_fail_sent_incoming_active_not_in_eq_alt_alt //.
  rewrite sum_fail_received_incoming_active_not_in_eq_alt_alt //.
  rewrite /cl {u2 cl}.
  by aac_reflexivity.
Qed.

End Aggregation.

(*
Require Import StructTact.Fin.
Module FinGroup (CFG : CommutativeFinGroup).
Module N3 : NatValue. Definition n := 3. End N3.
Module FN_N3 : FinNameType N3 := FinName N3.
Module NOT_N3 : NameOrderedType FN_N3 := FinNameOrderedType N3 FN_N3.
Module NOTC_N3 : NameOrderedTypeCompat FN_N3 := FinNameOrderedTypeCompat N3 FN_N3.
Module ANC_N3 := FinCompleteAdjacentNameType N3 FN_N3.
Require Import MSetList.
Module N3Set <: MSetInterface.S := MSetList.Make NOT_N3.
Require Import FMapList.
Module N3Map <: FMapInterface.S := FMapList.Make NOTC_N3.
Module AG := Aggregation FN_N3 NOT_N3 N3Set NOTC_N3 N3Map CFG ANC_N3.
Print AG.Msg.
End FinGroup.
*)
