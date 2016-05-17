Require Import Verdi.
Require Import NameOverlay.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.

Require Import mathcomp.fingroup.fingroup.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import FMapInterface.

Require Import AAC_tactics.AAC.

Set Implicit Arguments.

Module Type CommutativeFinGroup.
Parameter gT : finGroupType.
Parameter mulgC : @commutative gT _ mulg.
End CommutativeFinGroup.

Module ADefs (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC)
 (Import CFG : CommutativeFinGroup).

Import GroupScope.

Instance aac_mulg_Assoc : Associative eq (mulg (T:=gT)) := mulgA (T:=gT).

Instance aac_mulg_Comm : Commutative eq (mulg (T:=gT)) := mulgC.

Instance aac_mulg_unit : Unit eq (mulg (T:=gT)) 1.
Proof.
apply: (Build_Unit eq mulg 1) => x. 
- by rewrite mul1g.
- by rewrite mulg1.
Qed.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Definition m := gT.

Definition m_eq_dec : forall (a b : m), {a = b} + {a <> b}.
move => a b.
case H_dec: (a == b); move: H_dec; first by case/eqP; left.
move => H_eq; right.
case/eqP => H_neq.
by rewrite H_eq in H_neq.
Defined.

Definition NS := NSet.t.
Definition NM := NMap.t m.

Definition fins_lt (fins fins' : NS) : Prop :=
NSet.cardinal fins < NSet.cardinal fins'.

Lemma fins_lt_well_founded : well_founded fins_lt.
Proof.
apply (well_founded_lt_compat _ (fun fins => NSet.cardinal fins)).
by move => x y; rewrite /fins_lt => H.
Qed.

Definition init_map_t (fins : NS) : Type := 
{ map : NM | forall n, NSet.In n fins <-> NMap.find n map = Some 1 }.

Definition init_map_F : forall fins : NS, 
  (forall fins' : NS, fins_lt fins' fins -> init_map_t fins') ->
  init_map_t fins.
rewrite /init_map_t.
refine
  (fun (fins : NS) init_map_rec =>
   match NSet.choose fins as finsopt return (_ = finsopt -> _) with
   | None => fun (H_eq : _) => exist _ (NMap.empty m) _
   | Some n => fun (H_eq : _) => 
     match init_map_rec (NSet.remove n fins) _ with 
     | exist fins' H_fins' => exist _ (NMap.add n 1 fins') _
     end
   end (refl_equal _)).
- rewrite /fins_lt /=.
  apply NSet.choose_spec1 in H_eq.
  set fn := NSet.remove _ _.
  have H_notin: ~ NSet.In n fn by move => H_in; apply NSetFacts.remove_1 in H_in.
  have H_add: NSetProps.Add n fn fins.
    rewrite /NSetProps.Add.
    move => k.
    split => H_in.      
      case (name_eq_dec n k) => H_eq'; first by left.
      by right; apply NSetFacts.remove_2.
    case: H_in => H_in; first by rewrite -H_in.
    by apply NSetFacts.remove_3 in H_in.
  have H_card := NSetProps.cardinal_2 H_notin H_add.
  rewrite H_card {H_notin H_add H_card}.
  by auto with arith.
- move => n'.
  apply NSet.choose_spec1 in H_eq.
  case (name_eq_dec n n') => H_eq_n.
    rewrite -H_eq_n.
    split => //.
    move => H_ins.
    apply NMapFacts.find_mapsto_iff.
    exact: NMap.add_1.
  split => H_fins.
    apply NMapFacts.find_mapsto_iff.
    apply NMapFacts.add_neq_mapsto_iff => //.
    apply NMapFacts.find_mapsto_iff.    
    apply H_fins'.
    exact: NSetFacts.remove_2.
  apply NMapFacts.find_mapsto_iff in H_fins.
  apply NMapFacts.add_neq_mapsto_iff in H_fins => //.
  apply NMapFacts.find_mapsto_iff in H_fins.
  apply H_fins' in H_fins.
  by apply NSetFacts.remove_3 in H_fins.    
- move => n.
  apply NSet.choose_spec2 in H_eq.
  split => H_fin; first by contradict H_fin; auto with set.
  apply NMap.find_2 in H_fin.
  contradict H_fin.
  exact: NMap.empty_1.
Defined.

Definition init_map_str : forall (fins : NS), init_map_t fins :=
  @well_founded_induction_type
  NSet.t
  fins_lt
  fins_lt_well_founded
  init_map_t
  init_map_F.

Definition init_map (fins : NS) : NM := 
match init_map_str fins with
| exist map _ => map
end.

Definition sum_fold (fm : NM) (n : name) (partial : m) : m :=
match NMap.find n fm with
| Some m' => partial * m'
| None => partial
end.

Definition sumM (fs : NS) (fm : NM) : m := 
NSet.fold (sum_fold fm) fs 1.

Definition sum_active_fold (adj : NS) (map : NM) (n : name) (partial : m) : m :=
if NSet.mem n adj
then sum_fold map n partial
else partial.

Definition sumM_active (adj : NS) (map : NM) (ns : list name) : m :=
fold_right (sum_active_fold adj map) 1 ns.

Class AggregationData (data : Type) :=
  {
    aggr_local : data -> m ;
    aggr_aggregate : data -> m ;
    aggr_adjacent : data -> NS ;
    aggr_sent : data -> NM ;
    aggr_received : data -> NM
  }.

Section AggregationProps.

Context {data} {ad : AggregationData data}.

Definition conserves_node_mass (d : data) : Prop := 
d.(aggr_local) = d.(aggr_aggregate) * sumM d.(aggr_adjacent) d.(aggr_sent) * (sumM d.(aggr_adjacent) d.(aggr_received))^-1.

Definition sum_local (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * d.(aggr_local)) 1 l.

Definition sum_aggregate (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * d.(aggr_aggregate)) 1 l.

Definition sum_sent (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * sumM d.(aggr_adjacent) d.(aggr_sent)) 1 l.

Definition sum_received (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * sumM d.(aggr_adjacent) d.(aggr_received)) 1 l.

Definition conserves_mass_globally (l : list data) : Prop :=
sum_local l = sum_aggregate l * sum_sent l * (sum_received l)^-1.

Definition conserves_node_mass_all (l : list data) : Prop :=
forall d, In d l -> conserves_node_mass d.

Definition Nodes_data (ns : list name) (state : name -> data) : list data :=
fold_right (fun (n : name) (l' : list data) => n.(state) :: l') [] ns.

End AggregationProps.

Class AggregationMsg :=
  {
    aggr_msg : Type ;
    aggr_msg_eq_dec : forall x y : aggr_msg, {x = y} + {x <> y} ;
    aggr_fail : aggr_msg ;
    aggr_of : aggr_msg -> m ;
  }.

Section MsgFolds.

Context {am : AggregationMsg}.

Context {data} {ad : AggregationData data}.

Definition aggregate_sum_fold (mg : aggr_msg) (partial : m) : m :=
partial * aggr_of mg.

Definition sum_aggregate_msg := fold_right aggregate_sum_fold 1.

(* given n, sum aggregate messages for all its incoming channels *)
Definition sum_aggregate_msg_incoming (ns : list name) (packets : name -> name -> list aggr_msg) (n : name) : m := 
fold_right (fun (n' : name) (partial : m) => 
  partial * if In_dec aggr_msg_eq_dec aggr_fail (packets n' n) then 1 else sum_aggregate_msg (packets n' n)) 1 ns.

(* given list of active names and all names, sum all incoming channels for all active *)
Definition sum_aggregate_msg_incoming_active (allns : list name) (actns : list name)  (packets : name -> name -> list aggr_msg) : m :=
fold_right (fun (n : name) (partial : m) => partial * sum_aggregate_msg_incoming allns packets n) 1 actns.

Definition sum_fail_map (l : list aggr_msg) (from : name) (adj : NS) (map : NM) : m :=
if In_dec aggr_msg_eq_dec aggr_fail l && NSet.mem from adj then sum_fold map from 1 else 1.

Definition sum_fail_map_incoming (ns : list name) (packets : name -> name -> list aggr_msg) (n : name) (adj : NS) (map : NM) : m :=
fold_right (fun (n' : name) (partial : m) => partial * sum_fail_map (packets n' n) n' adj map) 1 ns.

Definition sum_fail_sent_incoming_active (allns : list name) (actns : list name) (packets : name -> name -> list aggr_msg) (state : name -> data) : m :=
fold_right (fun (n : name) (partial : m) => 
  partial * sum_fail_map_incoming allns packets n n.(state).(aggr_adjacent) n.(state).(aggr_sent)) 1 actns.

Definition sum_fail_received_incoming_active (allns : list name) (actns : list name) (packets : name -> name -> list aggr_msg) (state : name -> data) : m :=
fold_right (fun (n : name) (partial : m) => 
  partial * sum_fail_map_incoming allns packets n n.(state).(aggr_adjacent) n.(state).(aggr_received)) 1 actns.

Definition conserves_network_mass (actns : list name) (allns : list name) (packets : name -> name -> list aggr_msg) (state : name -> data) : Prop :=
sum_local (Nodes_data actns state) = 
  sum_aggregate (Nodes_data actns state) * sum_aggregate_msg_incoming_active allns actns packets * 
  sum_fail_sent_incoming_active allns actns packets state * (sum_fail_received_incoming_active allns actns packets state)^-1.

End MsgFolds.

Class AggregationMsgMap (P1 : AggregationMsg) (P2 : AggregationMsg) :=
  {
    map_msgs : list (@aggr_msg P1) -> list (@aggr_msg P2) ;
    sum_aggregate_msg_map_msgs_eq : forall ms, sum_aggregate_msg ms = sum_aggregate_msg (map_msgs ms) ;
    aggr_fail_in_in : forall ms, In aggr_fail ms <-> In aggr_fail (map_msgs ms)
  }.

Section AggregationInstProps.

Context {data_fst} {ad_fst : AggregationData data_fst}.
Context {data_snd} {ad_snd : AggregationData data_snd}.

Lemma sum_local_aggr_local_eq :
  forall (state : name -> data_fst) (state' : name -> data_snd) ns,
   (forall n, In n ns -> n.(state).(aggr_local) = n.(state').(aggr_local)) ->
    sum_local (Nodes_data ns state) = sum_local (Nodes_data ns state').
Proof.
move => state state'.
elim => //=.
move => n ns IH H_in.
rewrite /= H_in; last by left.
rewrite IH //.
move => n' H_in'.
by rewrite H_in; last by right.
Qed.

Lemma sum_aggregate_aggr_aggregate_eq :
  forall (state : name -> data_fst) (state' : name -> data_snd) ns,
   (forall n, In n ns -> n.(state).(aggr_aggregate) = n.(state').(aggr_aggregate)) ->
    sum_aggregate (Nodes_data ns state) = sum_aggregate (Nodes_data ns state').
Proof.
move => state state'.
elim => //=.
move => n ns IH H_in.
rewrite /= H_in; last by left.
rewrite IH //.
move => n' H_in'.
by rewrite H_in; last by right.
Qed.

Context {am_fst : AggregationMsg}.
Context {am_snd : AggregationMsg}.
Context {amm : AggregationMsgMap am_fst am_snd}.

Lemma sum_aggregate_msg_incoming_map_msgs_eq :
  forall (ns : list name) (packets : name -> name -> list (@aggr_msg am_fst)) (n : name),
  sum_aggregate_msg_incoming ns packets n = sum_aggregate_msg_incoming ns (fun src dst => map_msgs (packets src dst)) n.
Proof.
elim => //=.
move => n ns IH packets n'.
rewrite /is_left /=.
case in_dec => H_dec; case in_dec => H_dec'.
- by gsimpl; rewrite IH.
- by apply aggr_fail_in_in in H_dec.
- by apply aggr_fail_in_in in H_dec'.
- by rewrite sum_aggregate_msg_map_msgs_eq IH.
Qed.

Lemma sum_aggregate_msg_incoming_active_map_msgs_eq :
  forall (actns allns : list name) (packets : name -> name -> list (@aggr_msg am_fst)),
  sum_aggregate_msg_incoming_active allns actns packets = sum_aggregate_msg_incoming_active allns actns (fun src dst => map_msgs (packets src dst)).
Proof.
elim => //=.
move => n ns IH allns packets.
by rewrite sum_aggregate_msg_incoming_map_msgs_eq IH.
Qed.

Lemma sum_fail_map_map_msgs_eq :
  forall (packets : name -> name -> list (@aggr_msg am_fst)) src dst from adj map,
    sum_fail_map (packets src dst) from adj map = sum_fail_map (map_msgs (packets src dst)) from adj map.
Proof.
move => packets src dst from adj map.
rewrite /sum_fail_map /=.
case in_dec => H_dec; case in_dec => /= H_dec' //; first by apply aggr_fail_in_in in H_dec.
by apply aggr_fail_in_in in H_dec'.
Qed.

Lemma sum_fail_map_incoming_map_msgs_eq :
  forall ns (packets : name -> name -> list (@aggr_msg am_fst)) n adj map,
     sum_fail_map_incoming ns packets n adj map = sum_fail_map_incoming ns (fun src dst => map_msgs (packets src dst)) n adj map.
Proof.
elim => //=.
move => n ns IH packets n' adj map.
by rewrite sum_fail_map_map_msgs_eq // IH.
Qed.

Lemma sum_fail_sent_incoming_active_map_msgs_eq :
  forall (state : name -> data_fst) (state' : name -> data_snd) (packets : name -> name -> list (@aggr_msg am_fst)) allns actns,
    (forall n, In n actns -> n.(state).(aggr_adjacent) = n.(state').(aggr_adjacent)) ->
    (forall n, In n actns -> n.(state).(aggr_sent) = n.(state').(aggr_sent)) ->    
    sum_fail_sent_incoming_active allns actns packets state = 
    sum_fail_sent_incoming_active allns actns (fun src dst => map_msgs (packets src dst)) state'.
Proof.
move => state state' packets allns.
elim => //=.
move => n actns IH H_eq H_eq'.
rewrite sum_fail_map_incoming_map_msgs_eq //.
rewrite H_eq; last by left.
rewrite H_eq'; last by left.
rewrite IH //.
  move => n' H_in.
  by rewrite H_eq; last by right.
move => n' H_in.
by rewrite H_eq'; last by right.
Qed.

Lemma sum_fail_received_incoming_active_map_msgs_eq :
  forall (state : name -> data_fst) (state' : name -> data_snd) (packets : name -> name -> list (@aggr_msg am_fst)) allns actns,
    (forall n, In n actns -> n.(state).(aggr_adjacent) = n.(state').(aggr_adjacent)) ->
    (forall n, In n actns -> n.(state).(aggr_received) = n.(state').(aggr_received)) ->
    sum_fail_received_incoming_active allns actns packets state = 
    sum_fail_received_incoming_active allns actns (fun src dst => map_msgs (packets src dst)) state'.
Proof.
move => state state' packets allns.
elim => //=.
move => n actns IH H_eq H_eq'.
rewrite sum_fail_map_incoming_map_msgs_eq //.
rewrite H_eq; last by left.
rewrite H_eq'; last by left.
rewrite IH //.
  move => n' H_in.
  by rewrite H_eq; last by right.
move => n' H_in.
by rewrite H_eq'; last by right.
Qed.

End AggregationInstProps.

End ADefs.
