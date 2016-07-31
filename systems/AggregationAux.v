Require Import Verdi.
Require Import NameOverlay.
Require Import Sumbool.

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

Require Import OrderedLemmas.
Require Import AggregationDefinitions.

Set Implicit Arguments.

Module AAux (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC)
 (Import CFG : CommutativeFinGroup) (Import ANT : AdjacentNameType NT).

Module AD := ADefs NT NOT NSet NOTC NMap CFG.
Import AD.

Import GroupScope.

Section MsgFolds.

Context {am : AggregationMsg}.

Context {data} {ad : AggregationData data}.

Lemma sum_aggregate_msg_incoming_step_o_init :
  forall ns n, sum_aggregate_msg_incoming ns (fun _ _ => []) n = 1.
Proof.
move => ns n.
rewrite /sum_aggregate_msg_incoming /= {n}.
elim: ns => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_active_step_o_init :
  forall actns allns, sum_aggregate_msg_incoming_active allns actns (fun _ _ => []) = 1.
Proof.
rewrite /sum_aggregate_msg_incoming_active /=.
elim => [|a l IH] l' //=.
rewrite IH sum_aggregate_msg_incoming_step_o_init.
by gsimpl.
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
elim => //= [|mg l' IH] l2; first by gsimpl.
rewrite IH.
rewrite /aggregate_sum_fold /=.
by aac_reflexivity.
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
apply Permutation_split in H_pm.
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
apply Permutation_split in H_pm.
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

Lemma sumM_sumM_active_eq : 
  forall (ns : list name) (adj adj' : NS) (map : NM) (f : name -> name -> list aggr_msg) (n : name),
  NoDup ns ->
  (forall n', In aggr_fail (f n' n) -> ~ In n' ns) ->
  (forall n', NSet.In n' adj' -> NSet.In n' adj /\ ~ In aggr_fail (f n' n)) ->
  (forall n', NSet.In n' adj -> NSet.In n' adj' \/ In aggr_fail (f n' n)) ->
  (forall n', NSet.In n' adj -> exists m', NMap.find n' map = Some m') ->
  (forall n', NSet.In n' adj -> (In n' ns \/ In aggr_fail (f n' n))) ->
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

Lemma sumM_remove_fail_ex_eq : 
  forall ns f adj map n,
    NoDup ns ->
    (forall n', NSet.In n' adj -> In n' ns) ->
    (forall n', NSet.In n' adj -> exists m', NMap.find n' map = Some m') ->
    exists adj', 
      sumM adj map * (sum_fail_map_incoming ns f n adj map)^-1 = sumM adj' map /\
      (forall n', NSet.In n' adj' -> (NSet.In n' adj /\ ~ In aggr_fail (f n' n))) /\
      (forall n', NSet.In n' adj -> (NSet.In n' adj' \/ In aggr_fail (f n' n))).
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

End MsgFolds.

Section MsgProps.

Context {am : AggregationMsg}.

Context {data} {ad : AggregationData data}.

Lemma sum_aggregate_msg_neq_from :
forall from to n packets ms ns,
~ In from ns ->
fold_right
  (fun (n' : name) (partial : m) => 
     partial * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns =
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
     partial * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns =
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
          partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns0) 1 ns1 = 
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
  sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) n =
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
    sum_aggregate_msg_incoming_active ns' ns (update2 name_eq_dec f from to ms) =
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
      partial * sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) n0) 1 ns0 =
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
suff H_suff: update2 name_eq_dec f from to ms n' n = f n' n by rewrite H_suff.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq H_eq'].
by rewrite H_eq' in H_neq.
Qed.

Lemma sum_aggregate_msg_fold_split :
forall ns0 ns1 ns2 from to ms packets,
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns0) 1 (ns1 ++ ns2) = 
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns0) 1 ns1 * 
fold_right (fun (n : name) (partial : m) => partial * fold_right (fun (n' : name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns0) 1 ns2.
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
        partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 (ns0 ++ ns1) = 
fold_right (fun (n' : name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns0 *
fold_right (fun (n' : name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 name_eq_dec packets from to ms n' n)) 1 ns1.
Proof.
move => ns0 ns1 from to n onet ms.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH /=.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_update2_eq :
  forall ns f from to ms n,
  ~ In from ns ->
  sum_aggregate_msg_incoming ns (update2 name_eq_dec f from to ms) n =
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

Lemma sum_fail_map_incoming_sent_neq_eq :
  forall ns packets state from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 name_eq_dec packets from to ms) n
    (aggr_adjacent (match name_eq_dec n to with left _ => d | right_ => state n end))
    (aggr_sent (match name_eq_dec n to with left _ => d |right _ => state n end)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_sent (state n)).
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
  sum_fail_map_incoming ns (update2 name_eq_dec packets from to ms) n
    (aggr_adjacent (match name_eq_dec n to with left _ => d | right_ => state n end))
    (aggr_received (match name_eq_dec n to with left _ => d |right _ => state n end)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_received (state n)).
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

Lemma sum_fail_sent_incoming_active_not_in_eq_alt :
forall ns1 ns0 packets state h d,
  ~ In h ns1 ->
  sum_fail_sent_incoming_active ns0 ns1 packets (update name_eq_dec state h d) =
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

Lemma sum_fail_received_incoming_active_not_in_eq_alt :
forall ns packets state h d,
  ~ In h ns ->
  sum_fail_received_incoming_active nodes ns packets (update name_eq_dec state h d) =
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
    sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) n adj map =
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
  sum_fail_map_incoming ns (collate name_eq_dec h f l) n adj map =
  sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
case => n0 mg l IH ns h n f adj map H_in.
rewrite IH //.
by rewrite sum_fail_map_incoming_not_in_eq.
Qed.

Lemma sum_fail_map_incoming_update2_remove_eq :
  forall ns f from to ms adj map,
  ~ In from ns ->
  sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) to (NSet.remove from adj) (NMap.remove from map) =
  sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) to adj map.
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

Lemma Nodes_data_not_in_eq :
  forall ns (state : name -> data) to d,
    ~ In to ns ->
    Nodes_data ns (update name_eq_dec state to d) =
    Nodes_data ns state.
Proof.
elim => //.
move => n ns IH state to d H_in.
rewrite /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
case name_eq_dec => H_dec //.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma sum_fail_map_incoming_sent_neq_eq_alt :
  forall ns packets state from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 name_eq_dec packets from to ms) n
    (aggr_adjacent (update name_eq_dec state h d n))
    (aggr_sent (update name_eq_dec state h d n)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_sent (state n)).
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

Lemma sum_fail_map_incoming_received_neq_eq_alt :
  forall ns packets state from to ms h n d,
  n <> to ->
  n <> h ->
  sum_fail_map_incoming ns (update2 name_eq_dec packets from to ms) n
    (aggr_adjacent (update name_eq_dec state h d n))
    (aggr_received (update name_eq_dec state h d n)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_received (state n)).
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
    sum_fail_received_incoming_active ns1 ns0 (update2 name_eq_dec packets from to ms) (update name_eq_dec state h d) =
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
      sum_fail_map_incoming ns (update2 name_eq_dec f h n ms) h adj map =
      sum_fail_map_incoming ns f h adj map.
Proof.
elim => //=.
move => n0 l IH f h n ms adj map H_neq.
rewrite IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_dec; first by move: H_dec => [H_eq H_eq']; rewrite H_eq' in H_neq.
Qed.

Lemma sum_fail_map_incoming_not_in_fail_update2_eq :
  forall ns f h x ms adj map,
    h <> x ->
    sum_fail_map_incoming ns (update2 name_eq_dec f h x ms) h adj map =
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
    sum_fail_sent_incoming_active ns1 ns0 packets (update name_eq_dec state h d) =
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
    sum_fail_received_incoming_active ns1 ns0 packets (update name_eq_dec state h d) =
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

Lemma sum_aggregate_msg_incoming_active_singleton_neq_update2_eq :
  forall ns f h n n' ms,
    h <> n ->
    sum_aggregate_msg_incoming_active [n] ns f =
    sum_aggregate_msg_incoming_active [n] ns (update2 name_eq_dec f h n' ms).
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

Lemma sum_fail_sent_incoming_active_singleton_neq_update2_eq :
  forall ns f g h n n' ms,
    h <> n ->
    sum_fail_sent_incoming_active [n] ns f g =
    sum_fail_sent_incoming_active [n] ns (update2 name_eq_dec f h n' ms) g.
Proof.
elim => //=.
move => n0 ns IH f g h n n' ms H_neq.
gsimpl.
rewrite -IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_fail_received_incoming_active_singleton_neq_update2_eq :
  forall ns f g h n n' ms,
    h <> n ->
    sum_fail_received_incoming_active [n] ns f g =
    sum_fail_received_incoming_active [n] ns (update2 name_eq_dec f h n' ms) g.
Proof.
elim => //=.
move => n0 ns IH f g h n n' ms H_neq.
gsimpl.
rewrite -IH //.
rewrite /update2.
by case (sumbool_and _ _ _ _) => H_and; first by move: H_and => [H_and H_and'].
Qed.

Lemma sum_aggregate_msg_incoming_active_eq_not_in_eq :
forall ns ns' from to ms f,
  ~ In to ns ->
  sum_aggregate_msg_incoming_active ns' ns (update2 name_eq_dec f from to ms) =
  sum_aggregate_msg_incoming_active ns' ns f.
Proof.
elim => //=.
move => n ns IH ns' from to ms f H_in.
have H_not_in: ~ In to ns by move => H_in'; case: H_in; right.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_neq_eq.
Qed.

Lemma sum_aggregate_msg_incoming_collate_update2_eq :
  forall ns h n n' f l ms,
  n' <> n ->
  sum_aggregate_msg_incoming ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) n' =
  sum_aggregate_msg_incoming ns (collate name_eq_dec h f l) n'.
Proof.
elim => //=.
move => n0 ns IH h n n' f l ms H_neq.
set f1 := update2 _ _ _ _ _.
have H_eq: f1 n0 n' = f n0 n'.
  rewrite /f1.
  rewrite /update2.
  by case sumbool_and => /= H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite (collate_f_eq _ _ name_eq_dec _ _ _ _ _ _ H_eq) {H_eq}.
rewrite /f1 {f1}.
by case in_dec => /= H_dec; rewrite IH.
Qed.

Lemma sum_aggregate_msg_incoming_active_collate_update2_eq :
  forall ns ns' h n f l ms,
    ~ In n ns ->
    sum_aggregate_msg_incoming_active ns' ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) =
    sum_aggregate_msg_incoming_active ns' ns (collate name_eq_dec h f l).
Proof.
elim => //=.
move => n' ns IH ns' h n f l ms H_in.
have H_neq: n' <> n by move => H_in'; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
rewrite IH //.
by rewrite sum_aggregate_msg_incoming_collate_update2_eq.
Qed.

Lemma sum_aggregate_msg_incoming_collate_update2_notin_eq :
  forall ns h n f n' l ms,
    ~ In h ns ->
    sum_aggregate_msg_incoming ns (collate name_eq_dec h (update2 name_eq_dec  f h n' ms) l) n =
    sum_aggregate_msg_incoming ns (collate name_eq_dec h f l) n.
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
  set up2 := update2 _ _ _ _ _.
  have H_eq_f: up2 n0 n = f n0 n by rewrite /up2 /update2; case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  by rewrite (collate_f_eq _ _ name_eq_dec _ _ _ _ _ _ H_eq_f).
- rewrite IH //.
  set up2 := update2 _ _ _ _ _.
  have H_eq_f: up2 n0 n = f n0 n by rewrite /up2 /update2; case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  by rewrite (collate_f_eq _ _ name_eq_dec _ _ _ _ _ _ H_eq_f).
Qed.

Lemma sum_fail_map_incoming_collate_update2_eq :
  forall ns h n n' f l ms adj map,
  n' <> n ->
  sum_fail_map_incoming ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) n' adj map =
  sum_fail_map_incoming ns (collate name_eq_dec h f l) n' adj map.
Proof.
elim => //=.
move => n0 ns IH h n n' f l ms adj map H_neq.
set f1 := update2 _ _ _ _ _.
have H_eq: f1 n0 n' = f n0 n'.
  rewrite /f1.
  rewrite /update2.
  by case sumbool_and => /= H_and; first by move: H_and => [H_eq H_eq']; rewrite H_eq' in H_neq.
rewrite (collate_f_eq _ _ name_eq_dec _ _ _ _ _ _ H_eq) {H_eq}.
rewrite /f1 {f1}.
by rewrite IH.
Qed.

Lemma sum_fail_sent_incoming_active_collate_update2_eq :
  forall ns ns' h n f g l ms,
  ~ In n ns ->
  sum_fail_sent_incoming_active ns' ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) g =
  sum_fail_sent_incoming_active ns' ns (collate name_eq_dec h f l) g.
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
  sum_fail_received_incoming_active ns' ns (collate name_eq_dec h (update2 name_eq_dec f h n ms) l) g =
  sum_fail_received_incoming_active ns' ns (collate name_eq_dec h f l) g.
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
      sum_fail_map_incoming ns (update2 name_eq_dec f from to ms) n adj map =
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
  sum_fail_sent_incoming_active ns1 ns0 (update2 name_eq_dec f from to ms) g =
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
  sum_fail_received_incoming_active ns1 ns0 (update2 name_eq_dec f from to ms) g =
  sum_fail_received_incoming_active ns1 ns0 f g.
Proof.
elim => //.
move => n ns IH ns1 from to ms f g H_in.
have H_neq: to <> n by move => H_eq; case: H_in; left.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
rewrite /= IH //.
by rewrite sum_fail_map_incoming_update2_not_eq_alt.
Qed.

Lemma fold_right_update_id :
forall (ns : list name) h state,
fold_right 
  (fun (n : name) (l' : list data) =>
     update name_eq_dec state h (state h) n :: l') [] ns =
fold_right 
  (fun (n : name) (l' : list data) =>
     (state n) :: l') [] ns.
Proof.
elim => //.
move => n l IH h state.
rewrite /= IH.
rewrite /update /=.
case name_eq_dec => H_dec //.
by rewrite H_dec.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq :
  forall ns0 ns1 packets state from to ms d,
    ~ In to ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 
      (update2 name_eq_dec packets from to ms) 
      (fun nm : name => match name_eq_dec nm to with left _ => d | right _ => state nm end) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms d H_in.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_sent_neq_eq //=.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 packets state from to ms d H_in'.
rewrite /sum_fail_sent_incoming_active in IH'.
by rewrite IH' /=.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq :
  forall ns0 ns1 packets state from to ms d,
    ~ In to ns0 ->
    sum_fail_received_incoming_active ns1 ns0 (update2 name_eq_dec packets from to ms)
     (fun nm : name => match name_eq_dec nm to with left _ => d | right _ => state nm end) =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms d H_in.
rewrite /sum_fail_received_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite sum_fail_map_incoming_received_neq_eq //=.
have H_in': ~ In to ns by move => H_in'; case: H_in; right.
have IH' := IH ns1 packets state from to ms d H_in'.
rewrite /sum_fail_received_incoming_active in IH'.
by rewrite IH'.
Qed.

Lemma sum_fail_sent_incoming_active_not_in_eq_alt2 :
  forall ns0 ns1 packets state from to ms h d,
    ~ In to ns0 ->
    ~ In h ns0 ->
    sum_fail_sent_incoming_active ns1 ns0 (update2 name_eq_dec packets from to ms) (update name_eq_dec state h d) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //.
move => n ns IH ns1 packets state from to ms h d H_in H_in'.
rewrite /sum_fail_sent_incoming_active /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
have H_neq': n <> h by move => H_eq; case: H_in'; left.
rewrite sum_fail_map_incoming_sent_neq_eq_alt //=.
have H_inn: ~ In to ns by move => H_inn; case: H_in; right.
have H_inn': ~ In h ns by move => H_inn'; case: H_in'; right.
have IH' := IH ns1 packets state from to ms h d H_inn H_inn'.
rewrite /sum_fail_sent_incoming_active in IH'.
by rewrite IH'.
Qed.

Lemma sum_aggregate_msg_incoming_active_singleton_neq_collate_eq :
  forall ns f h n,
  h <> n ->
  sum_aggregate_msg_incoming_active [n] ns f =  
  sum_aggregate_msg_incoming_active [n] ns (collate name_eq_dec h f (map_snd aggr_fail (filter_rel adjacent_to_dec h ns))).
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

Lemma sum_fail_sent_incoming_active_singleton_neq_collate_eq :
  forall ns f g h n,
  h <> n ->
  sum_fail_sent_incoming_active [n] ns f g = 
  sum_fail_sent_incoming_active [n] ns (collate name_eq_dec h f (map_snd aggr_fail (filter_rel adjacent_to_dec h ns))) g.
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

Lemma sum_fail_received_incoming_active_singleton_neq_collate_eq :
  forall ns f g h n,
  h <> n ->
  sum_fail_received_incoming_active [n] ns f g =
  sum_fail_received_incoming_active [n] ns (collate name_eq_dec h f (map_snd aggr_fail (filter_rel adjacent_to_dec h ns))) g.
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
  sum_fail_map_incoming ns (collate name_eq_dec h f (map_snd aggr_fail (filter_rel adjacent_to_dec h ns'))) n adj map =
  sum_fail_map_incoming ns f n adj map.
Proof.
elim => //=.
move => n' ns IH ns' f h n adj map H_adj.
rewrite IH //.
case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
rewrite -H_dec.
by rewrite collate_map_pair_not_related.
Qed.

Lemma sum_aggregate_msg_incoming_not_adjacent_collate_eq :
  forall ns ns' f h n,
  ~ adjacent_to h n ->
  sum_aggregate_msg_incoming ns (collate name_eq_dec h f (map_snd aggr_fail (filter_rel adjacent_to_dec h ns'))) n =
  sum_aggregate_msg_incoming ns f n.
Proof.
elim => //=.
move => n' ns IH ns' f h n H_adj.
rewrite IH //.
case (name_eq_dec h n') => H_dec; last by rewrite collate_neq.
rewrite -H_dec.
by rewrite collate_map_pair_not_related.
Qed.

End MsgProps.

End AAux.
