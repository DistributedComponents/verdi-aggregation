Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Sumbool.

Require Import ssreflect.
Require Import ssrbool.
Require Import eqtype.
Require Import fintype.
Require Import finset.
Require Import fingroup.

Require Import AAC.

Set Implicit Arguments.

Module Type CommutativeMassGroup.
Parameter gT : finGroupType.
Parameter commutes : forall x y : gT, commute x y.
End CommutativeMassGroup.

Module Aggregation (N : NatValue) (CMG : CommutativeMassGroup) <:
       CommutativeMassGroup 
       with Definition gT := CMG.gT
       with Definition commutes := CMG.commutes.

Definition gT := CMG.gT.
Definition commutes := CMG.commutes.

Import GroupScope.

Instance aac_mulg_Assoc : Associative eq (mulg (T:=gT)) := mulgA (T:=gT).

Instance aac_mulg_Comm : Commutative eq (mulg (T:=gT)).
move => x y.
rewrite commute_sym //.
exact: commutes.
Defined.

Instance aac_mulg_unit : Unit eq (mulg (T:=gT)) 1.
apply: (Build_Unit eq (mulg (T:=gT)) 1 _ _) => x; first by rewrite mul1g.
by rewrite mulg1.
Defined.
 
Definition num_sources := N.n.

Require Import OrderedTypeEx.
Require Import FMapList.
Module fin_n_compat_OT := fin_OT_compat N.
Module FinNMap <: FMapInterface.S := FMapList.Make fin_n_compat_OT.

Require Import Orders.
Require Import MSetList.
Module fin_n_OT := fin_OT N.
Module FinNSet <: MSetInterface.S := MSetList.Make fin_n_OT.

Require Import MSetFacts.
Module FinNSetFacts := Facts FinNSet.

Require Import MSetProperties.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.
Require Import FMapFacts.
Module FinNMapFacts := Facts FinNMap.
  
Definition m := gT.

Definition FinNM := FinNMap.t m.

Definition FinNS := FinNSet.t.

Definition m_eq_dec : forall (a b : m), { a = b }+{ a <> b }.
move => a b.
case H_dec: (a == b); move: H_dec; first by case/eqP; left.
move => H_eq; right.
case/eqP => H_neq.
by rewrite H_eq in H_neq.
Defined.

Definition Name := (fin num_sources).

Definition list_sources := (all_fin num_sources).

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
exact: fin_eq_dec.
Defined.

Inductive Msg := 
| Aggregate : m -> Msg
| Fail : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Input :=
| Local : m -> Input
| SendAggregate : Name -> Input
| AggregateRequest : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: Name_eq_dec.
Defined.

Inductive Output :=
| AggregateResponse : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data :=  mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : FinNS ; 
  sent : FinNM ; 
  received : FinNM 
}.

Definition Nodes := list_sources.

Theorem In_n_Nodes : forall n : Name, In n Nodes.
Proof. exact: all_fin_all. Qed.

Theorem nodup : NoDup Nodes.
Proof. exact: all_fin_NoDup. Qed.

Parameter Adjacent_to : relation Name.

Parameter Adjacent_to_symmetric : Symmetric Adjacent_to.

Parameter Adjacent_to_irreflexive : Irreflexive Adjacent_to.

Parameter Adjacent_to_dec : forall n n', { Adjacent_to n n' } + { ~ Adjacent_to n n' }.

Definition Adjacent_to_node (n : Name) := 
filter (Adjacent_to_dec n).

Lemma Adjacent_to_node_Adjacent_to : 
  forall n n' ns,
  In n' (Adjacent_to_node n ns) -> In n' ns /\ Adjacent_to n n'.
Proof.
move => n n' ns H_in.
rewrite /Adjacent_to_node in H_in.
apply filter_In in H_in.
move: H_in => [H_in H_eq].
split => //.
move: H_eq.
by case (Adjacent_to_dec _ _) => H_dec H.
Qed.

Lemma Adjacent_to_Adjacent_to_node : 
  forall n n' ns,
  In n' ns -> 
  Adjacent_to n n' ->
  In n' (Adjacent_to_node n ns).
Proof.
move => n n' ns H_in H_adj.
apply filter_In.
split => //.
by case (Adjacent_to_dec _ _) => H_dec.
Qed.

Definition adjacency (n : Name) (ns : list Name) : FinNS :=
fold_right (fun n' fs => FinNSet.add n' fs) FinNSet.empty (Adjacent_to_node n ns).

Lemma Adjacent_to_node_adjacency : forall n n' ns, In n' (Adjacent_to_node n ns) <-> FinNSet.In n' (adjacency n ns).
Proof.
move => n n' ns.
split.
  elim: ns => //=.
  move => n0 ns IH.
  rewrite /adjacency /= /is_left.
  case (Adjacent_to_dec _ _) => H_dec /= H_in; last exact: IH.
  case: H_in => H_in.
    rewrite H_in.
    apply FinNSet.add_spec.
    by left.
  apply FinNSet.add_spec.
  right.
  exact: IH.
elim: ns => //=; first by rewrite /adjacency /=; exact: FinNSet.empty_spec.
move => n0 ns IH.
rewrite /adjacency /=.
rewrite /is_left.
case (Adjacent_to_dec _ _) => H_dec /= H_ins; last exact: IH.
apply FinNSet.add_spec in H_ins.
case: H_ins => H_ins; first by left.
right.
exact: IH.
Qed.

Lemma not_adjacent_self : forall n ns, ~ FinNSet.In n (adjacency n ns).
Proof.
move => n ns H_ins.
apply Adjacent_to_node_adjacency in H_ins.
apply Adjacent_to_node_Adjacent_to in H_ins.
move: H_ins => [H_in H_adj].
contradict H_adj.
exact: Adjacent_to_irreflexive.
Qed.

Lemma adjacency_mutual_in : 
  forall n n' ns,
  In n' ns ->
  FinNSet.In n (adjacency n' ns) -> 
  FinNSet.In n' (adjacency n ns).
Proof.
move => n n' ns H_in H_ins.
apply Adjacent_to_node_adjacency.
apply Adjacent_to_node_adjacency in H_ins.
apply Adjacent_to_node_Adjacent_to in H_ins.
move: H_ins => [H_in' H_adj].
apply Adjacent_to_symmetric in H_adj.
exact: Adjacent_to_Adjacent_to_node.
Qed.

Lemma adjacency_mutual : forall (n n' : Name), FinNSet.In n (adjacency n' Nodes) -> FinNSet.In n' (adjacency n Nodes).
Proof.
move => n n' H_ins.
have H_in: In n' Nodes by exact: In_n_Nodes.
exact: adjacency_mutual_in.
Qed.

Definition fins_lt (fins fins' : FinNS) : Prop :=
FinNSet.cardinal fins < FinNSet.cardinal fins'.

Lemma fins_lt_well_founded : well_founded fins_lt.
Proof.
apply (well_founded_lt_compat _ (fun fins => FinNSet.cardinal fins)).
by move => x y; rewrite /fins_lt => H.
Qed.

Definition init_map_t (fins : FinNS) : Type := 
{ map : FinNM | forall (n : Name), FinNSet.In n fins <-> FinNMap.find n map = Some 1 }.

Definition init_map_F : forall fins : FinNS, 
  (forall fins' : FinNS, fins_lt fins' fins -> init_map_t fins') ->
  init_map_t fins.
rewrite /init_map_t.
refine
  (fun (fins : FinNS) init_map_rec =>
   match FinNSet.choose fins as finsopt return (_ = finsopt -> _) with
   | None => fun (H_eq : _) => exist _ (FinNMap.empty m) _
   | Some n => fun (H_eq : _) => 
     match init_map_rec (FinNSet.remove n fins) _ with 
     | exist fins' H_fins' => exist _ (FinNMap.add n 1 fins') _
     end
   end (refl_equal _)).
- rewrite /fins_lt /=.
  apply FinNSet.choose_spec1 in H_eq.
  set fn := FinNSet.remove _ _.
  have H_notin: ~ FinNSet.In n fn by move => H_in; apply FinNSetFacts.remove_1 in H_in.
  have H_add: FinNSetProps.Add n fn fins.
    rewrite /FinNSetProps.Add.
    move => k.
    split => H_in.
      case (Name_eq_dec n k) => H_eq'; first by left.
      by right; apply FinNSetFacts.remove_2.
    case: H_in => H_in; first by rewrite -H_in.
    by apply FinNSetFacts.remove_3 in H_in.
  have H_card := FinNSetProps.cardinal_2 H_notin H_add.
  rewrite H_card {H_notin H_add H_card}.
  by auto with arith.
- move => n'.
  apply FinNSet.choose_spec1 in H_eq.
  case (Name_eq_dec n n') => H_eq_n.
    rewrite -H_eq_n.
    split => //.
    move => H_ins.
    apply FinNMapFacts.find_mapsto_iff.
    exact: FinNMap.add_1.
  split => H_fins.
    apply FinNMapFacts.find_mapsto_iff.
    apply FinNMapFacts.add_neq_mapsto_iff => //.
    apply FinNMapFacts.find_mapsto_iff.    
    apply H_fins'.
    exact: FinNSetFacts.remove_2.
  apply FinNMapFacts.find_mapsto_iff in H_fins.
  apply FinNMapFacts.add_neq_mapsto_iff in H_fins => //.
  apply FinNMapFacts.find_mapsto_iff in H_fins.
  apply H_fins' in H_fins.
  by apply FinNSetFacts.remove_3 in H_fins.    
- move => n.
  apply FinNSet.choose_spec2 in H_eq.
  split => H_fin; first by contradict H_fin; auto with set.
  apply FinNMap.find_2 in H_fin.
  contradict H_fin.
  exact: FinNMap.empty_1.
Defined.

Definition init_map_str : forall (fins : FinNS), init_map_t fins :=
  @well_founded_induction_type
  FinNSet.t
  fins_lt
  fins_lt_well_founded
  init_map_t
  init_map_F.

Definition init_map (fins : FinNS) : FinNM := 
match init_map_str fins with
| exist map _ => map
end.
    
Definition init_Data (n : Name) := mkData 1 1 (adjacency n Nodes) (init_map (adjacency n Nodes)) (init_map (adjacency n Nodes)).

Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
match msg with
| Aggregate m_msg => 
  st <- get ;;
  (* when (FinNSet.mem src st.(adjacent)) *)
  (match FinNMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    let new_aggregate := st.(aggregate) * m_msg in
    let new_received := FinNMap.add src (m_src * m_msg) st.(received) in
    put (mkData st.(local) new_aggregate st.(adjacent) st.(sent) new_received)
  end)
| Fail => 
  st <- get ;;
  match FinNMap.find src st.(sent), FinNMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>
    let new_aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 in
    let new_adjacent := FinNSet.remove src st.(adjacent) in
    let new_sent := FinNMap.remove src st.(sent) in
    let new_received := FinNMap.remove src st.(received) in
    put (mkData st.(local) new_aggregate new_adjacent new_sent new_received)
  | _, _ => nop
  end
end.

Definition IOHandler (me : Name) (i : Input) : Handler Data :=
match i with
| Local m_msg => 
  st <- get ;;
  let new_local := m_msg in
  let new_aggregate := st.(aggregate) * m_msg * st.(local)^-1 in
  put (mkData new_local new_aggregate st.(adjacent) st.(sent) st.(received))
| SendAggregate dst => 
  st <- get ;;
  when (FinNSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match FinNMap.find dst st.(sent) with
   | None => nop
   | Some m_dst =>        
     let new_aggregate := 1 in
     let new_sent := FinNMap.add dst (m_dst * st.(aggregate)) st.(sent) in
     put (mkData st.(local) new_aggregate st.(adjacent) new_sent st.(received)) >> (send (dst, (Aggregate st.(aggregate))))
   end)
| Query =>
  st <- get ;;
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
    name := Name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := Name_eq_dec ;
    nodes := Nodes ;
    all_names_nodes := In_n_Nodes ;
    no_dup_nodes := nodup ;
    init_handlers := init_Data ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Check Build_OverlayFailParams.

Instance Aggregation_OverlayFailParams : OverlayFailParams Aggregation_MultiParams :=
  {
    adjacent_to := Adjacent_to ;
    adjacent_to_dec := Adjacent_to_dec ;
    adjacent_to_irreflexive := Adjacent_to_irreflexive ;
    adjacent_to_symmetric := Adjacent_to_symmetric ;
    fail := Fail
  }.

Definition sum_fold (fm : FinNM) (n : Name) (partial : m) : m :=
match FinNMap.find n fm with
| Some m' => partial * m'
| None => partial
end.

Definition sumM (fs : FinNS) (fm : FinNM) : m := 
FinNSet.fold (sum_fold fm) fs 1.

Lemma fold_left_right : forall (fm : FinNM) (l : list Name),
  fold_left (fun partial n => (sum_fold fm) n partial) l 1 = fold_right (sum_fold fm) 1 l.
Proof.
move => fm; elim => [|a l IH] //.
rewrite /= -IH /sum_fold {IH}.
case (FinNMap.find _ _) => [m6|] // {a}; gsimpl.
move: m6; elim: l => [m6|a l IH m6] => /=; first by gsimpl.
case (FinNMap.find _ _) => [m7|] //.
rewrite commutes IH; gsimpl.
by rewrite -IH.
Qed.

Corollary sumM_fold_right : forall (fs : FinNS) (fm : FinNM), 
  FinNSet.fold (sum_fold fm) fs 1 = fold_right (sum_fold fm) 1 (FinNSet.elements fs).
Proof. by move => fs fm; rewrite FinNSet.fold_spec fold_left_right. Qed.

Lemma not_in_add_eq : forall (l : list Name) (n : name) (fm : FinNM) (m5 : m),
  ~ InA eq n l -> 
  fold_right (sum_fold (FinNMap.add n m5 fm)) 1 l = fold_right (sum_fold fm) 1 l.
move => l n fm m5; elim: l => //.
move => a l IH H_in.
have H_in': ~ InA eq n l by move => H_neg; apply: H_in; apply InA_cons; right.
apply IH in H_in'.
rewrite /= H_in' /= /sum_fold.
have H_neq: n <> a by move => H_eq; apply: H_in; apply InA_cons; left.
case H_find: (FinNMap.find _ _) => [m6|].
  apply FinNMapFacts.find_mapsto_iff in H_find.  
  apply FinNMapFacts.add_neq_mapsto_iff in H_find => //.
  apply FinNMapFacts.find_mapsto_iff in H_find.
  case H_find': (FinNMap.find _ _) => [m7|]; last by rewrite H_find' in H_find.
  rewrite H_find in H_find'.
  injection H_find' => H_eq.
  by rewrite H_eq.
case H_find': (FinNMap.find _ _) => [m6|] => //.
apply FinNMapFacts.find_mapsto_iff in H_find'.
apply (FinNMapFacts.add_neq_mapsto_iff _ m5 _ H_neq) in H_find'.
apply FinNMapFacts.find_mapsto_iff in H_find'.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_add_map : forall (n : Name) (fs : FinNS) (fm : FinNM) (m5 m' : m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM fs (FinNMap.add n (m5 * m') fm) = sumM fs fm * m'.
Proof.
move => n fs fm m5 m' H_in H_find.
have H_in_el: InA eq n (FinNSet.elements fs) by apply FinNSetFacts.elements_2.
have H_nodup := FinNSet.elements_spec2w fs.
move: H_in_el H_nodup {H_in}.
rewrite 2!/sumM 2!sumM_fold_right.
elim (FinNSet.elements fs) => [|a l IH] H_in H_nodup; first by apply InA_nil in H_in.
case (Name_eq_dec n a) => H_dec.
  rewrite H_dec in H_find.
  rewrite H_dec /sum_fold /=.
  have H_find_eq := @FinNMapFacts.add_eq_o m fm a a (m5 * m') (refl_equal a).
  case H_find': (FinNMap.find _ _) => [m6|]; last by rewrite H_find_eq in H_find'.
  rewrite H_find_eq in H_find'.
  injection H_find' => H_eq.
  rewrite -H_eq.
  case H_find'': (FinNMap.find _ _) => [m7|]; last by rewrite H_find in H_find''.
  rewrite H_find'' in H_find.
  injection H_find => H_eq'.
  rewrite H_eq'; gsimpl.
  inversion H_nodup; subst.
  by rewrite not_in_add_eq.
apply InA_cons in H_in.
case: H_in => H_in //.
have H_nodup': NoDupA eq l by inversion H_nodup.
rewrite /= (IH H_in H_nodup') /sum_fold.
case H_find': (FinNMap.find _ _) => [m6|].
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  apply FinNMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply FinNMapFacts.find_mapsto_iff in H_find'.
  case H_find'': (FinNMap.find _ _) => [m7|]; last by rewrite H_find'' in H_find'.
  rewrite H_find' in H_find''.
  injection H_find'' => H_eq.
  rewrite H_eq.
  by aac_reflexivity.
case H_find'': (FinNMap.find _ _) => [m7|] //.
apply FinNMapFacts.find_mapsto_iff in H_find''.
apply (FinNMapFacts.add_neq_mapsto_iff _ (m5 * m') _ H_dec) in H_find''.
apply FinNMapFacts.find_mapsto_iff in H_find''.
by rewrite H_find' in H_find''.
Qed.

Lemma eqlistA_eq : forall (l l' : list Name), eqlistA eq l l' -> l = l'.
Proof.
elim; first by move => l' H_eql; inversion H_eql.
move => a l IH.
case => [|a' l'] H; first by inversion H.
inversion H; subst.
by rewrite (IH l').
Qed.

Lemma sumM_remove : forall (fs : FinNS) (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) fm = sumM fs fm * m5^-1.
Proof.
move => I_ind.
pose P_ind (fs : FinNS) := forall (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) fm = sumM fs fm * m5^-1.
rewrite -/(P_ind I_ind).
apply (FinNSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty n fm m5 H_in.
  have H_empty' := FinNSet.empty_spec.
  by contradict H_in; apply H_empty.
rewrite /sumM.
move => fs I' IH a H_below H_add n fm m5 H_in H_map.
have H_eql := FinNSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite 2!sumM_fold_right.
case (Name_eq_dec a n) => H_eq.
  move: H_in H_map; rewrite -H_eq H_eql {H_eq} => H_in H_map.
  rewrite /FinNSetOrdProps.P.Add in H_add.
  have H_rem := FinNSet.remove_spec I' a.
  have H_below': FinNSetOrdProps.Below a (FinNSet.remove a I').
    rewrite /FinNSetOrdProps.Below => a' H_in'.
    apply FinNSet.remove_spec in H_in'.
    case: H_in' => H_in' H_neq.
    apply H_below.
    apply H_add in H_in'.
    by case: H_in' => H_in'; first by case H_neq.
  have H_add' := FinNSetProps.Add_remove H_in.
  have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
  apply eqlistA_eq in H_eql'.
  rewrite H_eql {H_eql} in H_eql'.
  set el_rm := FinNSet.elements _.
  have {H_eql'} ->: el_rm = FinNSet.elements fs by injection H_eql'.
  rewrite {2}/fold_right {2}/sum_fold {el_rm}.
  case H_find: (FinNMap.find _ _) => [m6|]; last by rewrite H_map in H_find.
  rewrite H_map in H_find.
  have ->: m6 = m5 by injection H_find.
  by gsimpl.
rewrite H_eql.
have H_in': FinNSet.In n fs.
  apply H_add in H_in.
  by case: H_in.
have H_below': FinNSetOrdProps.Below a (FinNSet.remove n fs).
  rewrite /FinNSetOrdProps.Below => a' H_inr.
  apply H_below.
  have H_rm := FinNSet.remove_spec fs n a'.
  apply H_rm in H_inr.
  by case: H_inr.
have H_add': FinNSetOrdProps.P.Add a (FinNSet.remove n fs) (FinNSet.remove n I').
  rewrite /FinNSetOrdProps.P.Add => a'.
  have H_add_a' := H_add a'.
  case (Name_eq_dec a a') => H_eq'.
    split => H_imp; first by left.
    have H_or: a = a' \/ FinNSet.In a' fs by left.
    apply H_add_a' in H_or.
    apply FinNSet.remove_spec; split => //.
    by rewrite -H_eq'.
  split => H_imp.    
    right.
    apply FinNSet.remove_spec in H_imp.
    case: H_imp => H_imp H_neq.
    apply FinNSet.remove_spec; split => //.
    apply H_add_a' in H_imp.
    by case: H_imp.
  case: H_imp => H_imp //.
  apply FinNSet.remove_spec in H_imp.
  case: H_imp => H_imp H_neq.
  have H_or: a = a' \/ FinNSet.In a' fs by right.
  apply H_add_a' in H_or.
  by apply FinNSet.remove_spec; split.
have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /fold_right /sum_fold.      
case H_find: (FinNMap.find a fm) => [m6|].
  have H_eq' := IH n fm m5 H_in' H_map.
  rewrite 2!sumM_fold_right /fold_right in H_eq'.
  rewrite H_eq' /sum_fold.
  by aac_reflexivity.
have H_eq' := IH n fm m5 H_in' H_map.
rewrite 2!sumM_fold_right in H_eq'.
rewrite /fold_right in H_eq'.
by rewrite H_eq' /sum_fold.
Qed.

Lemma sumM_notins_remove_map : forall (fs : FinNS) (n : Name) (fm : FinNM),
  ~ FinNSet.In n fs ->
  sumM fs (FinNMap.remove n fm) = sumM fs fm.
Proof.
move => fs n fm H_ins.
have H_notin: ~ InA eq n (FinNSet.elements fs).
  move => H_ina.
  by apply FinNSetFacts.elements_2 in H_ina.
rewrite 2!/sumM 2!sumM_fold_right.
move: H_notin.
elim (FinNSet.elements fs) => [|a l IH] H_in //.
have H_in': ~ InA eq n l.
  move => H_in'.
  contradict H_in.
  by right.
have H_neq: n <> a.
  move => H_eq.
  contradict H_in.
  by left.
have IH' := IH H_in'.
move: IH'.
rewrite /fold_right /sum_fold => IH'.
case H_find: (FinNMap.find _ _) => [m5|].
  case H_find': (FinNMap.find _ _) => [m6|]; rewrite FinNMapFacts.remove_neq_o in H_find => //.
    rewrite H_find in H_find'.
    injection H_find' => H_eq.
    rewrite H_eq.
    by rewrite IH'.
  by rewrite H_find in H_find'.
rewrite FinNMapFacts.remove_neq_o in H_find => //.
case H_find': (FinNMap.find _ _) => [m5|] //.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_remove_remove : forall (fs : FinNS) (n : Name) (fm : FinNM) (m5: m),
  FinNSet.In n fs ->
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.remove n fs) (FinNMap.remove n fm) = sumM fs fm * m5^-1.
Proof.
move => fs n fm m5 H_ins H_find.
have H_ins': ~ FinNSet.In n (FinNSet.remove n fs) by move => H_ins'; apply FinNSetFacts.remove_1 in H_ins'.
rewrite sumM_notins_remove_map => //.
exact: sumM_remove.
Qed.

Lemma sumM_empty : forall (fs : FinNS) (fm : FinNM), FinNSet.Empty fs -> sumM fs fm = 1.
Proof.
move => fs fm.
rewrite /FinNSet.Empty => H_empty.
have H_elts: forall (n : Name), ~ InA eq n (FinNSet.elements fs).
  move => n H_notin.
  apply FinNSetFacts.elements_2 in H_notin.
  by apply (H_empty n).
rewrite /sumM sumM_fold_right.
case H_elt: (FinNSet.elements fs) => [|a l] //.
have H_in: InA eq a (FinNSet.elements fs) by rewrite H_elt; apply InA_cons; left.
by contradict H_in; apply (H_elts a).
Qed.

Lemma sumM_eq : forall (fs : FinNS) (fm' : FinNS) (fm : FinNM),
   FinNSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
Proof.
move => I_ind.
pose P_ind (fs : FinNS) := forall (fm' : FinNS) (fm : FinNM),
   FinNSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
rewrite -/(P_ind I_ind).
apply (FinNSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty fm' fm H_eq.
  have H_empty': FinNSet.Empty fm'.
    rewrite /FinNSet.Empty => a H_in.
    apply H_eq in H_in.
    by apply H_empty in H_in.    
  rewrite sumM_empty //.
  by rewrite sumM_empty.
move => fs fm' IH a H_below H_add fm'' fm H_eq.
have H_eql := FinNSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite /sumM 2!sumM_fold_right H_eql.
have H_below': FinNSetOrdProps.Below a (FinNSet.remove a fm'').
  rewrite /FinNSetOrdProps.Below => a' H_in.
  apply H_below.
  apply (FinNSet.remove_spec) in H_in.
  case: H_in => H_in H_neq.    
  apply H_eq in H_in.
  apply H_add in H_in.
  by case: H_in => H_in; first by case H_neq.
have H_add': FinNSetOrdProps.P.Add a (FinNSet.remove a fm'') fm''.
  rewrite /FinNSetOrdProps.P.Add => a'.
  case (Name_eq_dec a a') => H_eq_a.
    split => H_imp; first by left.
    apply H_eq.
    rewrite -H_eq_a.
    by apply H_add; left.
  split => H_imp; first by right; apply FinNSet.remove_spec; split; last by contradict H_eq_a.
  case: H_imp => H_imp; first by case H_eq_a.
  by apply FinNSet.remove_spec in H_imp; case: H_imp.
have H_eq': FinNSet.Equal fs (FinNSet.remove a fm'').
   rewrite /FinNSet.Equal => a'.
   case (Name_eq_dec a a') => H_eq_a.
     have H_or: a = a' \/ FinNSet.In a' fs by left.
     apply H_add in H_or.
     split => H_imp.
       apply FinNSet.remove_spec.
       rewrite -H_eq_a in H_or H_imp.
       apply H_below in H_imp.
       by contradict H_imp.
     rewrite H_eq_a in H_imp.
     apply FinNSet.remove_spec in H_imp.
     by case: H_imp.
   split => H_imp.
     apply FinNSet.remove_spec; split; last by contradict H_eq_a.
     apply H_eq.
     by apply H_add; right.
   apply FinNSet.remove_spec in H_imp.
   case: H_imp => H_imp H_neq.
   apply H_eq in H_imp.
   apply H_add in H_imp.
   by case: H_imp.
have H_eql' := FinNSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /sum_fold /fold_right.
have IH' := IH (FinNSet.remove a fm'') fm.
rewrite /sumM 2!sumM_fold_right /fold_right in IH'.
by case H_find: (FinNMap.find _ _) => [m5|]; rewrite IH'.
Qed.

Corollary sumM_add : forall (fs : FinNS) (fm : FinNM) (m5 : m) (n : Name),
  ~ FinNSet.In n fs -> 
  FinNMap.find n fm = Some m5 ->
  sumM (FinNSet.add n fs) fm = sumM fs fm * m5.
Proof.
move => fs fm m5 n H_notin H_map.
have H_in: FinNSet.In n (FinNSet.add n fs) by apply FinNSet.add_spec; left.
have H_rm := @sumM_remove (FinNSet.add n fs) _ _ _ H_in H_map.
set srm := sumM _ _ in H_rm.
set sadd := sumM _ _ in H_rm *.
have <-: srm * m5 = sadd by rewrite H_rm; gsimpl.
suff H_eq: srm = sumM fs fm by rewrite H_eq; aac_reflexivity.
apply sumM_eq.
exact: (FinNSetProps.remove_add H_notin).
Qed.

Lemma sumM_add_add : forall (fs : FinNS) (M5 : FinNM) (m5 : m) (n : Name),
  ~ FinNSet.In n fs -> 
  sumM (FinNSet.add n fs) (FinNMap.add n m5 M5) = sumM fs M5 * m5.
Proof.
move => fs M5 m5 n H_in.
have H_find := @FinNMapFacts.add_eq_o _ M5 _ _ m5 (refl_equal n).
rewrite (@sumM_add _ _ _ _ H_in H_find) {H_find}.
set sadd := sumM _ _.
suff H_suff: sadd = sumM fs M5 by rewrite H_suff.
rewrite /sadd /sumM 2!sumM_fold_right {sadd}.
have H_in_el: ~ InA eq n (FinNSet.elements fs) by move => H_neg; apply FinNSetFacts.elements_2 in H_neg.
by move: H_in_el; apply not_in_add_eq.
Qed.

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
      (exists dst m', i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = FinNMap.add dst (m' * st.(aggregate)) st.(sent) /\
         st'.(received) = st.(received) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = None /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) = 1 /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = SendAggregate dst /\ ~ FinNSet.In dst st.(adjacent) /\ 
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
- case H_mem: (FinNSet.mem _ _); case (m_eq_dec _ _) => H_dec; rewrite /sumbool_not //=.
  * apply FinNSetFacts.mem_2 in H_mem.
    move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left; exists dst.
  * apply FinNSetFacts.mem_2 in H_mem.
    case H_find: (FinNMap.find _ _) => [m'|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    + by right; left; exists dst; exists m'.
    + by right; right; left; exists dst.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply FinNSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
  * move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; right; right; left.
    exists dst.
    split => //.
    split => //.
    move => H_ins.
    apply FinNSetFacts.mem_1 in H_ins.
    by rewrite H_mem in H_ins.
- move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
  by right; right; right; right; right.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ FinNMap.find src st.(received) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\     
     st'.(received) = FinNMap.add src (m_src * m_msg) st.(received) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ FinNMap.find src st.(received) = None /\ 
     st' = st /\ out = [] /\ ms = []) \/
    (exists m_snt m_rcd, msg = Fail /\ FinNMap.find src st.(sent) = Some m_snt /\ FinNMap.find src st.(received) = Some m_rcd /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = FinNMap.remove src st.(sent) /\
     st'.(received) = FinNMap.remove src st.(received) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (FinNMap.find src st.(sent) = None \/ FinNMap.find src st.(received) = None) /\
     st' = st /\ out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => [m_msg|]; monad_unfold.
  case H_find: (FinNMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=; first by left; exists m_msg; exists  m_src.
  by right; left; exists m_msg.
case H_find: (FinNMap.find _ _) => [m_snt|]; case H_find': (FinNMap.find _ _) => [m_rcd|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
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

Lemma Aggregation_node_not_adjacent_self : 
forall net failed tr n, 
 step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, net) tr ->
 ~ In n failed ->
 ~ FinNSet.In n (onwState net n).(adjacent).
Proof.
move => net failed tr n H.
remember step_o_f_init as y in *.
have ->: failed = fst (failed, net) by [].
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_o_f_init /=.
  move => H_f.
  exact: not_adjacent_self.
move => H_f.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; rewrite /=.
- find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec /=; last exact: IHrefl_trans_1n_trace1.
  rewrite -H_dec in H3.
  net_handler_cases => //.
  apply FinNSet.remove_spec in H0.
  by move: H0 => [H0 H_neq].
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec; last exact: IHrefl_trans_1n_trace1.
  rewrite -H_dec in H2.
  find_apply_lem_hyp input_handlers_IOHandler.
  by io_handler_cases.
- exact: IHrefl_trans_1n_trace1.
Qed.

Section SingleNodeInv.

Variable onet : ordered_network.

Variable failed : list name.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, onet) tr.

Variable n : Name.

Hypothesis not_failed : ~ In n failed.

Variable P : Data -> Prop.

Hypothesis after_init : P (init_Data n).

Hypothesis recv_aggregate : 
  forall onet failed tr n' m' m0,
    step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNMap.find n' (onet.(onwState) n).(received) = Some m0 ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add n' (m0 * m') (onet.(onwState) n).(received))).

Hypothesis recv_fail : 
  forall onet failed tr n' m_snt m_rcd,
    step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNMap.find n' (onet.(onwState) n).(sent) = Some m_snt ->
    FinNMap.find n' (onet.(onwState) n).(received) = Some m_rcd ->
    P (onet.(onwState) n) ->
    P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m_snt * (m_rcd)^-1) (FinNSet.remove n' (onet.(onwState) n).(adjacent)) (FinNMap.remove n' (onet.(onwState) n).(sent)) (FinNMap.remove n' (onet.(onwState) n).(received))).

Hypothesis recv_local_weight : 
  forall onet failed tr m',
  step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, onet) tr ->
  ~ In n failed ->
  P (onet.(onwState) n) ->
  P (mkData m' ((onwState onet n).(aggregate) * m' * ((onwState onet n).(local))^-1) (onwState onet n).(adjacent) (onwState onet n).(sent) (onwState onet n).(received)).

Hypothesis recv_send_aggregate : 
  forall onet failed tr n' m',
    step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, onet) tr ->
    ~ In n failed ->
    FinNSet.In n' (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    FinNMap.find n' (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add n' (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)).

Theorem P_inv_n : P (onwState onet n).
Proof.
move: onet tr H_step.
clear onet tr H_step.
move => onet' tr' H'_step.
have ->: onet' = snd (failed, onet') by [].
remember step_o_f_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_o_init /=.
  exact: after_init.
concludes.
match goal with
| [ H : step_o_f _ _ _ |- _ ] => invc H
end; simpl.
- find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2 to} in H0, H1, H2.
  net_handler_cases => //.
    case: d H3 H4 H5 H6 H7 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6 H7.
    rewrite H3 H4 H5 H6 H7 {local0 aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6 H7}.
    exact: (recv_aggregate _ _ H'_step1).
  case: d H4 H5 H6 H7 H8 => /=.
  move => local0 aggregate0 adjacent0 sent0 receive0.
  move => H4 H5 H6 H7 H8.
  rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
  exact: (recv_fail _ H'_step1).
- find_apply_lem_hyp input_handlers_IOHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec; last exact: IHH'_step1.
  rewrite -H_dec {H_dec H'_step2} in H0 H1.
  io_handler_cases => //.
  * case: d H2 H3 H4 H5 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H2 H3 H4 H5.
    rewrite H2 H3 H4 H5 {aggregate0 adjacent0 sent0 receive0 H2 H3 H4 H5}.
    exact: (recv_local_weight _ H'_step1).
  * case: d H4 H5 H6 H7 H8 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H4 H5 H6 H7 H8.
    rewrite H4 H5 H6 H7 H8 {local0 aggregate0 adjacent0 sent0 receive0 H4 H5 H6 H7 H8}.
    exact: (recv_send_aggregate H'_step1).
  * by rewrite /= in IHH'_step1.
Qed.

End SingleNodeInv.

Definition in_set_exists_find_sent (n : Name) (d : Data) : Prop :=
  FinNSet.In n d.(adjacent) -> exists m5 : m, FinNMap.find n d.(sent) = Some m5.

Lemma Aggregation_in_set_exists_find_sent : 
forall net failed tr, 
 step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, net) tr ->
 forall n n', 
    ~ In n failed ->
   in_set_exists_find_sent n' (net.(onwState) n).
Proof.
move => net failed tr H_st.
move => n n0 H_f.
pose P_curr (d : Data) := in_set_exists_find_sent n0 d.
rewrite -/(P_curr _).
apply: (P_inv_n H_st); rewrite /P_curr /in_set_exists_find_sent //= {P_curr net tr H_st failed H_f}.
- move => H_ins.
  exists 1.
  rewrite /init_map.
  case (init_map_str _) => fm H_init.
  by apply H_init in H_ins.
- move => onet failed tr n1 m_snt m_rcd H_step H_f H_find H_find' IH H_ins.
  apply FinNSet.remove_spec in H_ins.
  move: H_ins => [H_ins H_neq]. 
  apply IH in H_ins.
  move: H_ins => [m' H_find''].
  exists m'.  
  apply FinNMapFacts.find_mapsto_iff.
  apply FinNMapFacts.remove_neq_mapsto_iff; first by move => H_neq'; rewrite H_neq' in H_neq.
  by apply FinNMapFacts.find_mapsto_iff.
- move => onet failed tr n1 m' H_step H_f H_ins H_neq H_find IH H_ins'.
  apply IH in H_ins'.
  move: H_ins' => [m0 H_find'].
  case (Name_eq_dec n1 n0) => H_dec.
    rewrite H_dec.
    exists (m' * (onwState onet n).(aggregate)).
    exact: FinNMapFacts.add_eq_o.
  exists m0.
  apply FinNMapFacts.find_mapsto_iff.
  apply FinNMapFacts.add_neq_mapsto_iff => //.
  by apply FinNMapFacts.find_mapsto_iff.
Qed.

Definition in_set_exists_find_received (n : Name) (d : Data) : Prop :=
  FinNSet.In n d.(adjacent) -> exists m5 : m, FinNMap.find n d.(received) = Some m5.

Lemma Aggregation_in_set_exists_find_received : 
forall net failed tr, 
 step_o_f_star (params := Aggregation_OverlayFailParams) step_o_f_init (failed, net) tr -> 
 forall n n', 
   ~ In n failed ->
   in_set_exists_find_received n' (net.(onwState) n).
Proof.
move => net failed tr H_st.
move => n n0 H_f.
pose P_curr (d : Data) := in_set_exists_find_received n0 d.
rewrite -/(P_curr _).
apply: (P_inv_n H_st); rewrite /P_curr /in_set_exists_find_received //= {P_curr net tr H_st failed H_f}.
- move => H_ins.
  exists 1.
  rewrite /init_map.
  case (init_map_str _) => fm H_init.
  by apply H_init in H_ins.
- move => onet failed tr n' m' m0 H_step H_f H_find IH H_ins'.
  apply IH in H_ins'.
  move: H_ins' => [m1 H_find'].
  case (Name_eq_dec n' n0) => H_dec.
    rewrite H_dec.
    exists (m0 * m').
    exact: FinNMapFacts.add_eq_o.
  exists m1.
  apply FinNMapFacts.find_mapsto_iff.
  apply FinNMapFacts.add_neq_mapsto_iff => //.
  by apply FinNMapFacts.find_mapsto_iff.
- move => onet failed tr n1 m_snt m_rcd H_step H_f H_find H_find' IH H_ins.
  apply FinNSet.remove_spec in H_ins.
  move: H_ins => [H_ins H_neq]. 
  apply IH in H_ins.
  move: H_ins => [m' H_find''].
  exists m'.  
  apply FinNMapFacts.find_mapsto_iff.
  apply FinNMapFacts.remove_neq_mapsto_iff; first by move => H_neq'; rewrite H_neq' in H_neq.
  by apply FinNMapFacts.find_mapsto_iff.
Qed.

(* ---------------------------------- *)

(* prove that self-channel is empty *)

Definition self_channel_empty (net : ordered_network) : Prop :=
forall n, net.(onwPackets) n n = [].

Lemma Aggregation_self_channel_empty : 
forall net tr, 
 step_o_star (params := Aggregation_MultiParams) step_o_init net tr ->
 self_channel_empty net.
Proof.
move => onet tr H_step.
remember step_o_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init; rewrite /self_channel_empty /=; first by rewrite H_init /step_o_init.
rewrite /self_channel_empty in IHH_step1.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
    rewrite /update /= /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move: H_dec => [H_dec H_dec'].
    rewrite H_dec H_dec' in H0.
    by rewrite IHH_step1 in H0.
  rewrite /collate /= /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec //.
  move: H_dec => [H_dec H_dec'].
  rewrite H_dec H_dec' in H0.
  by rewrite IHH_step1 in H0.
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases; rewrite /collate /= //.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_dec H_dec'].
rewrite H_dec' H_dec in H.
by have H_not := Aggregation_node_not_adjacent_self H_step1 H.
Qed.

Lemma Aggregation_nodes_mutually_adjacent : 
forall net tr n n', 
 step_o_star (params := Aggregation_MultiParams) step_o_init net tr ->
 FinNSet.In n (onwState net n').(adjacent) -> FinNSet.In n' (onwState net n).(adjacent).
Proof.
move => net tr n n' H.
remember step_o_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_o_init /=.
  exact: adjacency_mutual.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_eq; case (Name_eq_dec _ _) => H_eq' //=; first by net_handler_cases.
    by net_handler_cases; exact: IHrefl_trans_1n_trace1.
  by net_handler_cases.
find_apply_lem_hyp input_handlers_IOHandler.
rewrite /update /=.
case (Name_eq_dec _ _) => H_eq; case (Name_eq_dec _ _) => H_eq' //=; first by io_handler_cases.
  by io_handler_cases; exact: IHrefl_trans_1n_trace1.
by io_handler_cases.
Qed.

Section SingleNodeInvOut.

Variable onet : ordered_network.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_star (params := Aggregation_MultiParams) step_o_init onet tr.

Variables n n' : Name.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

Hypothesis recv_aggregate_neq_from :
  forall onet tr from m' m0 ms,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  from <> n ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq :
  forall onet tr from m' m0 ms,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  n <> n' ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) from n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n n') ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n n').

Hypothesis recv_aggregate_neq_other_some :
  forall onet tr m' m0 ms,
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    n <> n' ->
    FinNMap.find n (received (onet.(onwState) n')) = Some m0 ->
    onet.(onwPackets) n n' = Aggregate m' :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (onet.(onwState) n) ms.

(* cannot happen *)
Hypothesis recv_aggregate_neq_other_none :
  forall onet tr m' ms,
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    n <> n' ->
    FinNMap.find n (received (onet.(onwState) n')) = None ->
    onet.(onwPackets) n n' = Aggregate m' :: ms ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (onet.(onwState) n) ms.

Hypothesis recv_local : 
  forall onet tr m_local,
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    P (onet.(onwState) n) (onet.(onwPackets) n n') ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

Hypothesis recv_local_eq_some :
  forall onet tr m',
      step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      FinNSet.In n' (onet.(onwState) n).(adjacent) ->
      FinNMap.find n' (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (FinNMap.add n' (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n' ++ [Aggregate (onet.(onwState) n).(aggregate)]).

Hypothesis recv_local_neq_some :
  forall onet tr to m',
      step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
      (onet.(onwState) n).(aggregate) <> 1 ->
      FinNSet.In to (onet.(onwState) n).(adjacent) ->
      FinNMap.find to (onet.(onwState) n).(sent) = Some m' ->
      P (onet.(onwState) n) (onet.(onwPackets) n n') ->
      P (mkData (onet.(onwState) n).(local) 1 (onet.(onwState) n).(adjacent) (FinNMap.add to (m' * (onet.(onwState) n).(aggregate)) (onet.(onwState) n).(sent)) (onet.(onwState) n).(received)) (onet.(onwPackets) n n').

Theorem P_inv_n_out : P (onet.(onwState) n) (onet.(onwPackets) n n').
Proof.
move: onet tr H_step.
clear onet tr H_step.
move => onet' tr' H'_step.
remember step_o_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_o_init /=.
  exact: after_init.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H2 H3 H4 H5 H6 H0.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H6 H0. 
        by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
      case: H_dec => H_dec.
        case: d H2 H3 H4 H5 H6 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H2 H3 H4 H5 H6.
        rewrite H2 H3 H4 H5 H6 {local0 aggregate0 adjacent0 sent0 receive0 H2 H3 H4 H5 H6}.
        exact: (recv_aggregate_neq_from H'_step1 H_dec H H0).
      case: d H2 H3 H4 H5 H6 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H2 H3 H4 H5 H6.
      rewrite H2 H3 H4 H5 H6 {local0 aggregate0 adjacent0 sent0 receive0 H2 H3 H4 H5 H6}.
      exact: (recv_aggregate_neq _ H'_step1 H_dec H H0).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite H_dec'' in H_dec.
    rewrite H_dec' {from H_dec' H'_step2} in H H6 H0.
    rewrite H_dec'' {H_dec'' to} in H H2 H3 H4 H5 H6 H0.
    exact: (recv_aggregate_neq_other_some H'_step1 H_dec H H0).
  rewrite /update.
  case (Name_eq_dec _ _) => H_dec.
    rewrite -H_dec in H H0.
    rewrite -H_dec.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    rewrite -H_dec'' in IHH'_step1.
    rewrite H_dec' in H H0.
    by rewrite (Aggregation_self_channel_empty H'_step1) in H0.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_dec' H_dec''].
  rewrite H_dec'' {H'_step2 to H_dec''} in H_dec H H0.
  rewrite H_dec' {H_dec' from} in H H0.
  exact: (recv_aggregate_neq_other_none H'_step1 H_dec H H0).
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases => //.
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec {h H_dec H'_step2} in H2 H3 H4 H1.
  case: d H1 H2 H3 H4 => /=.
  move => local0 aggregate0 adjacent0 sent0 receive0.
  move => H1 H2 H3 H4.
  rewrite H1 H2 H3 H4 {aggregate0 adjacent0 sent0 receive0 H1 H2 H3 H4}.
  exact: (recv_local _ H'_step1).
- rewrite /update /= /update2.
  case (Name_eq_dec _ _) => H_dec.
    rewrite -H_dec.
    rewrite -H_dec {h H_dec H'_step2} in H H1 H2 H3 H5 H6 H7.
    case (sumbool_and _ _ _ _) => H_dec'.
      move: H_dec' => [H_dec' H_dec''].
      rewrite H_dec''.
      rewrite H_dec'' {x H_dec'' H_dec'} in H H2 H6.
      case: d H4 H3 H5 H7 H6 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H4 H3 H5 H7 H6.
      rewrite H4 H3 H5 H7 H6 {local0 aggregate0 adjacent0 sent0 receive0 H4 H3 H5 H7 H6}.
      exact: (recv_local_eq_some H'_step1 H1 H H2).
    case: H_dec' => H_dec' //.
    case: d H4 H3 H5 H7 H6 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H4 H3 H5 H7 H6.
    rewrite H4 H3 H5 H7 H6 {local0 aggregate0 adjacent0 sent0 receive0 H4 H3 H5 H7 H6}.
    exact: (recv_local_neq_some H'_step1 H1 H H2).
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_dec' H_dec''].
  by rewrite H_dec' in H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
Qed.

End SingleNodeInvOut.

Definition aggregate_msg_adjacent (n : Name) (d : Data) (l : list msg) : Prop :=
  forall m_msg, In (Aggregate m_msg) l ->
  FinNSet.In n d.(adjacent).

Lemma Aggregation_aggregate_msg_dst_adjacent_src : 
forall net tr, 
 step_o_star (params := Aggregation_MultiParams) step_o_init net tr ->
 forall n n', aggregate_msg_adjacent n' (net.(onwState) n) (net.(onwPackets) n n').
Proof.
move => net tr H_st.
move => n n'.
pose P_curr (d : Data) (l : list msg) := aggregate_msg_adjacent n' d l.
rewrite -/(P_curr _ _).
apply: (P_inv_n_out H_st); rewrite /P_curr /aggregate_msg_adjacent //= {P_curr net tr H_st}.
  move => onet tr m' m0 ms H_step H_neq H_find H_eq IH.
  move => m_msg H_in.
  rewrite H_eq in IH.
  apply: (IH m_msg).
  by right.
move => onet tr m' ms H_step H_neq H_find H_eq IH m_msg H_in.
apply: (IH m_msg).
rewrite H_eq.
by right.
Qed.

Section SingleNodeInvIn.

Variable onet : ordered_network.

Variable tr : list (name * (input + list output)).

Hypothesis H_step : step_o_star (params := Aggregation_MultiParams) step_o_init onet tr.

Variables n n' : Name.

Variable P : Data -> list msg -> Prop.

Hypothesis after_init : P (init_Data n) [].

Hypothesis recv_aggregate : 
  forall onet tr m' m0 ms,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  FinNMap.find n' (onwState onet n).(received) = Some m0 ->
  onet.(onwPackets) n' n = Aggregate m' :: ms ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add n' (m0 * m') (onet.(onwState) n).(received))) ms.

Hypothesis recv_aggregate_other : 
  forall onet tr m' from m0,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  from <> n' ->
  FinNMap.find from (onwState onet n).(received) = Some m0 ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (mkData (onet.(onwState) n).(local) ((onet.(onwState) n).(aggregate) * m') (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (FinNMap.add from (m0 * m') (onet.(onwState) n).(received))) (onet.(onwPackets) n' n).

Hypothesis recv_local : 
  forall onet tr m_local,
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData m_local ((onet.(onwState) n).(aggregate) * m_local * (onet.(onwState) n).(local)^-1) (onet.(onwState) n).(adjacent) (onet.(onwState) n).(sent) (onet.(onwState) n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate : 
  forall onet tr n0 m',
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    n <> n' ->
    FinNSet.In n0 (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    FinNMap.find n0 (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add n0 (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_other : 
  forall onet tr n0 m',
    step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
    n0 <> n ->
    FinNSet.In n0 (onwState onet n).(adjacent) ->
    (onwState onet n).(aggregate) <> 1 ->
    FinNMap.find n0 (onwState onet n).(sent) = Some m' ->
    P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
    P (mkData (onwState onet n).(local) 1 (onwState onet n).(adjacent) (FinNMap.add n0 (m' * (onwState onet n).(aggregate)) (onwState onet n).(sent)) (onwState onet n).(received)) (onet.(onwPackets) n' n).

Hypothesis recv_send_aggregate_neq :
  forall onet tr,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  n <> n' ->
  (onet.(onwState) n').(aggregate) <> 1 ->
  FinNSet.In n (onet.(onwState) n').(adjacent) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n) ->
  P (onet.(onwState) n) (onet.(onwPackets) n' n ++ [Aggregate (onet.(onwState) n').(aggregate)]).

Theorem P_inv_n_in : P (onet.(onwState) n) (onet.(onwPackets) n' n).
Proof.
move: onet tr H_step.
clear onet tr H_step.
move => onet' tr' H'_step.
remember step_o_init as y in H'_step.
move: Heqy.
induction H'_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_o_init /=.
  exact: after_init.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec.
      rewrite -H_dec in H H2 H3 H4 H5 H6 H0.
      rewrite -H_dec /update2 /= {H_dec to H'_step2}.
      case (sumbool_and _ _ _ _) => H_dec.
        move: H_dec => [H_eq H_eq'].
        rewrite H_eq {H_eq from} in H H6 H0.
        case: d H2 H3 H4 H5 H6 => /=.
        move => local0 aggregate0 adjacent0 sent0 receive0.
        move => H2 H3 H4 H5 H6.
        rewrite H2 H3 H4 H5 H6 {local0 aggregate0 adjacent0 sent0 receive0 H2 H3 H4 H5 H6}.
        exact: (recv_aggregate H'_step1 H H0).
      case: H_dec => H_dec //.
      case: d H2 H3 H4 H5 H6 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H2 H3 H4 H5 H6.
      rewrite H2 H3 H4 H5 H6 {local0 aggregate0 adjacent0 sent0 receive0 H2 H3 H4 H5 H6}.
      exact: (recv_aggregate_other _ H'_step1).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_dec''].
    by rewrite H_dec'' in H_dec.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec.
    rewrite -H_dec.
    rewrite -H_dec in H H0.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec' //.
    move: H_dec' => [H_dec' H_eq].
    rewrite H_dec' in H0 H.
    have H_in: In (Aggregate x) (x'.(onwPackets) n' n) by rewrite H0; left.
    have H_adj := Aggregation_aggregate_msg_dst_adjacent_src H'_step1 n' n _ H_in.
    have H_mut := Aggregation_nodes_mutually_adjacent _ H'_step1 H_adj.
    have [m0 H_find'] := Aggregation_in_set_exists_find_received H'_step1 _ H_mut.
    by rewrite H_find' in H.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_dec' H_eq].
  by rewrite H_eq in H_dec.
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases => //.
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec {h H_dec H'_step2} in H2 H3 H4 H1.
  case: d H1 H2 H3 H4 => /=.
  move => local0 aggregate0 adjacent0 sent0 receive0.
  move => H1 H2 H3 H4.
  rewrite H1 H2 H3 H4 {aggregate0 adjacent0 sent0 receive0 H1 H2 H3 H4}.
  exact: (recv_local _ H'_step1).
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec'.
      move: H_dec' => [H_dec' H_eq].
      rewrite H_eq -H_dec in H.
      contradict H.
      exact: (Aggregation_node_not_adjacent_self H'_step1).
    case: H_dec' => H_dec'.
      rewrite -H_dec in H_dec'.
      rewrite -H_dec {H_dec h H'_step2} in H H1 H2 H3 H5 H6 H7.
      case: d H3 H4 H5 H6 H7 => /=.
      move => local0 aggregate0 adjacent0 sent0 receive0.
      move => H3 H4 H5 H6 H7.
      rewrite H3 H4 H5 H6 H7 {local0 aggregate0 adjacent0 sent0 receive0 H3 H4 H5 H6 H7}.
      exact: (recv_send_aggregate H'_step1).
    rewrite -H_dec {H_dec h H'_step2} in H H1 H2 H3 H5 H6 H7.
    case: d H3 H4 H5 H6 H7 => /=.
    move => local0 aggregate0 adjacent0 sent0 receive0.
    move => H3 H4 H5 H6 H7.
    rewrite H3 H4 H5 H6 H7 {H3 H4 H5 H6 H7}.
    exact: (recv_send_aggregate_other H'_step1).
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec' => [H_dec' H_dec''].
  rewrite H_dec' in H_dec H H1 H2 H3 H5 H6 H7.
  rewrite H_dec' {H'_step2 H_dec' h}.
  rewrite H_dec'' in H H2 H6.
  rewrite H_dec'' {H_dec'' x}.
  exact: (recv_send_aggregate_neq H'_step1).
- have [m' H_sent] := Aggregation_in_set_exists_find_sent H'_step1 _ H.
  by rewrite H_sent in H2.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec; first by rewrite -H_dec.
Qed.

End SingleNodeInvIn.

Lemma Aggregation_aggregate_msg_src_adjacent_dst : 
forall net tr, 
 step_o_star (params := Aggregation_MultiParams) step_o_init net tr ->
 forall n n', aggregate_msg_adjacent n' (net.(onwState) n) (net.(onwPackets) n' n).
Proof.
move => net tr H_st.
move => n n'.
pose P_curr (d : Data) (l : list msg) := aggregate_msg_adjacent n' d l.
rewrite -/(P_curr _ _).
apply: (P_inv_n_in H_st); rewrite /P_curr /aggregate_msg_adjacent //= {P_curr net tr H_st}.
  move => onet tr m' m0 ms H_st H_find H_eq IH m_msg H_in.
  rewrite H_eq in IH.
  apply: (IH m_msg).
  by right.
move => onet tr H_st H_neq H_neq_agg H_ins IH m_msg H_in.
exact: Aggregation_nodes_mutually_adjacent _ H_st H_ins.
Qed.

Lemma sumM_init_map_1 : forall fm, sumM fm (init_map fm) = 1.
Proof.
move => fm.
rewrite /sumM sumM_fold_right.
rewrite /init_map /=.
case (init_map_str _).
move => fm' H_init.
have H_el := FinNSet.elements_spec1 fm.
have H_in: forall n, In n (FinNSet.elements fm) -> FinNMap.find n fm' = Some 1.
  move => n H_in.
  apply H_init.
  have [H_el' H_el''] := H_el n.
  apply: H_el'.
  apply InA_alt.
  by exists n; split.
move {H_init H_el}.
elim: (FinNSet.elements fm) H_in => //.
move => n l IH H_in.
rewrite /= {1}/sum_fold.
have H_in': In n (n :: l) by left.
have H_find' := H_in n H_in'.
rewrite IH.
  case H_find: (FinNMap.find _ _) => [n'|] //.
  rewrite H_find in H_find'.
  injection H_find' => H_eq'.
  rewrite H_eq'.
  by gsimpl.
move => n' H_in''.
apply H_in.
by right.
Qed.

Definition conserves_node_mass (d : Data) : Prop := 
d.(local) = d.(aggregate) * sumM d.(adjacent) d.(sent) * (sumM d.(adjacent) d.(received))^-1.

Lemma Aggregation_conserves_node_mass : 
forall onet tr,
 step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
 forall n, conserves_node_mass (onet.(onwState) n).
Proof.
move => onet tr H_step.
remember step_o_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_o_init /conserves_node_mass /init_Data /= => n.
  by rewrite sumM_init_map_1; gsimpl.
move => n.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //; last by rewrite /update /=; case (Name_eq_dec _ _) => H_dec.
  rewrite /update /= {H_step2}.    
  have H_ins: FinNSet.In from (x'.(onwState) to).(adjacent).
    have H_in: In (Aggregate x) (x'.(onwPackets) from to) by rewrite H0; left.
    exact: (Aggregation_aggregate_msg_src_adjacent_dst H_step1 _ _ _ H_in).
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec {H_dec to} in H H2 H3 H4 H5 H6 H0 H_ins.
  rewrite /conserves_node_mass H2 H3 H4 H5 H6 {H2 H3 H4 H5 H6}.      
  rewrite IHH_step1 sumM_add_map //; gsimpl.      
  suff H_eq: (x'.(onwState) n).(aggregate) * x * sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent) * x^-1 * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received))^-1 = 
  (x'.(onwState) n).(aggregate) * sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received))^-1 * (x * x^-1) by rewrite H_eq; gsimpl.
  by aac_reflexivity.
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases => //.
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec {h H_dec H_step2} in H2 H3 H4 H1.
  rewrite /conserves_node_mass H1 H2 H3 H4 {H1 H2 H3 H4}.
  rewrite IHH_step1; gsimpl.
  suff H_eq: 
      (x'.(onwState) n).(aggregate) * d.(local) * sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent))^-1 * (x'.(onwState) n).(aggregate)^-1 * sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received))^-1 = 
      d.(local) * ((x'.(onwState) n).(aggregate) * (x'.(onwState) n).(aggregate)^-1) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(sent))^-1) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received) * (sumM (x'.(onwState) n).(adjacent) (x'.(onwState) n).(received))^-1) by rewrite H_eq; gsimpl.
  by aac_reflexivity.
- rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec {h H_dec H_step2} in H H2 H3 H1 H5 H6 H7.
  rewrite /conserves_node_mass /=.
  rewrite H4 H3 H5 H6 H7.
  rewrite IHH_step1 sumM_add_map; gsimpl.
  by aac_reflexivity.
- have [m' H_ex] := Aggregation_in_set_exists_find_sent H_step1 _ H.
  by rewrite H2 in H_ex.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec.
- rewrite /update /=.
  by case (Name_eq_dec _ _) => H_dec.
Qed.

Definition sum_local (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * d.(local)) 1 l.

Definition sum_aggregate (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * d.(aggregate)) 1 l.

Definition sum_sent (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * sumM d.(adjacent) d.(sent)) 1 l.

Definition sum_received (l : list Data) : m :=
fold_right (fun (d : Data) (partial : m) => partial * sumM d.(adjacent) d.(received)) 1 l.

Definition conserves_mass_globally (l : list Data) : Prop :=
sum_local l = sum_aggregate l * sum_sent l * (sum_received l)^-1.

Definition conserves_node_mass_all (l : list Data) : Prop :=
forall d, In d l -> conserves_node_mass d.

Lemma global_conservation : 
  forall (l : list Data), 
    conserves_node_mass_all l ->
    conserves_mass_globally l.
Proof.
rewrite /conserves_mass_globally /=.
elim => [|d l IH]; first by gsimpl.
move => H_cn.
rewrite /=.
rewrite /conserves_node_mass_all in H_cn.
have H_cn' := H_cn d.
rewrite H_cn'; last by left.
rewrite IH; first by gsimpl; aac_reflexivity.
move => d' H_in.
apply: H_cn.
by right.
Qed.

Definition Nodes_data (ns : list Name) (onet : ordered_network) : list Data :=
fold_right (fun (n : Name) (l' : list Data) => (onet.(onwState) n) :: l') [] ns.

Lemma Aggregation_conserves_node_mass_all : 
forall onet tr,
 step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
 conserves_node_mass_all (Nodes_data Nodes onet).
Proof.
move => onet tr H_st.
rewrite /conserves_node_mass_all.
rewrite /Nodes_data.
elim: Nodes => //.
move => n l IH.
move => d.
rewrite /=.
move => H_or.
case: H_or => H_or.
  rewrite -H_or.
  exact: (Aggregation_conserves_node_mass H_st).
exact: IH.
Qed.

Corollary Aggregate_conserves_mass_globally :
forall onet tr,
 step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
 conserves_mass_globally (Nodes_data Nodes onet).
Proof.
move => onet tr H_step.
apply: global_conservation.
exact: Aggregation_conserves_node_mass_all H_step.
Qed.

Definition aggregate_sum_fold (msg : Msg) (partial : m) : m :=
match msg with
| Aggregate m' => partial * m'
end.

Definition sum_aggregate_msg := fold_right aggregate_sum_fold 1.

Lemma Aggregation_sum_aggregate_msg_self :  
  forall onet tr,
   step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
   forall n, sum_aggregate_msg (onet.(onwPackets) n n) = 1.
Proof.
move => onet tr H_step n.
by rewrite (Aggregation_self_channel_empty H_step).
Qed.

(* given n, sum aggregate messages for all its incoming channels *)
Definition sum_aggregate_msg_incoming (ns : list Name) (onet : ordered_network) (n : Name) : m := 
fold_right (fun (n' : Name) (partial : m) => partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.

(* given list of active names and all names, sum all incoming channels for all active *)
Definition sum_aggregate_msg_incoming_active (allns : list Name) (actns : list Name)  (onet : ordered_network) : m :=
fold_right (fun (n : Name) (partial : m) => partial * sum_aggregate_msg_incoming allns onet n) 1 actns.

Definition conserves_network_mass (actns : list Name) (allns : list Name) (onet : ordered_network) : Prop :=
sum_local (Nodes_data actns onet) = sum_aggregate (Nodes_data actns onet) * sum_aggregate_msg_incoming_active allns actns onet.

Lemma sum_aggregate_msg_incoming_step_o_init :
  forall ns n, sum_aggregate_msg_incoming ns step_o_init n = 1.
Proof.
move => ns n.
rewrite /sum_aggregate_msg_incoming /= {n}.
elim: ns => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_msg_incoming_all_step_o_init :
  forall actns allns, sum_aggregate_msg_incoming_active allns actns step_o_init = 1.
Proof.
rewrite /sum_aggregate_msg_incoming_active /=.
elim => [|a l IH] l' //=.
rewrite IH sum_aggregate_msg_incoming_step_o_init.
by gsimpl.
Qed.

Lemma sum_local_step_o_init :
  forall ns, sum_local (Nodes_data ns step_o_init) = 1.
Proof.
rewrite /Nodes_data /step_o_init /=.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_aggregate_step_o_init :
  forall ns, sum_aggregate (Nodes_data ns step_o_init) = 1.
Proof.
elim => //.
move => n l IH.
rewrite /= IH.
by gsimpl.
Qed.

Lemma sum_local_split :
  forall ns0 ns1 onet n,
    sum_local (Nodes_data (ns0 ++ n :: ns1) onet) =
    (onet.(onwState) n).(local) * sum_local (Nodes_data (ns0 ++ ns1) onet).
Proof.
elim => /=; first by move => ns1 onet n; aac_reflexivity.
move => n ns IH ns1 onet n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma sum_aggregate_split :
  forall ns0 ns1 onet n,
    sum_aggregate (Nodes_data (ns0 ++ n :: ns1) onet) =
    (onet.(onwState) n).(aggregate) * sum_aggregate (Nodes_data (ns0 ++ ns1) onet).
Proof.
elim => /=; first by move => ns1 onet n; aac_reflexivity.
move => n ns IH ns1 onet n'.
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
forall n' d onet ns,
~ In n' ns ->
fold_right
  (fun (n : Name) (l : list Data) =>
     (match Name_eq_dec n n' with
      | left _ => d 
      | right _ => (onet.(onwState) n) 
      end) :: l) [] ns = Nodes_data ns onet.
Proof.
move => n' d onet.
elim => //.
move => a l IH H_in.
rewrite /=.
case (Name_eq_dec _ _) => H_dec; first by case: H_in; left.
rewrite IH => //.
move => H_in'.
by case: H_in; right.
Qed.

(* with failed nodes - don't add their incoming messages, but add their outgoing channels to non-failed nodes *)

Lemma sum_aggregate_msg_neq_from :
forall from to n onet ms ns,
~ In from ns ->
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns =
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.
Proof.
move => from to n onet ms.
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
forall from to n onet ms ns,
to <> n ->
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns =
fold_right
  (fun (n' : Name) (partial : m) => 
     partial * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns.
Proof.
move => from to n onet ms ns H_neq.
elim: ns => //.
move => n' l IH.
rewrite /= IH /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
by move: H_dec => [H_dec H_dec'].
Qed.

Lemma sum_aggregate_msg_neq_to :
forall from to onet ms ns1 ns0,
~ In to ns1 ->
fold_right
  (fun (n : Name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : Name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (update2 onet.(onwPackets) from to ms n' n)) 1 ns0) 1 ns1 = 
fold_right
  (fun (n : Name) (partial : m) =>
     partial *
     fold_right
       (fun (n' : Name) (partial0 : m) =>
          partial0 * sum_aggregate_msg (onet.(onwPackets) n' n)) 1 ns0) 1 ns1.
Proof.
move => from to onet ms.
elim => //=.
move => n l IH ns H_in.
rewrite IH /=; last by move => H_in'; case: H_in; right.
have H_neq: to <> n by move => H_eq; case: H_in; left.
by rewrite sum_aggregate_msg_n_neq_from.
Qed.

Lemma sum_aggregate_msg_fold_split :
forall ns0 ns1 ns2 from to ms onet,
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 (ns1 ++ ns2) = 
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 ns1 * 
fold_right (fun (n : Name) (partial : m) => partial * fold_right (fun (n' : Name) (partial0 : m) =>
         partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0) 1 ns2.
Proof.
move => ns0 ns1 ns2 from to ms onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split_folded :
forall ns0 ns1 from to n onet ms,
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 (ns0 ++ ns1) = 
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns0 *
fold_right (fun (n' : Name) (partial0 : m) =>
        partial0 * sum_aggregate_msg (update2 (onwPackets onet) from to ms n' n)) 1 ns1.
Proof.
move => ns0 ns1 from to n onet ms.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH /=.
by aac_reflexivity.
Qed.


Lemma sum_aggregate_msg_incoming_active_split :
forall ns0 ns1 ns2 onet,
sum_aggregate_msg_incoming_active ns0 (ns1 ++ ns2) onet = 
sum_aggregate_msg_incoming_active ns0 ns1 onet *
sum_aggregate_msg_incoming_active ns0 ns2 onet.
Proof.
move => ns0 ns1 ns2 onet.
elim: ns1 => //=; first by gsimpl.
move => n ns1 IH.
rewrite /= IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_incoming_split :
forall ns0 ns1 onet n,
sum_aggregate_msg_incoming (ns0 ++ ns1) onet n = 
sum_aggregate_msg_incoming ns0 onet n *
sum_aggregate_msg_incoming ns1 onet n.
Proof.
move => ns0 ns1 onet n.
elim: ns0 => //=; first by gsimpl.
move => n' ns0 IH.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_aggregate_msg_split : 
forall l1 l2,
sum_aggregate_msg (l1 ++ l2) = sum_aggregate_msg l1 * sum_aggregate_msg l2.
Proof.
elim => //= [|msg l' IH] l2; first by gsimpl.
rewrite IH.
rewrite /aggregate_sum_fold /=.
case: msg => m'.
by aac_reflexivity.
Qed.

Lemma fold_right_update_id :
forall ns h x',
fold_right 
  (fun (n : Name) (l' : list Data) =>
     update (onwState x') h (onwState x' h) n :: l') [] ns =
fold_right 
  (fun (n : Name) (l' : list Data) =>
     (onwState x' n) :: l') [] ns.
Proof.
elim => //.
move => n l IH h onet.
rewrite /= IH.
rewrite /update /=.
case (Name_eq_dec _ _) => H_dec //.
by rewrite H_dec.
Qed.

Lemma Aggregation_conserves_network_mass : 
  forall onet tr,
  step_o_star (params := Aggregation_MultiParams) step_o_init onet tr ->
  conserves_network_mass Nodes Nodes onet.
Proof.
move => onet tr H_step.
remember step_o_init as y in H_step.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /conserves_network_mass /= {H_init}.
  rewrite sum_aggregate_msg_incoming_all_step_o_init.
  rewrite sum_local_step_o_init sum_aggregate_step_o_init.
  by gsimpl.
concludes.
match goal with
| [ H : step_o _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  net_handler_cases => //.
  - rewrite /= /conserves_network_mass /=.
    have H_inn := In_n_Nodes to.     
    apply in_split in H_inn.
    move: H_inn => [ns0 [ns1 H_inn]].
    rewrite H_inn sum_local_split. 
    rewrite sum_aggregate_split /=.
    rewrite /Nodes_data.
    rewrite {2}/update /=.
    have H_nd := nodup.
    rewrite H_inn in H_nd.
    have H_nin := nodup_notin _ _ _ H_nd.
    rewrite (Nodes_data_not_in _ d x' _ H_nin).
    rewrite /update /=.
    case (Name_eq_dec _ _) => H_dec // {H_dec}.
    rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
    rewrite H2 H3 {H_nd H_nin}.
    rewrite /conserves_network_mass in IHH_step1.
    rewrite H_inn in IHH_step1.
    rewrite sum_local_split in IHH_step1.
    rewrite sum_aggregate_split in IHH_step1.
    rewrite sum_aggregate_msg_fold_split.   
    have H_inn': In from Nodes by exact: In_n_Nodes.
    apply in_split in H_inn'.
    move: H_inn' => [ns2 [ns3 H_in']].
    rewrite -{1}H_inn.
    have H_nin: ~ In to ns0.
      have H_nd := nodup.
      rewrite H_inn in H_nd.
      have H_nin := nodup_notin _ _ _ H_nd.
      move => H_nin'.
      case: H_nin.
      apply in_or_app.
      by left.    
    rewrite {1}sum_aggregate_msg_neq_to //.
    rewrite -/(sum_aggregate_msg_incoming_active Nodes ns0 x').
    rewrite /=.
    have H_nin': ~ In to ns1.
      have H_nd := nodup.
      rewrite H_inn in H_nd.
      have H_nin' := nodup_notin _ _ _ H_nd.
      move => H_nin''.
      case: H_nin'.
      apply in_or_app.
      by right.
    rewrite {1}sum_aggregate_msg_neq_to //.
    rewrite -{1}H_inn.
    rewrite -/(sum_aggregate_msg_incoming_active Nodes ns1 x').
    rewrite -H_inn {3}H_in'.
    rewrite sum_aggregate_msg_split_folded /=.
    have H_nin_f: ~ In from ns2.
      have H_nd := nodup.
      rewrite H_in' in H_nd.
      have H_nin_f := nodup_notin _ _ _ H_nd.
      move => H_nin_f'.
      case: H_nin_f.
      apply in_or_app.
      by left.
    have H_nin_f': ~ In from ns3.
      have H_nd := nodup.
      rewrite H_in' in H_nd.
      have H_nin_f' := nodup_notin _ _ _ H_nd.
      move => H_nin_f''.
      case: H_nin_f'.
      apply in_or_app.
      by right.
    rewrite sum_aggregate_msg_neq_from //.    
    rewrite -/(sum_aggregate_msg_incoming ns2 x' to).
    rewrite sum_aggregate_msg_neq_from //.    
    rewrite -/(sum_aggregate_msg_incoming ns3 x' to).
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec => H_dec.
    rewrite -{1}H_inn in IHH_step1.
    rewrite H_in' in IHH_step1.
    rewrite sum_aggregate_msg_incoming_active_split /= in IHH_step1.
    rewrite -{1 2}H_in' in IHH_step1.
    rewrite sum_aggregate_msg_incoming_split /= in IHH_step1.
    rewrite H0 /= in IHH_step1.
    rewrite IHH_step1.
    gsimpl.
    set mm := sum_aggregate _.
    by aac_reflexivity.    
  - have H_in_ag: In (Aggregate x) (x'.(onwPackets) from to) by rewrite H0; left.
    have H_adj := Aggregation_aggregate_msg_src_adjacent_dst H_step1 _ _ _ H_in_ag.
    have [m' H_recv] := Aggregation_in_set_exists_find_received H_step1 _ H_adj.
    by rewrite H in H_recv.
find_apply_lem_hyp input_handlers_IOHandler.
io_handler_cases => // {H_step2}.
- (* Local *)
  rewrite /=.
  rewrite /conserves_network_mass /=.
  have H_inn := In_n_Nodes h.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  rewrite H_inn sum_local_split. 
  rewrite sum_aggregate_split /=.
  rewrite /Nodes_data.
  rewrite {2}/update /=.
  have H_nd := nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  rewrite (Nodes_data_not_in _ d x' _ H_nin).
  rewrite {1 2}/update /=.
  case (Name_eq_dec _ _) => H_dec // {H_dec}.
  rewrite -H_inn.
  rewrite /sum_aggregate_msg_incoming_active /=.
  rewrite /sum_aggregate_msg_incoming /=.
  rewrite /conserves_network_mass in IHH_step1.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  rewrite {1 2}H_inn in IHH_step1.
  rewrite sum_local_split sum_aggregate_split in IHH_step1.
  rewrite H1.
  suff H_suff: sum_local (Nodes_data (ns0 ++ ns1) x') = aggregate (onwState x' h) * (local (onwState x' h))^-1 * sum_aggregate (Nodes_data (ns0 ++ ns1) x') * sum_aggregate_msg_incoming_active Nodes Nodes x'.
    rewrite H_suff.
    gsimpl.
    set mm := sum_aggregate _.
    by aac_reflexivity.
  have ->: sum_local (Nodes_data (ns0 ++ ns1) x') = sum_local (Nodes_data (ns0 ++ ns1) x') * local (onwState x' h) * (local (onwState x' h))^-1 by gsimpl.
  aac_rewrite IHH_step1.
  by aac_reflexivity.  
- (* send Aggregate *)
  rewrite /conserves_network_mass /=.
  have H_inn := In_n_Nodes h.
  apply in_split in H_inn.
  move: H_inn => [ns0 [ns1 H_inn]].
  rewrite H_inn sum_local_split /=.
  rewrite sum_aggregate_split /=.
  rewrite /Nodes_data.
  rewrite {2}/update /=.
  have H_nd := nodup.
  rewrite H_inn in H_nd.
  have H_nin := nodup_notin _ _ _ H_nd.
  rewrite (Nodes_data_not_in _ d x' _ H_nin).
  rewrite {1 2}/update /=.
  case (Name_eq_dec _ _) => H_dec // {H_dec}.
  rewrite H3 H4.
  gsimpl.
  rewrite -H_inn.
  rewrite /sum_aggregate_msg_incoming_active /=.
  rewrite /sum_aggregate_msg_incoming /=.
  have H_inn': In x Nodes by exact: In_n_Nodes.
  apply in_split in H_inn'.
  move: H_inn' => [ns2 [ns3 H_in']].
  rewrite {2}H_in'.
  have H_nin': ~ In x ns2.
    have H_nd' := nodup.
    rewrite H_in' in H_nd'.
    have H_nin' := nodup_notin _ _ _ H_nd'.
    move => H_nin''.
    case: H_nin'.
    apply in_or_app.
    by left.  
  rewrite sum_aggregate_msg_fold_split.
  rewrite sum_aggregate_msg_neq_to //.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes ns2 x').
  rewrite /=.
  have H_nin'': ~ In x ns3.
    have H_nd' := nodup.
    rewrite H_in' in H_nd'.
    have H_nin'' := nodup_notin _ _ _ H_nd'.
    move => H_nin'''.
    case: H_nin''.
    apply in_or_app.
    by right.
  rewrite sum_aggregate_msg_neq_to //.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes ns3 x').
  rewrite {3}H_inn.
  rewrite sum_aggregate_msg_split_folded.
  have H_nin_h: ~ In h ns0.
    move => H_in_h.
    case: H_nin.
    apply in_or_app.
    by left.
  have H_nin'_h: ~ In h ns1.
    move => H_in_h.
    case: H_nin.
    apply in_or_app.
    by right.
  rewrite sum_aggregate_msg_neq_from //.
  rewrite /=.
  rewrite sum_aggregate_msg_neq_from //.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec; last by case: H_dec.
  gsimpl.
  rewrite -/(sum_aggregate_msg_incoming ns0 x' x).
  rewrite -/(sum_aggregate_msg_incoming ns1 x' x).
  rewrite sum_aggregate_msg_split /=.
  gsimpl.
  rewrite /conserves_network_mass in IHH_step1.
  rewrite {1 2}H_inn in IHH_step1.
  rewrite sum_local_split in IHH_step1.
  rewrite sum_aggregate_split in IHH_step1.
  rewrite {2}H_in' in IHH_step1.
  rewrite sum_aggregate_msg_incoming_active_split /= in IHH_step1.
  rewrite {3}H_inn in IHH_step1.
  rewrite sum_aggregate_msg_incoming_split /= in IHH_step1.
  move: IHH_step1.
  gsimpl.
  move => IH.
  rewrite IH.
  set mm := sum_aggregate _.
  by aac_reflexivity.  
- have [m' H_recv] := Aggregation_in_set_exists_find_sent H_step1 _ H.
  by find_rewrite.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
- rewrite /conserves_network_mass /= in IHH_step1.
  rewrite /conserves_network_mass /=.
  rewrite /Nodes_data /=.
  rewrite fold_right_update_id /=.
  rewrite -/(Nodes_data Nodes x').
  rewrite /sum_aggregate_msg_incoming_active /= /sum_aggregate_msg_incoming /=.
  rewrite -/(sum_aggregate_msg_incoming_active Nodes Nodes x').
  by rewrite IHH_step1.
Qed.

Inductive step_o_f : step_relation (list name * ordered_network) (name * (input + list output)) :=
| SOF_deliver : forall net net' failed m ms out d l from to,
                   onwPackets net from to = m :: ms ->
                   ~ In to failed ->
                   net_handlers to from m (onwState net to) = (out, d, l) ->
                   net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l) (update (onwState net) to d) ->
                   step_o_f (failed, net) (failed, net') [(to, inr out)]
| SOF_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                 input_handlers h inp (onwState net h) = (out, d, l) ->
                 net' = mkONetwork (collate h (onwPackets net) l) (update (onwState net) h d) ->
                 step_o_f (failed, net) (failed, net') [(h, inl inp); (h, inr out)]
| SOF_fail :  forall h net net' failed l,
               ~ In h failed ->
               l =  ->
               net' = mkONetwork (collate h (onwPackets net) l) (onwState net) ->
               step_o_f (failed, net) (h :: failed, net') [].

Definition step_o_f_star := refl_trans_1n_trace step_o_f.

Definition step_o_f_init : list name * ordered_network := ([], step_o_init).

(* merge sent and received into "balance" map? *)

(* use boolean function, name-to-list function, or decision procedure for adjacency *)
(* at recovery time, send new to all existing neighbors *)
(* handle problem with unprocessed fail messages for recovery *)

(* higher-level language like ott/lem for protocols that exports to handlers? *)

(* 
path to liveness properties:

- handler monad must be able to output labels, e.g., return broadcast_level

- all labels must be decorated with the involved node names by the semantics

- labels must be removed at extraction time

- is strong local liveness warranted in practice? how can extraction guarantee it?

*)

(*Parameter adjacentP : Name -> Name -> Prop.*)

(*
firstin q5 (msg_new j) ->
dequeued q5 q' ->
sum_aggregate_queue_ident q' i5 = sum_aggregate_queue_ident q5 i5.
*)

(*
firstin q5 (msg_aggregate j m5) ->
  dequeued q5 q' ->
  sum_aggregate_queue_ident q' j = sum_aggregate_queue_ident q5 j * m5^-1.
*)

(* 
sum_aggregate_queue (queue_enqueue q5 (msg_aggregate j m5)) = sum_aggregate_queue q5 * m5.
*)

(* 
~ ISet.in j ->
snd (sum_aggregate_queue_aux (I5, m') (queue_enqueue q5 (msg_aggregate j m5))) = 
snd (sum_aggregate_queue_aux (I5, m') q5) * m5.
*)

(* 
  ~ In_queue (msg_fail j) q5 ->
  sum_aggregate_queue (queue_enqueue q5 (msg_fail j)) = sum_aggregate_queue q5 * (sum_aggregate_queue_ident q5 j)^-1.
*)

(* ---------------------------------- *)

(*
Section StepFailureMsg.

  (* this step relation transforms a list of failed hosts (list name * network), but does not transform handlers (H : hosts) *)
  Inductive step_fm : step_relation (list name * network) (name * (input + list output)) :=
  (* like step_m, but only delivers to hosts that haven't failed yet *)
  | SFM_deliver : forall net net' failed p xs ys out d l,
                nwPackets net = xs ++ p :: ys ->
                ~ In (pDst p) failed ->
                net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (out, d, l) ->
                net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys)
                                 (update (nwState net) (pDst p) d) ->
                step_fm (failed, net) (failed, net') [(pDst p, inr out)]
  | SFM_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                  input_handlers h inp (nwState net h) = (out, d, l) ->
                  net' = mkNetwork (send_packets h l ++ nwPackets net)
                                   (update (nwState net) h d) ->
                  step_fm (failed, net) (failed, net') [(h, inl inp) ;  (h, inr out)]
  (* a host fails and a Fail message is delivered to all adjacent hosts *)
  (* add same node to failed several times? *)
  (* use adjacency function *)
  | SFM_fail :  forall h net failed,
                 step_fm (failed, net) (h :: failed, net) [].

  Definition step_fm_star : step_relation (list name * network) (name * (input + list output)) :=
    refl_trans_1n_trace step_fm.

  Definition step_fm_init : list name * network := ([], step_m_init).
End StepFailureMsg.
*)

End Aggregation.

(* 

Module NatValue10 <: NatValue.
 Definition n := 10.
End NatValue10.

Module fin_10_compat_OT := fin_OT_compat NatValue10.

Require Import FMapList.
Module Map <: FMapInterface.S := FMapList.Make fin_10_compat_OT.

Definition b : fin 10 := Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))).

Eval compute in Map.find b (Map.add b 3 (Map.empty nat)).

Module fin_10_OT := fin_OT NatValue10.

Require Import MSetList.
Module FinSet <: MSetInterface.S := MSetList.Make fin_10_OT.
Eval compute in FinSet.choose (FinSet.singleton b).

*)

(*
Definition exclude (excluded : list Name) := filter (fun n => sumbool_not _ _ (in_dec Name_eq_dec n excluded)).

Definition fail_for := map (fun (n : Name) => (n, Fail)).

Inductive step_o_f : step_relation (list Name * ordered_network) (Name * (input + list output)) :=
| SOF_deliver : forall net net' failed m ms out d l from to,
                   onwPackets net from to = m :: ms ->
                   ~ In to failed ->
                   net_handlers to from m (onwState net to) = (out, d, l) ->
                   net' = mkONetwork (collate to (update2 (onwPackets net) from to ms) l) (update (onwState net) to d) ->
                   step_o_f (failed, net) (failed, net') [(to, inr out)]
| SOF_input : forall h net net' failed out inp d l,
                 ~ In h failed ->
                 input_handlers h inp (onwState net h) = (out, d, l) ->
                 net' = mkONetwork (collate h (onwPackets net) l) (update (onwState net) h d) ->
                 step_o_f (failed, net) (failed, net') [(h, inl inp); (h, inr out)]
| SOF_fail :  forall h net net' failed l,
               ~ In h failed ->
               l = fail_for (adjacent_to_node h (exclude failed nodes)) ->
               net' = mkONetwork (collate h (onwPackets net) l) (onwState net) ->
               step_o_f (failed, net) (h :: failed, net') [].

Definition step_o_f_star := refl_trans_1n_trace step_o_f.

Definition step_o_f_init : list Name * ordered_network := ([], step_o_init).
*)
