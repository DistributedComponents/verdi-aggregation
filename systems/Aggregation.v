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

Definition m_neq_bool (a b : m) : bool :=
match m_eq_dec a b with
| left _ => false
| right _ => true
end.

Definition Name := (fin num_sources).

Definition list_sources := (all_fin num_sources).

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
exact: fin_eq_dec.
Defined.

Definition Name_neq_bool (x y : Name) : bool :=
match Name_eq_dec x y with
| left _ => false
| right _ => true
end.

Lemma Name_neq_bool_true_neq : forall (x y : Name),
  Name_neq_bool x y = true -> x <> y.
Proof.
move => x y.
rewrite /Name_neq_bool.
by case (Name_eq_dec _ _).
Qed.

Lemma Name_neq_bool_neq_true : forall (x y : Name),
  x <> y -> Name_neq_bool x y = true.
Proof.
move => x y.
rewrite /Name_neq_bool.
by case (Name_eq_dec _ _).
Qed.

Inductive Msg := 
| Aggregate : m -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Input :=
| Local : m -> Input
| Send : Name -> Input
| Query : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: Name_eq_dec.
Defined.

Inductive Output :=
| Response : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data := mkData { local : m ; aggregate : m ; adjacent : FinNS ; sent : FinNM ; received : FinNM }.

Parameter adjacency : Name -> FinNS.

Parameter not_adjacent_self : forall (n : Name), ~ FinNSet.In n (adjacency n).

Parameter adjacency_mutual : forall (n n' : Name), FinNSet.In n (adjacency n') -> FinNSet.In n' (adjacency n).

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
    
Definition init_Data (n : Name) := mkData 1 1 (adjacency n) (init_map (adjacency n)) (init_map (adjacency n)).

Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
match msg with
| Aggregate m_msg => 
  st <- get ;;
  match FinNMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    let new_aggregate := st.(aggregate) * m_msg in
    let new_received := FinNMap.add src (m_src * m_msg) st.(received) in
    put (mkData st.(local) new_aggregate st.(adjacent) st.(sent) new_received)
  end
end.

Definition IOHandler (me : Name) (i : Input) : Handler Data :=
match i with
| Local m_msg => 
  st <- get ;;
  let new_local := m_msg in
  let new_aggregate := st.(aggregate) * m_msg * st.(local)^-1 in
  put (mkData new_local new_aggregate st.(adjacent) st.(sent) st.(received))
| Send dst => 
  st <- get ;;
  when 
  (FinNSet.mem dst st.(adjacent) && m_neq_bool st.(aggregate) 1)
  (match FinNMap.find dst st.(sent) with
   | None => nop
   | Some m_dst =>        
     let new_aggregate := 1 in
     let new_sent := FinNMap.add dst (m_dst * st.(aggregate)) st.(sent) in
     put (mkData st.(local) new_aggregate st.(adjacent) new_sent st.(received)) >> (send (dst, (Aggregate st.(aggregate))))
   end)
| Query =>
  st <- get ;;
  write_output (Response st.(aggregate))
end.

Definition Nodes := list_sources.

Theorem In_n_Nodes : forall n : Name, In n Nodes.
Proof. exact: all_fin_all. Qed.

Theorem nodup : NoDup Nodes.
Proof. exact: all_fin_NoDup. Qed.

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

Definition sum_fold (fm : FinNM) (n : Name) (partial : m) : m :=
match FinNMap.find n fm with
| Some m' => partial * m'
| None => partial
end.

Definition sumM (fs : FinNS) (fm : FinNM) : m := 
FinNSet.fold (sum_fold fm) fs 1.

Lemma fold_left_right : forall (fm : FinNM) (l : list Name),
  fold_left (fun partial j => (sum_fold fm) j partial) l 1 = fold_right (sum_fold fm) 1 l.
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
  sumM fs (FinNMap.remove (elt:=m) n fm) = sumM fs fm.
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
      (exists dst m', i = Send dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = FinNMap.add dst (m' * st.(aggregate)) st.(sent) /\
         out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (exists dst, i = Send dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ FinNMap.find dst st.(sent) = None /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = Send dst /\ FinNSet.In dst st.(adjacent) /\ st.(aggregate) = 1 /\
         st' = st /\
         out = [] /\ ms = []) \/
      (exists dst, i = Send dst /\ ~ FinNSet.In dst st.(adjacent) /\ 
         st' = st /\ 
         out = [] /\ ms = []) \/
      (i = Query /\ st' = st /\ out = [Response (aggregate st)] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler.
case: i => [m_msg|dst|]; monad_unfold.
- rewrite /= => H_eq.
  injection H_eq => H_ms H_st H_out H_tt.
  rewrite -H_st /=.
  by left; exists m_msg.
- case H_mem: (FinNSet.mem _ _); case H_neq: (m_neq_bool _ _); move: H_neq; rewrite /m_neq_bool; case (m_eq_dec _ _) => H_dec H_neq //=.
  * apply FinNSetFacts.mem_2 in H_mem.
    case H_find: (FinNMap.find _ _) => [m'|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    + by right; left; exists dst; exists m'.
    + by right; right; left; exists dst.
  * apply FinNSetFacts.mem_2 in H_mem.
    move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; left; exists dst.
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
     st' = st /\ out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg => m_msg; monad_unfold.
case H_find: (FinNMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
- by left; exists m_msg; exists  m_src.
- by right; exists m_msg.
Qed.

  Ltac set_up_io_handlers :=
    intros;
    find_apply_lem_hyp IOHandler_cases;
    intuition idtac; try break_exists; intuition idtac; subst;
    repeat find_rewrite;
    simpl in *; intuition idtac; repeat find_inversion.

  Ltac set_up_net_handlers :=
    intros;
    match goal with
      | [ H : context [ NetHandler (pDst ?p) _ _ _ ] |- _ ] =>
        destruct (pDst p) eqn:?
    end; simpl in *;
    find_apply_lem_hyp NetHandler_cases;
    intuition; subst;
    simpl in *; intuition;
    repeat find_rewrite;
    repeat find_inversion;
    simpl in *.

Lemma Aggregation_node_not_adjacent_self : 
forall net tr n, 
 step_m_star (params := Aggregation_MultiParams) step_m_init net tr ->
 ~ FinNSet.In n (nwState net n).(adjacent).
Proof.
move => net tr n H.
remember step_m_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_m_init /=.
  exact: not_adjacent_self.
concludes.
match goal with
| [ H : step_m _ _ _ |- _ ] => invc H
end; simpl.
find_apply_lem_hyp net_handlers_NetHandler.
  rewrite /update /=.
  case (Name_eq_dec _ _) => H_dec //.
  rewrite -H_dec in H3.
  find_apply_lem_hyp NetHandler_cases.
  case: H3 => [[m_msg [m_src H3]]|[m_msg H3]].
    move: H3 => [H_msg [H_find [H_l [H_a [H_adj H3]]]]].
    by rewrite H_adj.
  move: H3 => [H_msg [H_find [H_st H3]]].
  by rewrite H_st.
apply input_handlers_IOHandler in H2.
find_apply_lem_hyp IOHandler_cases.
rewrite /update /=.
case (Name_eq_dec _ _) => H_dec //.
rewrite -H_dec in H2.
case: H2 => [[m_msg H2]|H2].
  move: H2 => [H_i [H_l [H_ag [H_ad H2]]]].
  by rewrite H_ad.
case: H2 => [[dst [m' H2]]|H2].
  move: H2 => [H_i [H_ins [H_neq [H_find [H_l [H_ag [H_ad H2]]]]]]].
  by rewrite H_ad.
case: H2 => [[dst H2]|H2].
  move: H2 => [H_i [H_ins [H_neq [H_find [H_st H2]]]]].
  by rewrite H_st.
case: H2 => [[dst H2]|H2].
  move: H2 => [H_i [H_ins [H_eq [H_st H2]]]].
  by rewrite H_st.
case: H2 => [[dst H2]|H2].
  move: H2 => [H_i [H_ins [H_st H2]]].
  by rewrite H_st.
move: H2 => [H_i [H_st H2]].
by rewrite H_st.
Qed.

Lemma Aggregation_nodes_mutually_adjacent : 
forall net tr n n', 
 step_m_star (params := Aggregation_MultiParams) step_m_init net tr ->
 FinNSet.In n (nwState net n').(adjacent) -> FinNSet.In n' (nwState net n).(adjacent).
Proof.
move => net tr n n' H.
remember step_m_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /step_m_init /=.
  exact: adjacency_mutual.
rewrite H_init -/step_m_star in H H1.
have H_self := Aggregation_node_not_adjacent_self H.
concludes.
match goal with
| [ H : step_m _ _ _ |- _ ] => invc H
end; simpl.
find_apply_lem_hyp net_handlers_NetHandler.
  destruct (pBody p).
  rewrite /= in H3.
  monad_unfold.
  rewrite /= in H3.
  injection H3.
  move => H_l H_st H_out.
  rewrite -H_st /=.
  rewrite /update.
  case (Name_eq_dec _ _) => H_eq; case (Name_eq_dec _ _) => H_eq' //=.
  - rewrite -H_eq.
    rewrite -H_eq in H_eq'.
    rewrite H_eq'.
    move => H_ins.
    by contradict H_ins.
  - by rewrite -H_eq.
  - by rewrite -H_eq'.
apply input_handlers_IOHandler in H2.
destruct inp.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
  * rewrite /= H_eq H_eq' {H_eq H_eq'}.
    move => H_ins.
    by contradict H_ins.
  * by rewrite -H_eq.
  * by rewrite -H_eq'.
- move: H2.
  rewrite /IOHandler /=.
  monad_unfold.
  case H_mem: (FinNSet.mem _ _); case H_m_neq: (m_neq_bool _ _) => //= H2; injection H2 => H_l H_st H_o.
  * rewrite -H_st /update /= {H_st H2}.
    case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
    + by rewrite H_eq H_eq'.
    + by rewrite -H_eq.
    + by rewrite -H_eq'.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
    + by rewrite H_eq H_eq'.
    + by rewrite -H_eq.
    + by rewrite -H_eq'.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
    + by rewrite H_eq H_eq'.
    + by rewrite -H_eq.
    + by rewrite -H_eq'.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
    + by rewrite H_eq H_eq'.
    + by rewrite -H_eq.
    + by rewrite -H_eq'.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq; case (Name_eq_dec _) => H_eq' //=.
  * by rewrite H_eq H_eq'.
  * by rewrite -H_eq.
  * by rewrite -H_eq'.
Qed.

Definition in_set_exists_find_sent (d : Data) : Prop :=
  forall (n : Name), FinNSet.In n d.(adjacent) -> exists m5 : m, FinNMap.find n d.(sent) = Some m5.

Definition in_set_exists_find_received (d : Data) : Prop :=
  forall (n : Name), FinNSet.In n d.(adjacent) -> exists m5 : m, FinNMap.find n d.(received) = Some m5.

Definition conserves_node_mass (d : Data) : Prop := 
d.(local) = d.(aggregate) * sumM d.(adjacent) d.(sent) * (sumM d.(adjacent) d.(received))^-1.

Lemma Aggregation_conserves_node_mass : 
forall net tr n, 
 step_m_star (params := Aggregation_MultiParams) step_m_init net tr ->
 conserves_node_mass (nwState net n).
Proof.
move => net tr n H.
remember step_m_init as y in *.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
  
concludes.
match goal with
| [ H : step_m _ _ _ |- _ ] => invc H
end; simpl.
  find_apply_lem_hyp net_handlers_NetHandler.
  destruct (pBody p).
  rewrite /= in H3.
  monad_unfold.
  rewrite /= in H3.
  injection H3.
  move => H_l H_st H_out.
  rewrite -H_st /=.
  rewrite /update.
  case (name_eq_dec _ _) => H_eq //.
  rewrite /= -H_eq {H_eq}.
  case H_find: (FinNMap.find _ _) => [m'|].
    rewrite IHrefl_trans_1n_trace1 /=.
    rewrite (sum_mass_add_Some _ _ _ H_find).
    by ring_simplify.
  rewrite IHrefl_trans_1n_trace1 /=.
  rewrite (sum_mass_add_None _ _ _ H_find).
  by ring_simplify.
apply input_handlers_IOHandler in H2.
destruct inp.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq //.
  rewrite /= -H_eq {H_eq}.
  rewrite IHrefl_trans_1n_trace1 /=.
  symmetry.
  by ring_simplify.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  move: H2.
  case H_m_neq: (m_neq_bool _); case H_n_neq: (Name_neq_bool _ _) => //= H2; injection H2 => H_l H_st H_o.
  * rewrite -H_st /update /= {H_st H2}.
    case (Name_eq_dec _) => H_eq //=.
    rewrite -H_eq {H_eq}.
    case H_find: (FinNMap.find _ _) => [m'|].
      rewrite IHrefl_trans_1n_trace1 /=.
      rewrite (sum_mass_add_Some _ _ _ H_find).
      by ring_simplify.
    rewrite IHrefl_trans_1n_trace1 /=.
    rewrite (sum_mass_add_None _ _ _ H_find).
    by ring_simplify.          
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
  * rewrite -H_st /update /=.
    case (Name_eq_dec _) => H_eq //.
    by rewrite -H_eq.
- rewrite /IOHandler /= in H2.
  monad_unfold.
  injection H2 => H_l H_st H_o.
  rewrite -H_st /update /=.
  case (Name_eq_dec _) => H_eq //.
  by rewrite -H_eq.
Qed.

  (* Definition conserves_mass_globally (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) * (sum_sent nodes) * (sum_received nodes)^-1. *)

  (* Definition conserves_network_mass (nodes : list node) : Prop :=
     sum_local nodes = (sum_aggregate nodes) + (sum_aggregate_queues nodes) + (sum_sent_fail_queues nodes) - 
     (sum_received_fail_queues nodes). *)

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
