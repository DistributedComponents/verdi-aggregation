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

Set Implicit Arguments.

Module Type CommutativeFinGroup.
Parameter gT : finGroupType.
Parameter mulgC : @commutative gT _ mulg.
End CommutativeFinGroup.

Module AAux (Import NT : NameType)  
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

Lemma fold_left_right : forall (fm : NM) (l : list name),
  fold_left (fun partial n => (sum_fold fm) n partial) l 1 = fold_right (sum_fold fm) 1 l.
Proof.
move => fm; elim => [|a l IH] //.
rewrite /= -IH /sum_fold {IH}.
case (NMap.find _ _) => [m6|] // {a}; gsimpl.
move: m6; elim: l => [m6|a l IH m6] => /=; first by gsimpl.
case (NMap.find _ _) => [m7|] //.
rewrite mulgC IH; gsimpl.
by rewrite -IH.
Qed.

Corollary sumM_fold_right : forall (fs : NS) (fm : NM), 
  NSet.fold (sum_fold fm) fs 1 = fold_right (sum_fold fm) 1 (NSet.elements fs).
Proof. by move => fs fm; rewrite NSet.fold_spec fold_left_right. Qed.

Lemma not_in_add_eq : forall (l : list name) (n : name) (fm : NM) (m5 : m),
  ~ InA eq n l -> 
  fold_right (sum_fold (NMap.add n m5 fm)) 1 l = fold_right (sum_fold fm) 1 l.
move => l n fm m5; elim: l => //.
move => a l IH H_in.
have H_in': ~ InA eq n l by move => H_neg; apply: H_in; apply InA_cons; right.
apply IH in H_in'.
rewrite /= H_in' /= /sum_fold.
have H_neq: n <> a by move => H_eq; apply: H_in; apply InA_cons; left.
case H_find: (NMap.find _ _) => [m6|].
  apply NMapFacts.find_mapsto_iff in H_find.  
  apply NMapFacts.add_neq_mapsto_iff in H_find => //.
  apply NMapFacts.find_mapsto_iff in H_find.
  case H_find': (NMap.find _ _) => [m7|]; last by rewrite H_find' in H_find.
  rewrite H_find in H_find'.
  injection H_find' => H_eq.
  by rewrite H_eq.
case H_find': (NMap.find _ _) => [m6|] => //.
apply NMapFacts.find_mapsto_iff in H_find'.
apply (NMapFacts.add_neq_mapsto_iff _ m5 _ H_neq) in H_find'.
apply NMapFacts.find_mapsto_iff in H_find'.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_add_map : forall (n : name) (fs : NS) (fm : NM) (m5 m' : m),
  NSet.In n fs ->
  NMap.find n fm = Some m5 ->
  sumM fs (NMap.add n (m5 * m') fm) = sumM fs fm * m'.
Proof.
move => n fs fm m5 m' H_in H_find.
have H_in_el: InA eq n (NSet.elements fs) by apply NSetFacts.elements_1.
have H_nodup := NSet.elements_spec2w fs.
move: H_in_el H_nodup {H_in}.
rewrite 2!/sumM 2!sumM_fold_right.
elim (NSet.elements fs) => [|a l IH] H_in H_nodup; first by apply InA_nil in H_in.
case (name_eq_dec n a) => H_dec.
  rewrite H_dec in H_find.
  rewrite H_dec /sum_fold /=.
  have H_find_eq := @NMapFacts.add_eq_o m fm a a (m5 * m') (refl_equal a).
  case H_find': (NMap.find _ _) => [m6|]; last by rewrite H_find_eq in H_find'.
  rewrite H_find_eq in H_find'.
  injection H_find' => H_eq.
  rewrite -H_eq.
  case H_find'': (NMap.find _ _) => [m7|]; last by rewrite H_find in H_find''.
  rewrite H_find'' in H_find.
  injection H_find => H_eq'.
  rewrite H_eq'; gsimpl.
  inversion H_nodup; subst.
  by rewrite not_in_add_eq.
apply InA_cons in H_in.
case: H_in => H_in //.
have H_nodup': NoDupA eq l by inversion H_nodup.
rewrite /= (IH H_in H_nodup') /sum_fold.
case H_find': (NMap.find _ _) => [m6|].
  apply NMapFacts.find_mapsto_iff in H_find'.
  apply NMapFacts.add_neq_mapsto_iff in H_find' => //.
  apply NMapFacts.find_mapsto_iff in H_find'.
  case H_find'': (NMap.find _ _) => [m7|]; last by rewrite H_find'' in H_find'.
  rewrite H_find' in H_find''.
  injection H_find'' => H_eq.
  rewrite H_eq.
  set fr := fold_right _ _ _.
  by aac_reflexivity.
case H_find'': (NMap.find _ _) => [m7|] //.
apply NMapFacts.find_mapsto_iff in H_find''.
apply (NMapFacts.add_neq_mapsto_iff _ (m5 * m') _ H_dec) in H_find''.
apply NMapFacts.find_mapsto_iff in H_find''.
by rewrite H_find' in H_find''.
Qed.

Lemma eqlistA_eq : forall (l l' : list name), eqlistA eq l l' -> l = l'.
Proof.
elim; first by move => l' H_eql; inversion H_eql.
move => a l IH.
case => [|a' l'] H; first by inversion H.
inversion H; subst.
by rewrite (IH l').
Qed.

Lemma sumM_remove : forall (fs : NS) (n : name) (fm : NM) (m5: m),
  NSet.In n fs ->
  NMap.find n fm = Some m5 ->
  sumM (NSet.remove n fs) fm = sumM fs fm * m5^-1.
Proof.
move => I_ind.
pose P_ind (fs : NS) := forall n (fm : NM) (m5: m),
  NSet.In n fs ->
  NMap.find n fm = Some m5 ->
  sumM (NSet.remove n fs) fm = sumM fs fm * m5^-1.
rewrite -/(P_ind I_ind).
apply (NSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty n fm m5 H_in.
  have H_empty' := NSet.empty_spec.
  by contradict H_in; apply H_empty.
rewrite /sumM.
move => fs I' IH a H_below H_add n fm m5 H_in H_map.
have H_eql := NSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite 2!sumM_fold_right.
case (name_eq_dec a n) => H_eq.
  move: H_in H_map; rewrite -H_eq H_eql {H_eq} => H_in H_map.
  rewrite /NSetOrdProps.P.Add in H_add.
  have H_rem := NSet.remove_spec I' a.
  have H_below': NSetOrdProps.Below a (NSet.remove a I').
    rewrite /NSetOrdProps.Below => a' H_in'.
    apply NSet.remove_spec in H_in'.
    case: H_in' => H_in' H_neq.
    apply H_below.
    apply H_add in H_in'.
    by case: H_in' => H_in'; first by case H_neq.
  have H_add' := NSetProps.Add_remove H_in.
  have H_eql' := NSetOrdProps.elements_Add_Below H_below' H_add'.
  apply eqlistA_eq in H_eql'.
  rewrite H_eql {H_eql} in H_eql'.
  set el_rm := NSet.elements _.
  have {H_eql'} ->: el_rm = NSet.elements fs by injection H_eql'.
  rewrite {2}/fold_right {2}/sum_fold {el_rm}.
  case H_find: (NMap.find _ _) => [m6|]; last by rewrite H_map in H_find.
  rewrite H_map in H_find.
  have ->: m6 = m5 by injection H_find.
  by gsimpl.
rewrite H_eql.
have H_in': NSet.In n fs.
  apply H_add in H_in.
  by case: H_in.
have H_below': NSetOrdProps.Below a (NSet.remove n fs).
  rewrite /NSetOrdProps.Below => a' H_inr.
  apply H_below.
  have H_rm := NSet.remove_spec fs n a'.
  apply H_rm in H_inr.
  by case: H_inr.
have H_add': NSetOrdProps.P.Add a (NSet.remove n fs) (NSet.remove n I').
  rewrite /NSetOrdProps.P.Add => a'.
  have H_add_a' := H_add a'.
  case (name_eq_dec a a') => H_eq'.
    split => H_imp; first by left.
    have H_or: a = a' \/ NSet.In a' fs by left.
    apply H_add_a' in H_or.
    apply NSet.remove_spec; split => //.
    by rewrite -H_eq'.
  split => H_imp.    
    right.
    apply NSet.remove_spec in H_imp.
    case: H_imp => H_imp H_neq.
    apply NSet.remove_spec; split => //.
    apply H_add_a' in H_imp.
    by case: H_imp.
  case: H_imp => H_imp //.
  apply NSet.remove_spec in H_imp.
  case: H_imp => H_imp H_neq.
  have H_or: a = a' \/ NSet.In a' fs by right.
  apply H_add_a' in H_or.
  by apply NSet.remove_spec; split.
have H_eql' := NSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /fold_right /sum_fold.      
case H_find: (NMap.find a fm) => [m6|].
  have H_eq' := IH n fm m5 H_in' H_map.
  rewrite 2!sumM_fold_right /fold_right in H_eq'.
  rewrite H_eq' /sum_fold.
  by aac_reflexivity.
have H_eq' := IH n fm m5 H_in' H_map.
rewrite 2!sumM_fold_right in H_eq'.
rewrite /fold_right in H_eq'.
by rewrite H_eq' /sum_fold.
Qed.

Lemma sumM_notins_remove_map : forall (fs : NS) (n : name) (fm : NM),
  ~ NSet.In n fs ->
  sumM fs (NMap.remove n fm) = sumM fs fm.
Proof.
move => fs n fm H_ins.
have H_notin: ~ InA eq n (NSet.elements fs).
  move => H_ina.
  by apply NSetFacts.elements_2 in H_ina.
rewrite 2!/sumM 2!sumM_fold_right.
move: H_notin.
elim (NSet.elements fs) => [|a l IH] H_in //.
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
case H_find: (NMap.find _ _) => [m5|].
  case H_find': (NMap.find _ _) => [m6|]; rewrite NMapFacts.remove_neq_o in H_find => //.
    rewrite H_find in H_find'.
    injection H_find' => H_eq.
    rewrite H_eq.
    by rewrite IH'.
  by rewrite H_find in H_find'.
rewrite NMapFacts.remove_neq_o in H_find => //.
case H_find': (NMap.find _ _) => [m5|] //.
by rewrite H_find in H_find'.
Qed.

Lemma sumM_remove_remove : forall (fs : NS) (n : name) (fm : NM) (m5: m),
  NSet.In n fs ->
  NMap.find n fm = Some m5 ->
  sumM (NSet.remove n fs) (NMap.remove n fm) = sumM fs fm * m5^-1.
Proof.
move => fs n fm m5 H_ins H_find.
have H_ins': ~ NSet.In n (NSet.remove n fs) by move => H_ins'; apply NSetFacts.remove_1 in H_ins'.
rewrite sumM_notins_remove_map => //.
exact: sumM_remove.
Qed.

Lemma sumM_empty : forall (fs : NS) (fm : NM), NSet.Empty fs -> sumM fs fm = 1.
Proof.
move => fs fm.
rewrite /NSet.Empty => H_empty.
have H_elts: forall n, ~ InA eq n (NSet.elements fs).
  move => n H_notin.
  apply NSetFacts.elements_2 in H_notin.
  by apply (H_empty n).
rewrite /sumM sumM_fold_right.
case H_elt: (NSet.elements fs) => [|a l] //.
have H_in: InA eq a (NSet.elements fs) by rewrite H_elt; apply InA_cons; left.
by contradict H_in; apply (H_elts a).
Qed.

Lemma sumM_eq : forall (fs : NS) (fm' : NS) (fm : NM),
   NSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
Proof.
move => I_ind.
pose P_ind (fs : NS) := forall (fm' : NS) (fm : NM),
   NSet.Equal fs fm' ->
   sumM fs fm = sumM fm' fm.
rewrite -/(P_ind I_ind).
apply (NSetOrdProps.set_induction_min); rewrite /P_ind {P_ind I_ind}.
  move => fs H_empty fm' fm H_eq.
  have H_empty': NSet.Empty fm'.
    rewrite /NSet.Empty => a H_in.
    apply H_eq in H_in.
    by apply H_empty in H_in.    
  rewrite sumM_empty //.
  by rewrite sumM_empty.
move => fs fm' IH a H_below H_add fm'' fm H_eq.
have H_eql := NSetOrdProps.elements_Add_Below H_below H_add.
apply eqlistA_eq in H_eql.
rewrite /sumM 2!sumM_fold_right H_eql.
have H_below': NSetOrdProps.Below a (NSet.remove a fm'').
  rewrite /NSetOrdProps.Below => a' H_in.
  apply H_below.
  apply (NSet.remove_spec) in H_in.
  case: H_in => H_in H_neq.    
  apply H_eq in H_in.
  apply H_add in H_in.
  by case: H_in => H_in; first by case H_neq.
have H_add': NSetOrdProps.P.Add a (NSet.remove a fm'') fm''.
  rewrite /NSetOrdProps.P.Add => a'.
  case (name_eq_dec a a') => H_eq_a.
    split => H_imp; first by left.
    apply H_eq.
    rewrite -H_eq_a.
    by apply H_add; left.
  split => H_imp; first by right; apply NSet.remove_spec; split; last by contradict H_eq_a.
  case: H_imp => H_imp; first by case H_eq_a.
  by apply NSet.remove_spec in H_imp; case: H_imp.
have H_eq': NSet.Equal fs (NSet.remove a fm'').
   rewrite /NSet.Equal => a'.
   case (name_eq_dec a a') => H_eq_a.
     have H_or: a = a' \/ NSet.In a' fs by left.
     apply H_add in H_or.
     split => H_imp.
       apply NSet.remove_spec.
       rewrite -H_eq_a in H_or H_imp.
       apply H_below in H_imp.
       contradict H_imp.
       by apply NOT.lt_strorder.
     rewrite H_eq_a in H_imp.
     apply NSet.remove_spec in H_imp.
     case: H_imp.
     move => H_in H_eq'.
     by case: H_eq'.
   split => H_imp.
     apply NSet.remove_spec; split; last by contradict H_eq_a.
     apply H_eq.
     by apply H_add; right.
   apply NSet.remove_spec in H_imp.
   case: H_imp => H_imp H_neq.
   apply H_eq in H_imp.
   apply H_add in H_imp.
   by case: H_imp.
have H_eql' := NSetOrdProps.elements_Add_Below H_below' H_add'.
apply eqlistA_eq in H_eql'.
rewrite H_eql' /sum_fold /fold_right.
have IH' := IH (NSet.remove a fm'') fm.
rewrite /sumM 2!sumM_fold_right /fold_right in IH'.
by case H_find: (NMap.find _ _) => [m5|]; rewrite IH'.
Qed.

Corollary sumM_add : forall (fs : NS) (fm : NM) (m5 : m) (n : name),
  ~ NSet.In n fs -> 
  NMap.find n fm = Some m5 ->
  sumM (NSet.add n fs) fm = sumM fs fm * m5.
Proof.
move => fs fm m5 n H_notin H_map.
have H_in: NSet.In n (NSet.add n fs) by apply NSet.add_spec; left.
have H_rm := @sumM_remove (NSet.add n fs) _ _ _ H_in H_map.
set srm := sumM _ _ in H_rm.
set sadd := sumM _ _ in H_rm *.
have <-: srm * m5 = sadd by rewrite H_rm; gsimpl.
suff H_eq: srm = sumM fs fm by rewrite H_eq; aac_reflexivity.
apply sumM_eq.
exact: (NSetProps.remove_add H_notin).
Qed.

Lemma sumM_add_add : forall (fs : NS) (M5 : NM) (m5 : m) (n : name),
  ~ NSet.In n fs -> 
  sumM (NSet.add n fs) (NMap.add n m5 M5) = sumM fs M5 * m5.
Proof.
move => fs M5 m5 n H_in.
have H_find := @NMapFacts.add_eq_o _ M5 _ _ m5 (refl_equal n).
rewrite (@sumM_add _ _ _ _ H_in H_find) {H_find}.
set sadd := sumM _ _.
suff H_suff: sadd = sumM fs M5 by rewrite H_suff.
rewrite /sadd /sumM 2!sumM_fold_right {sadd}.
have H_in_el: ~ InA eq n (NSet.elements fs) by move => H_neg; apply NSetFacts.elements_2 in H_neg.
by move: H_in_el; apply not_in_add_eq.
Qed.

Lemma sumM_init_map_1 : forall fm, sumM fm (init_map fm) = 1.
Proof.
move => fm.
rewrite /sumM sumM_fold_right.
rewrite /init_map /=.
case (init_map_str _).
move => fm' H_init.
have H_el := NSet.elements_spec1 fm.
have H_in: forall n, In n (NSet.elements fm) -> NMap.find n fm' = Some 1.
  move => n H_in.
  apply H_init.
  have [H_el' H_el''] := H_el n.
  apply: H_el'.
  apply InA_alt.
  by exists n; split.
move {H_init H_el}.
elim: (NSet.elements fm) H_in => //.
move => n l IH H_in.
rewrite /= {1}/sum_fold.
have H_in': In n (n :: l) by left.
have H_find' := H_in n H_in'.
rewrite IH.
  case H_find: (NMap.find _ _) => [n'|] //.
  rewrite H_find in H_find'.
  injection H_find' => H_eq'.
  rewrite H_eq'.
  by gsimpl.
move => n' H_in''.
apply H_in.
by right.
Qed.

Definition sum_active_fold (adj : NS) (map : NM) (n : name) (partial : m) : m :=
if NSet.mem n adj
then sum_fold map n partial
else partial.

Definition sumM_active (adj : NS) (map : NM) (ns : list name) : m :=
fold_right (sum_active_fold adj map) 1 ns.

Lemma sumM_active_remove_eq : 
  forall ns n adj map,
  ~ In n ns ->
  sumM_active adj map ns = sumM_active (NSet.remove n adj) map ns.
Proof.
elim => [|n ns IH] n' adj map H_notin //.
have H_notin': ~ In n' ns by move => H_in; case: H_notin; right.
rewrite /= /sum_active_fold.
case: ifPn => H_mem; case: ifPn => H_mem'.
- by rewrite (IH n').
- apply NSetFacts.mem_2 in H_mem.
  have H_ins: ~ NSet.In n (NSet.remove n' adj).
    move => H_ins.
    move/negP: H_mem' => H_mem'.
    contradict H_mem'.
    by apply NSetFacts.mem_1 in H_ins.
  contradict H_ins.
  apply NSetFacts.remove_2 => //.
  move => H_eq.
  contradict H_notin.
  by left.
- have H_ins: ~ NSet.In n adj by move => H_ins; apply NSetFacts.mem_1 in H_ins; rewrite H_ins in H_mem.
  apply NSetFacts.mem_2 in H_mem'.
  contradict H_ins.
  by apply NSetFacts.remove_3 in H_mem'.
- by rewrite (IH n').
Qed.

Lemma sumM_active_app_distr : 
  forall ns0 ns1 adj map,
    sumM_active adj map (ns0 ++ ns1) = sumM_active adj map ns0 * sumM_active adj map ns1.
Proof.
elim => [|n ns0 IH] ns1 adj map /=; first by gsimpl.
rewrite IH.
rewrite /sum_active_fold /sum_fold.
case: ifP => H_mem //.
by case H_find: (NMap.find _ _) => [m0|]; first by aac_reflexivity.
Qed.

Lemma sumM_active_eq_sym : 
  forall ns ns' adj map,
  Permutation ns ns' ->
  sumM_active adj map ns = sumM_active adj map ns'.
Proof.
elim => [|n ns IH] ns' adj map H_pm.
  apply Permutation_nil in H_pm.
  by rewrite H_pm.
have H_in: In n (n :: ns) by left.
have H_in': In n ns'.
  move: H_pm H_in.
  exact: Permutation_in.
apply in_split in H_in'.
move: H_in' => [ns0 [ns1 H_eq]].
rewrite H_eq in H_pm.
have H_pm' := H_pm.
apply Permutation_cons_app_inv in H_pm'.
rewrite H_eq sumM_active_app_distr /=.
rewrite (IH _ _ _ H_pm') sumM_active_app_distr.
rewrite /sum_active_fold.
case: ifP => H_mem //.
rewrite /sum_fold.
by case H_find: (NMap.find _ _) => [m0|]; first by aac_reflexivity.
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

Lemma permutation_split : 
  forall (A : Type) (ns ns' : list A) (n : A),
  Permutation (n :: ns) ns' ->
  exists ns0, exists ns1, ns' = ns0 ++ n :: ns1.
Proof.
move => A ns ns' n H_pm.
have H_in: In n (n :: ns) by left. 
have H_in': In n ns'.
  move: H_pm H_in. 
  exact: Permutation_in.
by apply In_split in H_in'.
Qed.

Lemma nodup_app_split_right : 
  forall (A : Type) (ns0 ns1 : list A), 
    NoDup (ns0 ++ ns1) -> NoDup ns1.
Proof.
move => A.
elim => [|n ns0 IH] ns1 H_nd //.
inversion H_nd => {l H0 x H}.
exact: IH.
Qed.

Lemma nodup_in_not_in_right : 
  forall (A : Type) (ns0 ns1 : list A) (x : A),
    NoDup (ns0 ++ ns1) -> In x ns0 -> ~ In x ns1.
Proof.
move => A.
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
  forall (A : Type) (ns0 ns1 : list A) (x : A),
    NoDup (ns0 ++ ns1) -> In x ns1 -> ~ In x ns0.
Proof.
move => A.
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
  forall (A : Type) (ns0 ns1 : list A), 
    NoDup (ns0 ++ ns1) -> NoDup ns0.
Proof.
move => A.
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

Lemma global_conservation : 
  forall (l : list data), 
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

Definition Nodes_data (ns : list name) (state : name -> data) : list data :=
fold_right (fun (n : name) (l' : list data) => n.(state) :: l') [] ns.

Lemma sum_local_split :
  forall ns0 ns1 state n,
    sum_local (Nodes_data (ns0 ++ n :: ns1) state) =
    n.(state).(aggr_local) * sum_local (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => /=; first by move => ns1 state n; aac_reflexivity.
move => n ns IH ns1 state n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma sum_aggregate_split :
  forall ns0 ns1 state n,
    sum_aggregate (Nodes_data (ns0 ++ n :: ns1) state) =
    n.(state).(aggr_aggregate) * sum_aggregate (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => /=; first by move => ns1 state n; aac_reflexivity.
move => n ns IH ns1 state n'.
rewrite IH /=.
by gsimpl.
Qed.

Lemma Nodes_data_not_in : 
forall n' d state ns,
~ In n' ns ->
fold_right
  (fun (n : name) (l : list data) =>
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

Section MsgProps.

Context {am : AggregationMsg}.

Context {data} {ad : AggregationData data}.

Instance EqDec_eq_name : EqDec_eq name := name_eq_dec.

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
suff H_suff: @update2 _ EqDec_eq_name _ f from to ms n' n = f n' n by rewrite H_suff.
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

Lemma sum_fail_map_incoming_sent_neq_eq :
  forall ns packets state from to ms n d,
  n <> to ->
  sum_fail_map_incoming ns (update2 packets from to ms) n
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
  sum_fail_map_incoming ns (update2 packets from to ms) n
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
  sum_fail_sent_incoming_active ns0 ns1 packets (update' state h d) =
  sum_fail_sent_incoming_active ns0 ns1 packets state.
Proof.
elim => //=.
move => n ns1 IH ns0 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns1 by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update'.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_not_in_eq_alt :
forall ns packets state h d,
  ~ In h ns ->
  sum_fail_received_incoming_active nodes ns packets (update' state h d) =
  sum_fail_received_incoming_active nodes ns packets state.
Proof.
elim => //=.
move => n ns IH packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_not_in: ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update'.
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

Lemma Nodes_data_not_in_eq :
  forall ns (state : name -> data) to d,
    ~ In to ns ->
    Nodes_data ns (update' state to d) =
    Nodes_data ns state.
Proof.
elim => //.
move => n ns IH state to d H_in.
rewrite /=.
have H_neq: n <> to by move => H_eq; case: H_in; left.
rewrite {1}/update' /=.
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
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (aggr_adjacent (update' state h d n))
    (aggr_sent (update' state h d n)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_sent (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update'.
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
  sum_fail_map_incoming ns (update2 packets from to ms) n
    (aggr_adjacent (update' state h d n))
    (aggr_received (update' state h d n)) =
  sum_fail_map_incoming ns packets n (aggr_adjacent (state n)) (aggr_received (state n)).
Proof.
elim => //=.
move => n ns IH packets state from to ms h n0 d H_neq H_neq'.
rewrite IH //.
rewrite /update'.
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
    sum_fail_received_incoming_active ns1 ns0 (update2 packets from to ms) (update' state h d) =
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
    sum_fail_sent_incoming_active ns1 ns0 packets (update' state h d) =
    sum_fail_sent_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update'.
by case (name_eq_dec _ _) => H_dec.
Qed.

Lemma sum_fail_received_incoming_active_update_not_in_eq :
  forall ns0 ns1 packets state h d,
    ~ In h ns0 ->
    sum_fail_received_incoming_active ns1 ns0 packets (update' state h d) =
    sum_fail_received_incoming_active ns1 ns0 packets state.
Proof.
elim => //=.
move => n ns IH ns1 packets state h d H_in.
have H_neq: n <> h by move => H_eq; case: H_in; left.
have H_in': ~ In h ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update'.
by case (name_eq_dec _ _) => H_dec.
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
rewrite (collate_f_eq _ _ _ _ _ _ H_eq) {H_eq}.
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
  by rewrite (collate_f_eq _ _ _ _ _ _ H_eq_f).
- rewrite IH //.
  set up2 := update2 _ _ _ _.
  have H_eq_f: up2 n0 n = f n0 n by rewrite /up2 /update2; case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
  by rewrite (collate_f_eq _ _ _ _ _ _ H_eq_f).
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
rewrite (collate_f_eq _ _ _ _ _ _ H_eq) {H_eq}.
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

End MsgProps.

End AAux.
