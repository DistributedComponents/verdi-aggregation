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

Class AggregationData (data : Type) :=
  {
    aggr_local : data -> m ;
    aggr_aggregate : data -> m ;
    aggr_adjacent : data -> NS ;
    aggr_balance : data -> NM
  }.

Section AggregationProps.

Context {data} {ad : AggregationData data}.

Definition conserves_node_mass (d : data) : Prop := 
d.(aggr_local) = d.(aggr_aggregate) * sumM d.(aggr_adjacent) d.(aggr_balance).

Definition sum_local (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * d.(aggr_local)) 1 l.

Definition sum_aggregate (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * d.(aggr_aggregate)) 1 l.

Definition sum_balance (l : list data) : m :=
fold_right (fun (d : data) (partial : m) => partial * sumM d.(aggr_adjacent) d.(aggr_balance)) 1 l.

Definition conserves_mass_globally (l : list data) : Prop :=
sum_local l = sum_aggregate l * sum_balance l.

Definition conserves_node_mass_all (l : list data) : Prop :=
forall d, In d l -> conserves_node_mass d.

Definition Nodes_data (ns : list name) (state : name -> data) : list data :=
fold_right (fun (n : name) (l' : list data) => n.(state) :: l') [] ns.

End AggregationProps.

Section AggregationDataProps.

Context {data} {ad : AggregationData data}.

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
  forall ns0 ns1 (state : name -> data),
    Nodes_data (ns0 ++ ns1) state =
    Nodes_data ns0 state ++ Nodes_data ns1 state.
Proof.
elim => //.
move => n ns0 IH ns1 state.
rewrite /=.
by rewrite IH.
Qed.

Lemma sum_balance_distr : 
  forall dl dl',
    sum_balance (dl ++ dl') = sum_balance dl * sum_balance dl'.
Proof.
elim => /=; first by move => dl'; gsimpl.
move => d dl IH dl'.
rewrite IH.
by aac_reflexivity.
Qed.

Lemma sum_balance_Nodes_data_distr : 
  forall ns0 ns1 state,
    sum_balance (Nodes_data ns0 state) * sum_balance (Nodes_data ns1 state) =
    sum_balance (Nodes_data (ns0 ++ ns1) state).
Proof.
elim => [|n ns0 IH] ns1 net /=; first by gsimpl.
rewrite -IH.
by aac_reflexivity.
Qed.

End AggregationDataProps.

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

Definition sum_fail_balance_incoming_active (allns : list name) (actns : list name) (packets : name -> name -> list aggr_msg) (state : name -> data) : m :=
fold_right (fun (n : name) (partial : m) => 
  partial * sum_fail_map_incoming allns packets n n.(state).(aggr_adjacent) n.(state).(aggr_balance)) 1 actns.

Definition conserves_network_mass (actns : list name) (allns : list name) (packets : name -> name -> list aggr_msg) (state : name -> data) : Prop :=
sum_local (Nodes_data actns state) = 
  sum_aggregate (Nodes_data actns state) * 
  sum_aggregate_msg_incoming_active allns actns packets * 
  sum_fail_balance_incoming_active allns actns packets state.

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

Lemma sum_fail_balance_incoming_active_map_msgs_eq :
  forall (state : name -> data_fst) (state' : name -> data_snd) (packets : name -> name -> list (@aggr_msg am_fst)) allns actns,
    (forall n, In n actns -> n.(state).(aggr_adjacent) = n.(state').(aggr_adjacent)) ->
    (forall n, In n actns -> n.(state).(aggr_balance) = n.(state').(aggr_balance)) ->    
    sum_fail_balance_incoming_active allns actns packets state = 
    sum_fail_balance_incoming_active allns actns (fun src dst => map_msgs (packets src dst)) state'.
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
