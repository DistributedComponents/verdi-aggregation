Require Import Verdi.

Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Relation_Definitions.
Require Import RelationClasses.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Section OrderedProps.

Context {A : Type}. 
Context {ea : EqDec_eq A}.
Context {R : relation A} {rd : RelDec R}.

Lemma filter_rel_related :
  forall n n' ns,
  In n' (filter_rel n ns) -> 
  In n' ns /\ R n n'.
Proof.
move => n n' ns H_in.
rewrite /filter_rel in H_in.
apply filter_In in H_in.
move: H_in => [H_in H_eq].
split => //.
move: H_eq.
by case rel_dec.
Qed.

Lemma related_filter_rel : 
  forall n n' ns,
    In n' ns -> 
    R n n' ->
    In n' (filter_rel n ns).
Proof.
move => n n' ns H_in H_adj.
apply filter_In.
split => //.
by case rel_dec.
Qed.

Lemma count_occ_app_split : 
  forall l l' (a : A),
    count_occ eq_dec (l ++ l') a = count_occ eq_dec l a + count_occ eq_dec l' a.
Proof.
elim => //.
move => a' l IH l' a.
rewrite /=.
case eq_dec => H_dec; first by rewrite IH.
by rewrite IH.
Qed.

(* holds when there are no a' in the list until after all a *)
Fixpoint In_all_before (a a' : A) l : Prop :=
match l with
| [] => True
| a0 :: l' => ~ In a l' \/ (a' <> a0 /\ In_all_before a a' l')
end.

Lemma head_before_all_not_in : 
  forall l (a a' : A),
  a <> a' ->
  In_all_before a a' (a' :: l) ->
  ~ In a l.
Proof.
move => l a a' H_neq H_bef.
case: H_bef => H_bef //.
by move: H_bef => [H_neq' H_bef].
Qed.

Lemma append_neq_before_all : 
  forall l (a a' a0 : A),
    a0 <> a ->
    In_all_before a a' l ->
    In_all_before a a' (l ++ [a0]).
Proof.
elim => [|a l IH] a' a0 a1 H_neq H_bef; first by left.
rewrite /=.
case: H_bef => H_bef.
  left.
  move => H_in.
  apply in_app_or in H_in.
  case: H_in => H_in //.
  by case: H_in => H_in.
move: H_bef => [H_neq' H_bef].
right.
split => //.
exact: IH.
Qed.

Lemma append_before_all_not_in : 
  forall l (a a' a0 : A),
    ~ In a' l ->
    In_all_before a a' (l ++ [a0]).
Proof.
elim => [|a l IH] a0 a' a1 H_in; first by left.
have H_neq': a' <> a.
  move => H_neq.
  rewrite H_neq in H_in.
  case: H_in.
  by left.
have H_in': ~ In a' l.
  move => H_in'.
  by case: H_in; right.
rewrite /=.
right.
split => //.
exact: IH.
Qed.

Lemma not_in_all_before :
  forall l (a a' : A),
    ~ In a l ->
    In_all_before a a' l.
Proof.
case => //.
move => a l a0 a' H_in.
have H_in': ~ In a0 l.
  move => H_in'.
  by case: H_in; right.
by left.
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
case eq_dec => H_dec //.
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
case (in_dec _ _) => H_dec; case eq_dec => H_dec' H_eq.
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

Lemma exclude_in_split_eq :
  forall ns0 ns1 ns failed h,
    exclude (h :: failed) (ns0 ++ h :: ns1) = ns ->
    exclude (h :: failed) (h :: ns0 ++ ns1) = ns.
Proof.
elim => //.
move => n ns IH ns1 ns' failed h.
rewrite /=.
case eq_dec => H_dec; case eq_dec => H_dec' //.
  move => H_ex.
  apply IH in H_ex.
  move: H_ex.
  rewrite /=.
  by case eq_dec.
case (in_dec _ _ _) => H_dec''.
  move => H_ex.
  apply IH in H_ex.
  move: H_ex.
  rewrite /=.
  by case eq_dec.
move => H_ex.
case: ns' H_ex => //.
move => a ns' H_ex.
inversion H_ex.
rewrite H1.
apply IH in H1.
move: H1.
rewrite /=.
case eq_dec => H_ex_dec //.
move => H.
by rewrite H.
Qed.

Lemma collate_f_eq :
  forall B (f : A -> A -> list B) g h n n' l,
  f n n' = g n n' ->
  collate h f l n n' = collate h g l n n'.
Proof.
move => B f g h n n' l.
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

Lemma collate_in_in :
  forall B l h n n' (f : A -> A -> list B) mg,
    In mg (f n' n) ->
    In mg ((collate h f l) n' n).
Proof.
move => B.
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

Lemma collate_neq :
  forall B h n n' ns (f : A -> A -> list B),
    h <> n ->
    collate h f ns n n' = f n n'.
Proof.
move => B h n n' ns f H_neq.
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

Lemma collate_not_in_eq :
  forall B h' h (f : A -> A -> list B) l,
 ~ In h (map (fun nm : A * B => fst nm) l) -> 
  collate h' f l h' h = f h' h.
Proof.
move => B h' h f l.
elim: l f => //=.
case => n m l IH f H_in.
rewrite IH /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by case: H_in; left; move: H_dec => [H_eq H_eq'].
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_app :
  forall B h' l1 l2 (f : A -> A -> list B),
  collate h' f (l1 ++ l2) = collate h' (collate h' f l1) l2.
Proof.
move => B h'.
elim => //.
case => n m l1 IH l2 f.
rewrite /=.
by rewrite IH.
Qed.

Lemma collate_neq_update2 :
  forall B h h' n (f : A -> A -> list B) l ms,
  n <> h' ->
  collate h (update2 f h n ms) l h h' = collate h f l h h'.
Proof.
move => B h h' n f l ms H_neq.
have H_eq: update2 f h n ms h h' =  f h h'.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_eq; first by move: H_eq => [H_eq H_eq'].
by rewrite (collate_f_eq _ _ _ _ _ _ H_eq).
Qed.

Lemma collate_not_in :
  forall B h h' l1 l2 (f : A -> A -> list B),
  ~ In h' (map (fun nm : A * B => fst nm) l1) ->
  collate h f (l1 ++ l2) h h' = collate h f l2 h h'.
Proof.
move => B h h' l1 l2 f H_in.
rewrite collate_app.
elim: l1 f H_in => //.
case => n m l IH f H_in.
rewrite /= IH.
  have H_neq: n <> h' by move => H_eq; case: H_in; left.
  by rewrite collate_neq_update2.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_not_in_mid :
 forall B h h' l1 l2 (f : A -> A -> list B) m,
   ~ In h (map (fun nm : A * B => fst nm) (l1 ++ l2)) ->
   collate h' (update2 f h' h (f h' h ++ [m])) (l1 ++ l2) = collate h' f (l1 ++ (h, m) :: l2).
Proof.
move => B h h' l1 l2 f m H_in.
apply functional_extensionality => from.
apply functional_extensionality => to.
case (eq_dec h' from) => H_dec.
  rewrite -H_dec.
  case (eq_dec h to) => H_dec'.
    rewrite -H_dec'.
    rewrite collate_not_in; last first.
      move => H_in'.
      case: H_in.
      rewrite map_app.
      apply in_or_app.
      by left.
    rewrite collate_not_in //.
    move => H_in'.
    case: H_in.
    rewrite map_app.
    apply in_or_app.
    by left.
  rewrite collate_neq_update2 //.
  rewrite 2!collate_app.
  rewrite /=.
  by rewrite collate_neq_update2.
rewrite collate_neq //.
rewrite collate_neq //.
rewrite /update2 /=.
case (sumbool_and _ _) => H_dec' //.
by move: H_dec' => [H_eq H_eq'].
Qed.

Lemma permutation_map_fst :
  forall B l l',
  Permutation l l' ->
  Permutation (map (fun nm : A * B => fst nm) l) (map (fun nm : A * B => fst nm) l').
Proof.
move => B.
elim.
  move => l' H_pm.
  apply Permutation_nil in H_pm.
  by rewrite H_pm.
case => /= n m l IH l' H_pm.
have H_in: In (n, m) ((n, m) :: l) by left.
have H_in': In (n, m) l'.
  move: H_pm H_in.
  exact: Permutation_in.
apply in_split in H_in'.
move: H_in' => [l1 [l2 H_eq]].
rewrite H_eq in H_pm.
apply Permutation_cons_app_inv in H_pm.
rewrite H_eq.
apply IH in H_pm.
move: H_pm.
rewrite 2!map_app /=.
move => H_pm.
exact: Permutation_cons_app.
Qed.

Lemma nodup_perm_collate_eq :
  forall B h (f : A -> A -> list B) l l',
    NoDup (map (fun nm => fst nm) l) ->
    Permutation l l' ->
    collate h f l = collate h f l'.
Proof.
move => B h f l.
elim: l h f.
  move => h f l' H_nd H_pm.
  apply Permutation_nil in H_pm.
  by rewrite H_pm.
case => h m l IH h' f l' H_nd.
rewrite /= in H_nd.
inversion H_nd; subst.
move => H_pm.
rewrite /=.
have H_in': In (h, m) ((h, m) :: l) by left.
have H_pm' := Permutation_in _ H_pm H_in'.
apply in_split in H_pm'.
move: H_pm' => [l1 [l2 H_eq]].
rewrite H_eq.
rewrite H_eq in H_pm.
apply Permutation_cons_app_inv in H_pm.
have IH' := IH h' (update2 f h' h (f h' h ++ [m])) _ H2 H_pm.
rewrite IH'.
rewrite collate_not_in_mid //.
move => H_in.
case: H1.
suff H_pm': Permutation (map (fun nm : A * B => fst nm) l) (map (fun nm : A * B => fst nm) (l1 ++ l2)).
  move: H_in.
  apply Permutation_in.
  exact: Permutation_sym.
exact: permutation_map_fst.
Qed.

Lemma not_in_exclude :
  forall n ns failed,
    ~ In n ns ->
    ~ In n (exclude failed ns).
Proof.
move => n.
elim => //.
move => n' l IH failed H_in.
rewrite /=.
case (in_dec _ _) => H_dec.
  apply IH.
  move => H_in'.
  case: H_in.
  by right.
move => H_in'.
case: H_in' => H_in'.
  case: H_in.
  by left.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma snd_eq_not_in :
  forall B l n m,
  (forall nm, In nm l -> snd nm = m) ->
  ~ In (n, m) l ->
  ~ In n (map (fun nm : A * B => fst nm) l).
Proof.
move => B.
elim => //.
case => n m l IH n' m' H_in H_in'.
rewrite /= => H_in_map.
case: H_in_map => H_in_map.
  case: H_in'.
  left.
  rewrite -H_in_map.
  have H_in' := H_in (n, m).
  rewrite -H_in' //.
  by left.
contradict H_in_map.
apply: (IH _ m').
  move => nm H_inn.
  apply: H_in.
  by right.
move => H_inn.
case: H_in'.
by right.
Qed.

Lemma not_in_not_in_filter_rel :
  forall ns n h,
    ~ In n ns ->
    ~ In n (filter_rel h ns).
Proof.
elim => //=.
move => n' ns IH n h H_in.
have H_neq: n' <> n by move => H_neq; case: H_in; left.
have H_not_in: ~ In n ns by move => H_in'; case: H_in; right.
case rel_dec => H_dec; last exact: IH.
move => H_in'.
case: H_in' => H_in' //.
contradict H_in'.
exact: IH.
Qed.

Lemma nodup_filter_rel:
  forall h ns,
    NoDup ns ->
    NoDup (filter_rel h ns).
Proof.
move => h m.
elim => //=; first exact: NoDup_nil.
move => n ns H_in H_nd.
case rel_dec => H_dec //.
apply NoDup_cons.
exact: not_in_not_in_filter_rel.
Qed.


Lemma filter_rel_self_eq {irreflexive_R : Irreflexive R} :
  forall ns0 ns1 h,
  filter_rel h (ns0 ++ h :: ns1) = filter_rel h (ns0 ++ ns1).
Proof.
elim => [|n ns0 IH] ns1 h /=.
  case (rel_dec _ _) => /= H_dec //.
  by apply irreflexive_R in H_dec.
case (rel_dec _ _) => /= H_dec //.
by rewrite IH.
Qed.

Lemma collate_map_pair_not_related :
  forall B m n h ns (f : A -> A -> list B),
    ~ R h n ->
    collate h f (map_pair m (filter_rel h ns)) h n = f h n.
Proof.
move => B m n h ns f H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (rel_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_map_pair_notin :
  forall B m' n h ns (f : A -> A -> list B),
    ~ In n ns ->
    collate h f (map_pair m' (filter_rel h ns)) h n = f h n.
Proof.
move => B m' n h ns f.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (rel_dec _ _) => H_dec'.
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

Lemma collate_map_pair_notin_exclude :
  forall B m n h ns (f : A -> A -> list B) failed,
    ~ In n ns ->
    collate h f (map_pair m (filter_rel h (exclude failed ns))) h n = f h n.
Proof.
move => B m n h ns f failed H_in.
apply collate_map_pair_notin.
move => H_ex.
by apply exclude_in in H_ex.
Qed.

Lemma collate_map_pair_live_related :
  forall B m n h ns (f : A -> A -> list B) failed,
    ~ In n failed ->
    R h n ->
    In n ns ->
    NoDup ns ->
    collate h f (map_pair m (filter_rel h (exclude failed ns))) h n = f h n ++ [m].
Proof.
move => B m n h ns f failed H_in H_adj.
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
  case (rel_dec _ _) => H_dec' //.
  rewrite /=.
  rewrite collate_map_pair_notin_exclude //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
rewrite /=.
case (rel_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by move: H_sumb => [H_eq H_eq'].
by rewrite IH.
Qed.

Lemma collate_map_pair_in_failed :
  forall B m' n h ns (f : A -> A -> list B) failed,
    In n failed ->
    collate h f (map_pair m' (filter_rel h (exclude failed ns))) h n = f h n.
Proof.
move => B m' n h ns f failed.
move: f.
elim: ns => //.
  move => n' ns IH f H_in.
  rewrite /=.
  case (in_dec _ _) => H_dec; first by rewrite IH.
rewrite /=.
case (rel_dec _ _) => H_dec'; last by rewrite IH.
rewrite /= IH //.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_in.
Qed.

Lemma collate_map_pair_live_related_alt :
  forall B mg n h ns (f : A -> A -> list B),
    R h n ->
    ~ In n ns ->
    collate h f (map_pair mg (filter_rel h (n :: ns))) h n = f h n ++ [mg].
Proof.
move => B mg n h ns f H_adj H_in /=.
case rel_dec => /= H_dec // {H_dec}.
move: f n h H_in H_adj.
elim: ns  => //=.
  move => f H_in n h.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and //.
  by case: H_and => H_and.
move => n' ns IH f n h H_in H_adj.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
have H_neq: n <> n' by move => H_eq; case: H_in; left.
case rel_dec => /= H_dec; last by rewrite IH.
rewrite {3}/update2.
case sumbool_and => H_and; first by move: H_and => [H_and H_and'].
have IH' := IH f.
rewrite collate_map_pair_notin //.
rewrite /update2.
case sumbool_and => H_and'; first by move: H_and' => [H_and' H_and'']; rewrite H_and'' in H_neq.
case sumbool_and => H_and'' //.
by case: H_and''.
Qed.

Lemma in_collate_in :
  forall B ns n h (f : A -> A -> list B) mg,
  ~ In n ns ->
  In mg ((collate h f (map_pair mg (filter_rel h ns))) h n) ->
  In mg (f h n).
Proof.
move => B.
elim => //=.
move => n' ns IH n h f mg H_in.
have H_neq: n' <> n by move => H_eq; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
case rel_dec => H_dec; last exact: IH.
rewrite /=.
set up2 := update2 _ _ _ _.
have H_eq_f: up2 h n = f h n.
  rewrite /up2 /update2.
  by case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
rewrite (collate_f_eq _ _ _ _ _ _ H_eq_f).
exact: IH.
Qed.

Lemma not_in_map_pair :
  forall B n h (m : B) ns,
    ~ In n ns ->
    ~ In (n, m) (map_pair m (filter_rel h ns)).
Proof.
move => B n h m.
elim => //=.
move => n' ns IH H_in.
case (rel_dec _ _) => H_dec.
  rewrite /=.
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    by case: H_in; left.
  contradict H_in'.
  apply: IH.
  move => H_in'.
  case: H_in.
  by right.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma nodup_map_pair :
  forall B h (m : B) ns,
    NoDup ns ->
    NoDup (map_pair m (filter_rel h ns)).
Proof.
move => B h m.
elim => //=.
  move => H_nd.
  exact: NoDup_nil.
move => n ns IH H_in.
inversion H_in.
case (rel_dec _ _) => H_dec.
  rewrite /=.
  apply NoDup_cons.
    apply IH in H2.
    exact: not_in_map_pair.
  exact: IH.
exact: IH.
Qed.

Lemma nodup_snd_fst :
  forall B nms,
    NoDup nms ->
    (forall nm nm', In nm nms -> In nm' nms -> snd nm = snd nm') ->
    NoDup (map (fun nm : A * B => fst nm) nms).
Proof.
move => B.
elim => //=.
  move => H_nd H_eq.
  exact: NoDup_nil.
case => n m l IH H_nd H_in.
inversion H_nd.
rewrite /=.
apply NoDup_cons.
  have H_snd: forall nm, In nm l -> snd nm = m.
    move => nm H_in_nm.
    have ->: m = snd (n, m) by [].
    apply H_in; first by right.
    by left.    
  exact: (@snd_eq_not_in _ _ _ m).
apply IH => //.
move => nm nm' H_in_nm H_in_nm'.
apply H_in => //.
  by right.
by right.
Qed.

Lemma in_for_msg :
  forall B h (m : B) ns nm,
  In nm (map_pair m (filter_rel h ns)) ->
  snd nm = m.
Proof.
move => B h m.
elim => //.
move => n l IH.
case => /= n' m'.
case (rel_dec _ _) => H_dec.
  rewrite /=.
  move => H_in.
  case: H_in => H_in; first by inversion H_in.
  have ->: m' = snd (n', m') by [].
  exact: IH.
move => H_in.
have ->: m' = snd (n', m') by [].
exact: IH.
Qed.

Lemma in_map_pair_related_in :
  forall B (m : B) ns n h,
  In (n, m) (map_pair m (filter_rel h ns)) ->
  R h n /\ In n ns.
Proof.
move => B m.
elim => //=.
move => n ns IH n' h.
case (rel_dec _ _) => /= H_dec.
  move => H_in.
  case: H_in => H_in.
    inversion H_in.
    rewrite H0 in H_dec.
    split => //.
    by left.
  apply IH in H_in.
  move: H_in => [H_adj H_in].
  split => //.
  by right.
move => H_in.
apply IH in H_in.
move: H_in => [H_adj H_in].
split => //.
by right.
Qed.

Lemma collate_ls_not_in :
  forall B ns (f : A -> A -> list B) h mg from to,
    ~ In from ns ->
    collate_ls ns f h mg from to = f from to.
Proof.
move => B.
elim => //=.
move => n ns IH f h mg from to H_in.
have H_neq: n <> from by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update2.
case sumbool_and => H_dec //.
by move: H_dec => [H_eq H_eq'].
Qed.

Lemma collate_ls_neq_to : 
  forall B ns (f : A -> A -> list B) h mg from to,
    h <> to ->
    collate_ls ns f h mg from to = f from to.
Proof.
move => B.
elim => //=.
move => n ns IH f h mg from to H_neq.
rewrite IH //.
rewrite /update2.
case sumbool_and => H_dec //.
by move: H_dec => [H_eq H_eq'].
Qed.

Lemma collate_ls_nodup_in : 
  forall B ns (f : A -> A -> list B) h mg from,
  NoDup ns ->
  In from ns ->
  collate_ls ns f h mg from h = f from h ++ [mg].
Proof.
move => B.
elim => //=.
move => n ns IH f h mg from H_nd H_in.
inversion H_nd; subst.
break_or_hyp.
  rewrite collate_ls_not_in //.
  rewrite /update2.
  by case sumbool_and => H_dec; last break_or_hyp.    
have H_neq: n <> from by move => H_eq; find_rewrite.
rewrite IH //.
rewrite /update2.
by case sumbool_and => H_dec; first by break_and; find_rewrite.
Qed.

Lemma collate_ls_live_related : 
  forall B ns (f : A -> A -> list B) failed h mg from,
  ~ In from failed ->
  R h from ->
  In from ns ->
  NoDup ns ->     
  collate_ls (filter_rel h (exclude failed ns)) f h mg from h = f from h ++ [mg].
Proof.
move => B ns f failed h mg from.
move => H_f H_adj H_in H_nd.
rewrite collate_ls_nodup_in //; first by apply: nodup_filter_rel; exact: nodup_exclude.
apply filter_In.
split; first exact: In_n_exclude.
by case rel_dec.
Qed.

Lemma collate_ls_f_eq :
  forall B ns (f : A -> A -> list B) g h mg n n',
  f n n' = g n n' ->
  collate_ls ns f h mg n n' = collate_ls ns g h mg n n'.
Proof.
move => B.
elim => //=.
move => n0 ns IH f g h mg n n' H_eq.
set f' := update2 _ _ _ _.
set g' := update2 _ _ _ _.
rewrite (IH f' g') //.
rewrite /f' /g' {f' g'}.
rewrite /update2 /=.
case sumbool_and => H_dec //.
by break_and; repeat find_rewrite.
Qed.

Lemma collate_ls_neq_update2 : 
  forall B ns (f : A -> A -> list B) n h h' ms mg,
  n <> h' ->
  collate_ls ns (update2 f n h ms) h mg h' h = collate_ls ns f h mg h' h.
Proof.
move => B ns f n h h' ms mg H_neq.
have H_eq: update2 f n h ms h' h = f h' h.
  rewrite /update2.
  by case sumbool_and => H_eq; first by break_and; find_rewrite.
by rewrite (collate_ls_f_eq _ _ _ _ _ _ _ H_eq).
Qed.

Lemma collate_ls_not_related :
  forall B ns (f : A -> A -> list B) n h mg,
    ~ R h n ->
    collate_ls (filter_rel h ns) f h mg n h = f n h.
Proof.
move => B.
elim => //=.
move => n' ns IH f n h mg H_adj.
case (eq_dec n n') => H_dec.
  rewrite -H_dec.
  case rel_dec => H_dec' //=.
  by rewrite IH.
case rel_dec => H_dec' /=; last by rewrite IH.
rewrite IH //.
rewrite /update2.
by case sumbool_and => H_and; first by break_and; find_rewrite.
Qed.

Lemma collate_ls_not_in_related :
  forall B ns (f : A -> A -> list B) n h mg,
    ~ In n ns ->
    collate_ls (filter_rel h ns) f h mg n h = f n h.
Proof.
move => B ns f n h mg H_in.
rewrite collate_ls_not_in //.
exact: not_in_not_in_filter_rel.
Qed.

Lemma collate_ls_not_in_related_exclude :
  forall B ns (f : A -> A -> list B) n h mg failed,
    ~ In n ns ->
    collate_ls (filter_rel h (exclude failed ns)) f h mg n h = f n h.
Proof.
move => B ns f n h mg failed H_in.
rewrite collate_ls_not_in //.
apply: not_in_not_in_filter_rel.
exact: not_in_exclude.
Qed.

End OrderedProps.
