Require Import Verdi.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Section ListProps.

Variable A : Type.

Variable A_eq_dec : forall (a a' : A), {a = a'} + {a <> a'}.

Lemma count_occ_app_split : 
  forall l l' (a : A),
    count_occ A_eq_dec (l ++ l') a = count_occ A_eq_dec l a + count_occ A_eq_dec l' a.
Proof.
elim => //.
move => a' l IH l' a.
rewrite /=.
case A_eq_dec => H_dec; first by rewrite IH.
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

End ListProps.

Section OrderedAuxMultiParams.

Context `{multi_params : MultiParams}.

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

End OrderedAuxMultiParams.

Section OrderedAuxNameOverlayParams.

Context `{overlay_params : NameOverlayParams}.

Lemma collate_msg_for_not_adjacent :
  forall m n h ns f,
    ~ adjacent_to h n ->
    collate h f (msg_for m (adjacent_to_node h ns)) h n = f h n.
Proof.
move => m n h ns f H_adj.
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

Lemma collate_msg_for_notin_exclude :
  forall m n h ns f failed,
    ~ In n ns ->
    collate h f (msg_for m (adjacent_to_node h (exclude failed ns))) h n = f h n.
Proof.
move => m n h ns f failed H_in.
apply: collate_msg_for_notin.
move => H_ex.
by apply exclude_in in H_ex.
Qed.

Lemma collate_msg_for_live_adjacent :
  forall m n h ns f failed,
    ~ In n failed ->
    adjacent_to h n ->
    In n ns ->
    NoDup ns ->
    collate h f (msg_for m (adjacent_to_node h (exclude failed ns))) h n = f h n ++ [m].
Proof.
move => m n h ns f failed H_in H_adj.
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
  rewrite collate_msg_for_notin_exclude //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.
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

End OrderedAuxNameOverlayParams.
