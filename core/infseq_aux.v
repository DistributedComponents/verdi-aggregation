Require Import infseq.
Require Import Classical.
Require Import mathcomp.ssreflect.ssreflect.

Section Aux.

Context {T : Type}.

Definition neg_tl (P : infseq T -> Prop) : infseq T -> Prop := fun s => ~ P s.

Lemma P_or_neg_tl_P : forall (P : infseq T -> Prop) (s : infseq T),
  P s \/ (neg_tl P) s.
Proof.
move => P s.
exact: classic.
Qed.

Lemma neg_tl_neg : forall (P : infseq T -> Prop) (s : infseq T),
  neg_tl P s -> ~ P s.
Proof.
move => P; case => e s.
by move => H_neg H_p.
Qed.

Lemma not_eventually_neg_then_always : forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually (neg_tl P) s ->
  always P s.
Proof.
move => P.
cofix c.
case => e s H_al.
apply: Always.
  case (P_or_neg_tl_P P (Cons e s)) => H_or //.
  by apply (E0 _ (neg_tl P)) in H_or.
apply: c.
move => /= H_ev.
case: H_al.
exact: E_next.
Qed.

Lemma eventually_always_two_both : forall (P Q : infseq T -> Prop) (s : infseq T),
  eventually (always P) s ->
  eventually (always Q) s ->
  eventually (always (P /\_ Q)) s.
Proof.
move => P q s.
elim => {s}.
  move => s H_al H_ev.
  elim: H_ev H_al => {s}.
    move => s H_al H_al'.
    apply: E0.
    move: s H_al H_al'.
    cofix c.
    case => T5 s H_al H_al'.
    inversion H_al; subst.
    inversion H_al'; subst.
    apply Always; first by split.
    exact: c.
  move => e s H_ev IH H_al.
  apply: E_next.
  apply IH.
  by inversion H_al.  
move => e s H_al IH H_ev.
apply E_next.
apply: IH.
inversion H_ev; subst => //.
inversion H; subst.
exact: E0.
Qed.

Lemma not_always_then_eventually_neg : forall (P : infseq T -> Prop) (s : infseq T),
  ~ (always P s) ->
  eventually (neg_tl P) s.
Proof.
move => P s H_al.
set Q := eventually _.
case (P_or_neg_tl_P Q s) => //.
rewrite /Q {Q} => H_neg.
apply neg_tl_neg in H_neg.
by apply not_eventually_neg_then_always in H_neg.
Qed.

Lemma not_eventually_then_always_neg : forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually P s ->
  always (neg_tl P) s.
Proof.
move => P.
cofix c.
case => e s H_al.
apply: Always.
  case (P_or_neg_tl_P P (Cons e s)) => H_or //.
  by apply (E0 _ P) in H_or.
apply: c.
move => /= H_ev.
case: H_al.
exact: E_next.
Qed.

Lemma not_always_eventually_then_eventually_always_not : forall (P : infseq T -> Prop) (s : infseq T),
  ~ (always (eventually P) s) -> eventually (always (neg_tl P)) s.
Proof.
move => P s H_al.
apply not_always_then_eventually_neg in H_al.
elim: H_al => {s}.
  move => s H_neg.
  apply neg_tl_neg in H_neg.
  apply not_eventually_then_always_neg in H_neg.
  exact: E0.
move => e s H_ev H_ev'.
exact: E_next.
Qed.

Lemma eventually_always_not_then_not_always_eventually : forall (P : infseq T -> Prop) (s : infseq T),
  eventually (always (neg_tl P)) s ->
  ~ (always (eventually P) s).
Proof.
move => P s.
elim => {s}.
  case => T5 s H_al H_al'.
  inversion H_al'; subst.
  elim: H H_al.
    move => s0 H_P H_al.
    by inversion H_al.    
  move => e s0 H_ev H_al H_al''.
  by inversion H_al''.
move => e s H_al H_al' H_al''.
by inversion H_al''.
Qed.

Lemma eventually_always_neg_and_or : forall (P Q : infseq T -> Prop) (s : infseq T),
  eventually (always ((neg_tl P) /\_ (neg_tl Q))) s ->
  eventually (always (neg_tl (P \/_ Q))) s.
Proof.
move => P Q.
apply: eventually_monotonic_simple.
apply: always_monotonic.
move => s H_neg H_neg'.
case: H_neg' => H_neg'.
  by case: H_neg => H_neg1 H_neg2.
by case: H_neg => H_neg1 H_neg2.
Qed.

Lemma eventually_always_neg_and_or_many : forall (P Q R : infseq T -> Prop) (s : infseq T),
  eventually (always ((neg_tl P) /\_ (neg_tl Q) /\_ R)) s ->
  eventually (always ((neg_tl (P \/_ Q)) /\_ R)) s.
Proof.
move => P Q R.
apply: eventually_monotonic_simple.
apply: always_monotonic.
move => s H_neg.
move: H_neg => [H_P [H_Q H_R]].
split => //.
move => H_neg.
by case: H_neg.
Qed.

Lemma eventually_always_and_comm : forall (P Q : infseq T -> Prop) (s : infseq T),
  eventually (always (P /\_ Q)) s ->
  eventually (always (Q /\_ P)) s.
Proof.
move => P Q.
apply: eventually_monotonic_simple.
apply: always_monotonic.
move => s [H_P H_Q].
by split.
Qed.

Lemma eventually_always_and_assoc : forall (P Q R : infseq T -> Prop) (s : infseq T),
  eventually (always ((P /\_ Q) /\_ R)) s <->
  eventually (always (P /\_ Q /\_ R)) s.
Proof.
move => P Q R.
split.
  move: s.
  apply: eventually_monotonic_simple.
  apply: always_monotonic.
  by move => s [[H_P H_Q] H_R].
move: s.
apply: eventually_monotonic_simple.
apply: always_monotonic.
by move => s [H_P [H_Q H_R]].
Qed.

Lemma until_always_or_eventually : forall (s : infseq T) (J P : infseq T -> Prop),
  until J P s -> ~ eventually P s -> always J s.
Proof.
move => s J P.
move: s.
cofix c.
case => e s.
move => H_un H_ev.
apply until_Cons in H_un.
case: H_un => H_un.
  case H_ev.
  by constructor.
move: H_un => [H_j H_un].
constructor; first by [].
rewrite /=.
apply: c => //.
move => H_ev'.
case: H_ev.
by constructor 2.
Qed.

End Aux.
