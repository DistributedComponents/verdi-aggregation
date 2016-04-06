Require Import Verdi.
Require Import HandlerMonad.
Require Import StructTact.Fin.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Require Import OrderedType.

Module Type NameType.
Parameter name : Type.
Parameter name_eq_dec : forall x y : name, {x = y} + {x <> y}.
Parameter nodes : list name.
Parameter all_names_nodes : forall x, In x nodes.
Parameter no_dup_nodes : NoDup nodes.
End NameType.

Module Type FinNameType (Import N : NatValue) <: NameType.
Definition name := fin n.
Definition name_eq_dec := fin_eq_dec n.
Parameter nodes : list (fin n).
Parameter all_names_nodes : forall x, In x nodes.
Parameter no_dup_nodes : NoDup nodes.
End FinNameType.

Module FinName (Import N : NatValue) <: FinNameType N.
Definition name := fin n.
Definition name_eq_dec := fin_eq_dec n.
Definition nodes := all_fin n.
Definition all_names_nodes := all_fin_all n.
Definition no_dup_nodes := all_fin_NoDup n.
End FinName.

Module Type NameOrderedTypeCompat (Import NT : NameType) <: OrderedType.
Definition t := name.
Definition eq := eq (A := name).
Parameter lt : name -> name -> Prop.
Definition eq_refl := eq_refl (A := name).
Definition eq_sym := eq_sym (A := name).
Definition eq_trans := eq_trans (A := name).
Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Parameter compare : forall x y : t, Compare lt eq x y.
Definition eq_dec := name_eq_dec.
End NameOrderedTypeCompat.

Module FinNameOrderedTypeCompat (N : NatValue) (FN : FinNameType N) <: NameOrderedTypeCompat FN := fin_OT_compat N.

Require Import MSetInterface.

Module Type NameOrderedType (Import NT : NameType) <: OrderedType.
Definition t := name.
Definition eq := eq (A := name).
Definition eq_equiv := eq_equivalence (A := name).
Parameter lt : name -> name -> Prop.
Parameter lt_strorder : StrictOrder lt.
Parameter lt_compat : Proper (eq==>eq==>iff) lt.
Parameter compare : forall x y : name, comparison.
Parameter compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Definition eq_dec := name_eq_dec.
End NameOrderedType.

Module FinNameOrderedType (N : NatValue) (FN : FinNameType N) <: NameOrderedType FN := fin_OT N.

Module Type RootNameType (Import NT : NameType).
Parameter root : name -> Prop.
Parameter root_dec : forall n, {root n} + {~ root n}.
Parameter root_unique : forall n n', root n -> root n' -> n = n'.
End RootNameType.

Module FinRootNameType (Import N : NatValue) (FN : FinNameType N) <: RootNameType FN.
Definition root (x : fin n) := fin_to_nat x = 1.
Definition root_dec (x : fin n) := Nat.eq_dec (fin_to_nat x) 1.
Lemma root_unique : forall x y, root x -> root y -> x = y.
Proof.
move => x y.
rewrite /root.
move => H_x H_y.
case (fin_compare n x y) => H_lt //.
- rewrite /fin_lt in H_lt.
  rewrite H_x H_y in H_lt.
  contradict H_lt.
  by auto with arith.
- rewrite /fin_lt in H_lt.
  rewrite H_x H_y in H_lt.
  contradict H_lt.
  by auto with arith.
Qed.
End FinRootNameType.

Module Type AdjacentNameType (Import NT : NameType).
Parameter adjacent_to : relation name.
Parameter adjacent_to_dec : forall x y : name, {adjacent_to x y} + {~ adjacent_to x y}.
Parameter adjacent_to_symmetric : Symmetric adjacent_to.
Parameter adjacent_to_irreflexive : Irreflexive adjacent_to.
End AdjacentNameType.

Inductive fin_complete (n : nat) : fin n -> fin n -> Prop :=
| fin_complete_neq : forall x y, x <> y -> fin_complete n x y.

Definition fin_complete_dec : forall n (x y : fin n), {fin_complete n x y} + {~ fin_complete n x y }.
move => n x y.
case (fin_eq_dec n x y) => H_eq.
  rewrite H_eq.
  right.
  move => H_r.
  by inversion H_r.
left.
exact: fin_complete_neq.
Defined.

Lemma fin_complete_Symmetric : forall n, Symmetric (fin_complete n).
Proof.
rewrite /Symmetric.
move => n x y H_r.
inversion H_r; subst.
apply: fin_complete_neq.
move => H_eq.
by rewrite H_eq in H.
Qed.

Lemma fin_complete_Irreflexive : forall n, Irreflexive (fin_complete n).
Proof.
rewrite /Irreflexive /Reflexive /complement.
move => n x H_x.
by inversion H_x.
Qed.

Module FinCompleteAdjacentNameType (Import N : NatValue) (FN : FinNameType N) <: AdjacentNameType FN.
Definition adjacent_to := fin_complete n.
Definition adjacent_to_dec := fin_complete_dec n.
Definition adjacent_to_symmetric := fin_complete_Symmetric n.
Definition adjacent_to_irreflexive := fin_complete_Irreflexive n.
End FinCompleteAdjacentNameType.

Module Adjacency (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (Import ANT : AdjacentNameType NT).

Definition NS := NSet.t.

Instance NT_NameParams : NameParams :=
  {
    name := name ;
    name_eq_dec := name_eq_dec ;
    nodes := nodes ;
    all_names_nodes := all_names_nodes ;
    no_dup_nodes := no_dup_nodes
  }.

Instance ANT_NameOverlayParams : NameOverlayParams NT_NameParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Lemma adjacent_to_node_adjacent_to : 
  forall n n' ns,
  In n' (adjacent_to_node n ns) -> In n' ns /\ adjacent_to n n'.
Proof.
move => n n' ns H_in.
rewrite /adjacent_to_node in H_in.
apply filter_In in H_in.
move: H_in => [H_in H_eq].
split => //.
move: H_eq.
by case adjacent_to_dec.
Qed.

Lemma adjacent_to_adjacent_to_node : 
  forall n n' ns,
    In n' ns -> 
    adjacent_to n n' ->
    In n' (adjacent_to_node n ns).
Proof.
move => n n' ns H_in H_adj.
apply filter_In.
split => //.
by case adjacent_to_dec.
Qed.

Definition adjacency (n : name) (ns : list name) : NS :=
  fold_right (fun n' fs => NSet.add n' fs) NSet.empty (adjacent_to_node n ns).

Lemma adjacent_to_node_adjacency : 
  forall n n' ns, 
    In n' (adjacent_to_node n ns) <-> NSet.In n' (adjacency n ns).
Proof.
move => n n' ns.
split.
elim: ns => //=.
move => n0 ns IH.
rewrite /adjacency /= /is_left.
case adjacent_to_dec => H_dec /= H_in; last exact: IH.
case: H_in => H_in.
  rewrite H_in.
  apply NSet.add_spec.
  by left.
apply NSet.add_spec.
right.
exact: IH.
elim: ns => //=; first by rewrite /adjacency /=; exact: NSet.empty_spec.
move => n0 ns IH.
rewrite /adjacency /=.
rewrite /is_left.
case adjacent_to_dec => H_dec /= H_ins; last exact: IH.
apply NSet.add_spec in H_ins.
case: H_ins => H_ins; first by left.
right.
exact: IH.
Qed.

Lemma not_adjacent_self : 
  forall n ns, ~ NSet.In n (adjacency n ns).
Proof.
move => n ns H_ins.
apply adjacent_to_node_adjacency in H_ins.
apply adjacent_to_node_adjacent_to in H_ins.
move: H_ins => [H_in H_adj].
contradict H_adj.
exact: adjacent_to_irreflexive.
Qed.

Lemma adjacency_mutual_in : 
  forall n n' ns,
  In n' ns ->
  NSet.In n (adjacency n' ns) -> 
  NSet.In n' (adjacency n ns).
Proof.
move => n n' ns H_in H_ins.
apply adjacent_to_node_adjacency.
apply adjacent_to_node_adjacency in H_ins.
apply adjacent_to_node_adjacent_to in H_ins.
move: H_ins => [H_in' H_adj].
apply adjacent_to_symmetric in H_adj.
exact: adjacent_to_adjacent_to_node.
Qed.

Lemma adjacency_mutual : forall (n n' : name), NSet.In n (adjacency n' nodes) -> NSet.In n' (adjacency n nodes).
Proof.
move => n n' H_ins.
have H_in: In n' nodes by exact: all_names_nodes.
exact: adjacency_mutual_in.
Qed.

End Adjacency.

(*
Module N3 : NatValue. Definition n := 3. End N3.
Module FN_N3 : FinNameType N3 := FinName N3.
Module NOT_N3 : NameOrderedType FN_N3 := FinNameOrderedType N3 FN_N3.
Module ANC_N3 := FinCompleteAdjacentNameType N3 FN_N3.
Require Import MSetList.
Module N3Set <: MSetInterface.S := MSetList.Make NOT_N3.
Module A := Adjacency FN_N3 NOT_N3 N3Set ANC_N3.
*)
