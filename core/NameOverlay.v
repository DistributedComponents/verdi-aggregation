Require Import Verdi.
Require Import HandlerMonad.
Require Import StructTact.Fin.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Require Import MSetList.
Require Import FMapList.

Module Adjacency (N : NatValue).

Module fin_n_OT := fin_OT N.
Module FinNSet <: MSetInterface.S := MSetList.Make fin_n_OT.
Definition FinNS := FinNSet.t.

Module fin_n_OT_compat := fin_OT_compat N.
Module FinNMap <: FMapInterface.S := FMapList.Make fin_n_OT_compat.

Instance Fin_n_NameParams : NameParams :=
  { 
    name := fin N.n ;
    name_eq_dec := fin_eq_dec N.n ;
    nodes := all_fin N.n ;
    all_names_nodes := all_fin_all N.n ;
    no_dup_nodes := all_fin_NoDup N.n
  }.

Section Adjacent.

  Context {fin_nop : NameOverlayParams Fin_n_NameParams}.

  Definition adjacent_to_node (n : name) := 
  filter (adjacent_to_dec n).

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

  Definition adjacency (n : name) (ns : list name) : FinNS :=
  fold_right (fun n' fs => FinNSet.add n' fs) FinNSet.empty (adjacent_to_node n ns).

  Lemma adjacent_to_node_adjacency : 
    forall n n' ns, 
      In n' (adjacent_to_node n ns) <-> FinNSet.In n' (adjacency n ns).
  Proof.
  move => n n' ns.
  split.
  elim: ns => //=.
  move => n0 ns IH.
  rewrite /adjacency /= /is_left.
  case adjacent_to_dec => H_dec /= H_in; last exact: IH.
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
  case adjacent_to_dec => H_dec /= H_ins; last exact: IH.
  apply FinNSet.add_spec in H_ins.
  case: H_ins => H_ins; first by left.
  right.
  exact: IH.
  Qed.

  Lemma not_adjacent_self : 
    forall n ns, ~ FinNSet.In n (adjacency n ns).
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
    FinNSet.In n (adjacency n' ns) -> 
    FinNSet.In n' (adjacency n ns).
  Proof.
  move => n n' ns H_in H_ins.
  apply adjacent_to_node_adjacency.
  apply adjacent_to_node_adjacency in H_ins.
  apply adjacent_to_node_adjacent_to in H_ins.
  move: H_ins => [H_in' H_adj].
  apply adjacent_to_symmetric in H_adj.
  exact: adjacent_to_adjacent_to_node.
  Qed.

  Lemma adjacency_mutual : forall (n n' : name), FinNSet.In n (adjacency n' nodes) -> FinNSet.In n' (adjacency n nodes).
  Proof.
  move => n n' H_ins.
  have H_in: In n' nodes by exact: all_names_nodes.
  exact: adjacency_mutual_in.
  Qed.

End Adjacent.

End Adjacency.
