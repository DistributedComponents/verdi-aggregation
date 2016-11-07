Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.
Require Import StructTact.Fin.

Module Type Adjacency (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT)
 (Import ANT : AdjacentNameType NT).

  Definition NS := NSet.t.

  Definition adjacency (n : name) (ns : list name) : NS :=
    fold_right (fun n' fs => NSet.add n' fs) NSet.empty (filter_rel adjacent_to_dec n ns).

  Parameter adjacent_to_node_adjacency : 
  forall n n' ns, In n' (filter_rel adjacent_to_dec n ns) <-> NSet.In n' (adjacency n ns).

  Parameter not_adjacent_self : forall n ns, ~ NSet.In n (adjacency n ns).

  Parameter adjacency_mutual_in : 
    forall n n' ns, In n' ns -> NSet.In n (adjacency n' ns) -> NSet.In n' (adjacency n ns).

  Parameter adjacency_mutual : 
    forall n n', NSet.In n (adjacency n' nodes) -> NSet.In n' (adjacency n nodes).
End Adjacency.

Module NameTypeAdjacency (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT)
 (Import ANT : AdjacentNameType NT) <: Adjacency NT NOT NSet ANT.

  Definition NS := NSet.t.

  Definition adjacency (n : name) (ns : list name) : NS :=
    fold_right (fun n' fs => NSet.add n' fs) NSet.empty (filter_rel adjacent_to_dec n ns).

  Require Import mathcomp.ssreflect.ssreflect.

  Lemma adjacent_to_node_adjacency : 
    forall n n' ns, In n' (filter_rel adjacent_to_dec n ns) <-> NSet.In n' (adjacency n ns).
  Proof.
    move => n n' ns.
    split.
    elim: ns => //=.
    move => n0 ns IH.
    rewrite /adjacency /=.
    case adjacent_to_dec => //= H_dec H_in.
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
      case adjacent_to_dec =>  //= H_dec H_ins.
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
    apply filter_rel_related in H_ins.
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
    apply filter_rel_related in H_ins.
    move: H_ins => [H_in' H_adj].
    apply adjacent_to_symmetric in H_adj.
    exact: related_filter_rel.
  Qed.

  Lemma adjacency_mutual : 
    forall (n n' : name), 
      NSet.In n (adjacency n' nodes) -> 
      NSet.In n' (adjacency n nodes).
  Proof.
    move => n n' H_ins.
    have H_in: In n' nodes by exact: all_names_nodes.
    exact: adjacency_mutual_in.
  Qed.
End NameTypeAdjacency.

Module FinAdjacency (N : NatValue) (FNT : FinNameType N)
 (NOT : NameOrderedType FNT) (NSet : MSetInterface.S with Module E := NOT)
 (ANT : AdjacentNameType FNT) <: Adjacency FNT NOT NSet ANT :=
NameTypeAdjacency FNT NOT NSet ANT.
