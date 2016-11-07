Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.

Require Import NameAdjacency.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import Sumbool.

Require Import AggregationDefinitions.
Require Import AggregationAux.

Require Import AAC_tactics.AAC.

Module SingleAggregator (Import NT : NameType)
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import CFG : CommutativeFinGroup) (Import ANT : AdjacentNameType NT) (Import A : Adjacency NT NOT NSet ANT).

Module AX := AAux NT NOT NSet NOTC NMap CFG ANT.
Import AX.AD.
Import AX.

Import GroupScope.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Inductive Input : Type :=
| Aggregate : name -> m -> Input
| Fail : name -> Input
| Local : m -> Input
| SendAggregate : name -> Input
| AggregateRequest : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
- exact: m_eq_dec.
- exact: name_eq_dec.
- exact: name_eq_dec.
- exact: m_eq_dec.
- exact: name_eq_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : m -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Record Data := mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : NS ; 
  balance : NM
}.

Definition InitData (n : name) :=
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     balance := init_map (adjacency n nodes) |}.

Definition Handler (S : Type) := GenHandler unit S Output unit.

Definition IOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Aggregate src m_inp =>  
  when (NSet.mem src st.(adjacent))
  (match NMap.find src st.(balance) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_inp ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_inp)^-1) st.(balance) |}
  end)
| Fail src =>
  when (NSet.mem src st.(adjacent))
  (match NMap.find src st.(balance) with
  | Some m_bal =>
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_bal ;
           adjacent := NSet.remove src st.(adjacent) ;
           balance := NMap.remove src st.(balance) |}
  | None => nop
  end)
| Local m_inp =>
  put {| local := m_inp ;
         aggregate := st.(aggregate) * m_inp * st.(local)^-1 ;
         adjacent := st.(adjacent) ;
         balance := st.(balance) |}
| AggregateRequest =>  
  write_output (AggregateResponse st.(aggregate))
| SendAggregate dst =>
  when (NSet.mem dst st.(adjacent) && sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match NMap.find dst st.(balance) with
   | None => nop
   | Some m_dst =>
     put {| local := st.(local) ;
            aggregate := 1 ;
            adjacent := st.(adjacent) ;
            balance := NMap.add dst (m_dst * st.(aggregate)) st.(balance) |}
   end)
end.

Instance Aggregator_BaseParams : BaseParams := 
  {
    data := Data ;
    input := Input ;
    output := Output
  }.

Instance Aggregator_SingleParams (n : name) : SingleParams Aggregator_BaseParams :=
  {
    init_handler := InitData n;
    input_handler := fun i d => runGenHandler1_ignore (IOHandler i) d
  }.

Lemma IOHandler_cases :
  forall i st u out st' ms,
      IOHandler i st = (u, out, st', ms) ->
      (exists m_inp m_src src, i = Aggregate src m_inp /\ NSet.In src st.(adjacent) /\ NMap.find src st.(balance) = Some m_src /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) * m_inp /\
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = NMap.add src (m_src * (m_inp)^-1) st.(balance) /\
       out = []) \/
      (exists m_inp src, i = Aggregate src m_inp /\ NSet.In src st.(adjacent) /\ NMap.find src st.(balance) = None /\ 
       st' = st /\ out = []) \/
      (exists m_inp src, i = Aggregate src m_inp /\ ~ NSet.In src st.(adjacent) /\
       st' = st /\ out = []) \/
      (exists m_bal src, i = Fail src /\ NSet.In src st.(adjacent) /\ NMap.find src st.(balance) = Some m_bal /\
       st'.(local) = st.(local) /\ 
       st'.(aggregate) = st.(aggregate) * m_bal /\
       st'.(adjacent) = NSet.remove src st.(adjacent) /\
       st'.(balance) = NMap.remove src st.(balance) /\
       out = []) \/
      (exists src, i = Fail src /\ NSet.In src st.(adjacent) /\ NMap.find src st.(balance) = None /\
       st' = st /\ out = []) \/
      (exists src, i = Fail src /\ ~ NSet.In src st.(adjacent) /\
       st' = st /\ out = []) \/
      (exists m_inp, i = Local m_inp /\ 
       st'.(local) = m_inp /\ 
       st'.(aggregate) = st.(aggregate) * m_inp * st.(local)^-1 /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = st.(balance) /\
       out = []) \/
      (exists dst m', i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(balance) = Some m' /\
         st'.(local) = st.(local) /\ 
         st'.(aggregate) = 1 /\
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = NMap.add dst (m' * st.(aggregate)) st.(balance) /\
         out = []) \/
      (exists dst, i = SendAggregate dst /\ NSet.In dst st.(adjacent) /\ st.(aggregate) <> 1 /\ NMap.find dst st.(balance) = None /\
         st' = st /\
         out = []) \/
      (exists dst, i = SendAggregate dst /\ ~ NSet.In dst st.(adjacent) /\ 
         st' = st /\ 
         out = []) \/
      (exists dst, i = SendAggregate dst /\ st.(aggregate) = 1 /\
         st' = st /\ 
         out = []) \/
      (i = AggregateRequest /\ st' = st /\ out = [AggregateResponse (aggregate st)]).
Proof.
move => i st u out st' ms.
rewrite /IOHandler.
case: i => [src m_inp|src|m_inp|dst|]; monad_unfold.
- move => H_eq.
  repeat break_match; repeat tuple_inversion.
  * find_apply_lem_hyp NSetFacts.mem_2.
    left => /=.
    by exists m_inp; exists a; exists src.
  * find_apply_lem_hyp NSetFacts.mem_2.
    right; left => /=.
    by exists m_inp; exists src.
  * have H_ins: ~ NSet.In src st'.(adjacent) by move => H_ins; find_apply_lem_hyp NSetFacts.mem_1; eauto.
    right; right; left.
    by exists m_inp; exists src.
- move => H_eq.
  repeat break_match; repeat tuple_inversion.
  * find_apply_lem_hyp NSetFacts.mem_2.
    right; right; right; left => /=.
    by exists a; exists src.
  * find_apply_lem_hyp NSetFacts.mem_2.
    right; right; right; right; left => /=.
    by exists src.
  * have H_ins: ~ NSet.In src st'.(adjacent) by move => H_ins; find_apply_lem_hyp NSetFacts.mem_1; eauto.
    right; right; right; right; right; left => /=.
    by exists src.
- move => H_eq.
  repeat tuple_inversion.
  right; right; right; right; right; right; left => /=.
  by exists m_inp.
- repeat break_let; break_if; first (repeat break_let; break_match).
  * move => H_eq.
    move/andP: Heqb => /= [H_mem H_neq].
    repeat tuple_inversion.
    rewrite /sumbool_not in H_neq.
    break_match => //.
    find_apply_lem_hyp NSetFacts.mem_2.
    right; right; right; right; right; right; right; left => /=.
    by exists dst; exists a.
  * move => H_eq.
    move/andP: Heqb => /= [H_mem H_neq].
    repeat tuple_inversion.
    rewrite /sumbool_not in H_neq.
    break_match => //.
    find_apply_lem_hyp NSetFacts.mem_2.
    right; right; right; right; right; right; right; right; left => /=.
    by exists dst.
  * move => H_eq.
    move/nandP: Heqb => /= Heqb.
    repeat tuple_inversion.
    break_or_hyp.
      move/negP: H => H.
      have H_ins: ~ NSet.In dst st'.(adjacent) by move => H_ins; find_apply_lem_hyp NSetFacts.mem_1.
      right; right; right; right; right; right; right; right; right; left => /=.
      by exists dst.
    unfold sumbool_not in *.
    break_match => //.
    right; right; right; right; right; right; right; right; right; right; left => /=.
    by exists dst.
- move => H_eq.
  tuple_inversion.
  by right; right; right; right; right; right; right; right; right; right; right.
Qed.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Definition conserves_node_mass (d : data) : Prop := 
d.(local) = d.(aggregate) * sumM d.(adjacent) d.(balance).

Lemma Aggregator_conserves_node_mass : 
 forall n st tr, @step_s_star _ (Aggregator_SingleParams n) (@init_handler _ (Aggregator_SingleParams n))  st tr ->
  conserves_node_mass st.
Proof.
move => n st tr H_st.
remember init_handler as y in *.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => H_init.
  rewrite H_init /conserves_node_mass /InitData; gsimpl.
  rewrite /init_handler /=.
  by rewrite sumM_init_map_1.
concludes.
match goal with
| [ H : step_s _ _ _ |- _ ] => invc H
end; simpl.
rewrite /init_handler /= /runGenHandler1_ignore /= in H0.
repeat break_let.
repeat tuple_inversion.
io_handler_cases; unfold conserves_node_mass in *; simpl in * => //.
- repeat find_rewrite.
  rewrite sumM_add_map //; gsimpl.
  set m1 := aggregate _.
  set m2 := sumM _ _.
  suff H_suff: m1 * x * m2 * x^-1 = m1 * m2 * (x * x^-1) by rewrite H_suff; gsimpl.
  by aac_reflexivity.
- repeat find_rewrite.
  rewrite (sumM_remove_remove H H1); gsimpl.
  set m1 := aggregate _.
  set m2 := sumM _ _.
  suff H_suff: m1 * x * m2 * x^-1 = m1 * m2 * (x * x^-1) by rewrite H_suff; gsimpl.
  by aac_reflexivity.
- repeat find_rewrite.
  gsimpl.
  set m0 := local _.
  set m1 := aggregate _.
  set m2 := sumM _ _.
  set rhs := _ * _.
  suff H_suff: rhs = m0 * (m1 * m1^-1) * (m2 * m2^-1) by rewrite H_suff; gsimpl.
  rewrite /rhs.
  by aac_reflexivity.
- repeat find_rewrite.
  rewrite sumM_add_map //.
  gsimpl.
  by aac_reflexivity.
Qed.

End SingleAggregator.
