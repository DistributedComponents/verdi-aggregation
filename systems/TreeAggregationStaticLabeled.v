Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.PartialExtendedMapSimulations.
Require Import Verdi.TotalMapExecutionSimulations.
Require Import Verdi.PartialMapExecutionSimulations.

Require Import NameAdjacency.
Require Import AggregationDefinitions.
Require Import AggregationAux.
Require Import AggregationStatic.
Require Import TreeAux.
Require Import TreeStaticLabeled.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import InfSeqExt.exteq.
Require Import InfSeqExt.map.

Require Import Sumbool.
Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import AAC_tactics.AAC.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module TreeAggregation (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT)
 (Import CFG : CommutativeFinGroup)
 (Import ANT : AdjacentNameType NT) (Import A : Adjacency NT NOT NSet ANT)
 (Import TA : TAux NT NOT NSet NOTC NMap).

Module AG := Aggregation NT NOT NSet NOTC NMap CFG ANT A.
Import AG.OA.AX.AD.

Module TR := Tree NT NOT NSet NOTC NMap RNT ANT A TA.

Import GroupScope.

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Inductive Msg : Type := 
| Aggregate : m -> Msg
| Fail : Msg
| Level : option lv -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality; first exact: m_eq_dec.
case: o; case: o0.
- move => n m.
  case (lv_eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Inductive Input : Type :=
| Local : m -> Input
| SendAggregate : Input
| AggregateRequest : Input
| LevelRequest : Input
| Broadcast : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : m -> Output
| LevelResponse : option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality; first exact: m_eq_dec.
case: o; case: o0.
- move => n m.
  case (lv_eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Record Data :=  mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : NS ; 
  balance : NM ;
  broadcast : bool ; 
  levels : NL
}.

Definition InitData (n : name) := 
if root_dec n then
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     balance := init_map (adjacency n nodes) ;
     broadcast := true ;
     levels := NMap.empty lv |}
else
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     balance := init_map (adjacency n nodes) ;
     broadcast := false ;
     levels := NMap.empty lv |}.

Inductive Label : Type :=
| Tau : Label
| RecvFail : name -> name -> Label
| RecvLevel : name -> name -> Label
| RecvAggregate : name -> name -> Label
| DeliverBroadcastTrue : name -> Label
| DeliverBroadcastFalse : name -> Label
| DeliverLevelRequest : name -> Label
| DeliverSendAggregate : name -> Label
| DeliverLocal : name -> Label
| DeliverAggregateRequest : name -> Label.

Definition Label_eq_dec : forall x y : Label, {x = y} + {x <> y}.
decide equality; auto using name_eq_dec.
Defined.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output Label.

Definition RootNetHandler (me src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Aggregate m_msg => 
  match NMap.find src st.(balance) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_msg)^-1) st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end ;;
  ret (RecvAggregate me src)
| Level _ => ret (RecvLevel me src)
| Fail =>
  match NMap.find src st.(balance) with
  | Some m_bal =>    
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_bal ;
           adjacent := NSet.remove src st.(adjacent) ;
           balance := NMap.remove src st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  | None =>
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := NSet.remove src st.(adjacent) ;
           balance := st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end ;; 
  ret (RecvFail me src)
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match NMap.find src st.(balance) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_msg)^-1) st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end ;;
  ret (RecvAggregate me src)
| Level None =>
  (if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.remove src st.(levels))) then
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           balance := st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := NMap.remove src st.(levels) |}
  else 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           balance := st.(balance) ;
           broadcast := true ;
           levels := NMap.remove src st.(levels) |}) ;; 
  ret (RecvLevel me src)
| Level (Some lv') =>
  (if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.add src lv' st.(levels))) then
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           balance := st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := NMap.add src lv' st.(levels) |}
  else
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           balance := st.(balance) ;
           broadcast := true ;
           levels := NMap.add src lv' st.(levels) |}) ;; 
  ret (RecvLevel me src)
| Fail => 
  match NMap.find src st.(balance) with
  | Some m_bal =>    
    if olv_eq_dec (level st.(adjacent) st.(levels)) (level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels))) then
      put {| local := st.(local) ;
             aggregate := st.(aggregate) * m_bal ;
             adjacent := NSet.remove src st.(adjacent) ;
             balance := NMap.remove src st.(balance) ;
             broadcast := st.(broadcast) ;
             levels := NMap.remove src st.(levels) |}
    else
      put {| local := st.(local) ;
             aggregate := st.(aggregate) * m_bal ;
             adjacent := NSet.remove src st.(adjacent) ;
             balance := NMap.remove src st.(balance) ;
             broadcast := true ;
             levels := NMap.remove src st.(levels) |}
  | None => 
    if olv_eq_dec (level st.(adjacent) st.(levels)) (level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels))) then
      put {| local := st.(local) ;
             aggregate := st.(aggregate) ;
             adjacent := NSet.remove src st.(adjacent) ;
             balance := st.(balance) ;
             broadcast := st.(broadcast) ;
             levels := NMap.remove src st.(levels) |}
    else
      put {| local := st.(local) ;
             aggregate := st.(aggregate) ;
             adjacent := NSet.remove src st.(adjacent) ;
             balance := st.(balance) ;
             broadcast := true ;
             levels := NMap.remove src st.(levels) |}
  end ;; 
  ret (RecvFail me src)
end.

Definition NetHandler (me src : name) (msg : Msg) : Handler Data :=
if root_dec me then RootNetHandler me src msg 
else NonRootNetHandler me src msg.

Definition send_level_fold (lvo : option lv) (n : name) (res : Handler Data) : Handler Data :=
send (n, Level lvo) ;; res.

Definition send_level_adjacent (lvo : option lv) (fs : NS) : Handler Data :=
NSet.fold (send_level_fold lvo) fs (ret Tau).

Definition RootIOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1;
         adjacent := st.(adjacent);
         balance := st.(balance);
         broadcast := st.(broadcast);
         levels := st.(levels) |}  ;;
  ret (DeliverLocal me)
| SendAggregate => 
  ret (DeliverSendAggregate me)
| AggregateRequest => 
  write_output (AggregateResponse st.(aggregate)) ;;
  ret (DeliverAggregateRequest me)
| Broadcast => 
  if st.(broadcast) then
  (send_level_adjacent (Some 0) st.(adjacent) ;;
   put {| local := st.(local);
          aggregate := st.(aggregate);
          adjacent := st.(adjacent);
          balance := st.(balance);
          broadcast := false;
          levels := st.(levels) |}) ;;
    ret (DeliverBroadcastTrue me)
  else
    ret (DeliverBroadcastFalse me)
| LevelRequest => 
  write_output (LevelResponse (Some 0)) ;;
  ret (DeliverLevelRequest me)
end.

Definition NonRootIOHandler (me : name) (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg; 
         aggregate := st.(aggregate) * m_msg * st.(local)^-1;
         adjacent := st.(adjacent); 
         balance := st.(balance);
         broadcast := st.(broadcast);
         levels := st.(levels) |}  ;;
  ret (DeliverLocal me)
| SendAggregate => 
  when (sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match parent st.(adjacent) st.(levels) with
  | None => nop
  | Some dst => 
    match NMap.find dst st.(balance) with
    | None => nop
    | Some m_dst =>   
      send (dst, (Aggregate st.(aggregate))) ;;
      put {| local := st.(local);
             aggregate := 1;
             adjacent := st.(adjacent);
             balance := NMap.add dst (m_dst * st.(aggregate)) st.(balance);
             broadcast := st.(broadcast);
             levels := st.(levels) |}
    end
  end)  ;;
  ret (DeliverSendAggregate me)
| AggregateRequest => 
  write_output (AggregateResponse st.(aggregate))  ;;
  ret (DeliverAggregateRequest me)
| Broadcast =>
  if st.(broadcast) then
    send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent) ;; 
    put {| local := st.(local);
           aggregate := st.(aggregate);
           adjacent := st.(adjacent);
           balance := st.(balance);
           broadcast := false;
           levels := st.(levels) |}  ;;
    ret (DeliverBroadcastTrue me)
  else
    ret (DeliverBroadcastFalse me)
| LevelRequest =>   
  write_output (LevelResponse (level st.(adjacent) st.(levels))) ;;
  ret (DeliverLevelRequest me)
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler me i 
else NonRootIOHandler me i.

Instance TreeAggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance TreeAggregation_LabeledMultiParams : LabeledMultiParams TreeAggregation_BaseParams :=
  {
    lb_name := name ;
    lb_msg  := Msg ;
    lb_msg_eq_dec := Msg_eq_dec ;
    lb_name_eq_dec := name_eq_dec ;
    lb_nodes := nodes ;
    lb_all_names_nodes := all_names_nodes ;
    lb_no_dup_nodes := no_dup_nodes ;
    label := Label ;
    label_silent := Tau ;
    lb_init_handlers := InitData ;
    lb_net_handlers := fun dst src msg s =>
                        runGenHandler s (NetHandler dst src msg) ;
    lb_input_handlers := fun nm msg s =>
                        runGenHandler s (IOHandler nm msg)
  }.

Instance TreeAggregation_MultiParams : MultiParams TreeAggregation_BaseParams := unlabeled_multi_params.

Instance TreeAggregation_NameOverlayParams : NameOverlayParams TreeAggregation_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance TreeAggregation_FailMsgParams : FailMsgParams TreeAggregation_MultiParams :=
  {
    msg_fail := Fail
  }.

Lemma net_handlers_NetHandler :
  forall dst src m st os st' ms,
    net_handlers dst src m st = (os, st', ms) ->
    exists lb, NetHandler dst src m st = (lb, os, st', ms).
Proof.
intros.
simpl in *.
unfold unlabeled_net_handlers, lb_net_handlers in *.
simpl in *.
repeat break_let.
find_inversion.
by exists l0; auto.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st lb out st' ms,
    NetHandler dst src msg st = (lb, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ lb = RecvAggregate dst src /\ NMap.find src st.(balance) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = NMap.add src (m_src * (m_msg)^-1) st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ lb = RecvAggregate dst src /\ NMap.find src st.(balance) = None /\ 
     st' = st /\ 
     out = [] /\ ms = []) \/
    (root dst /\ msg = Fail /\ lb = RecvFail dst src /\ exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\
     exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\
     exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ msg = Fail /\ lb = RecvFail dst src /\ NMap.find src st.(balance) = None /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\ NMap.find src st.(balance) = None /\
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ lb = RecvFail dst src /\ NMap.find src st.(balance) = None /\
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ lb = RecvLevel dst src /\
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\ lb = RecvLevel dst src /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg => [m_msg||olv_msg]; monad_unfold; case root_dec => /= H_dec; repeat break_let; repeat find_injection; try (break_match; repeat find_injection); try (break_if; repeat find_injection).
- by left; exists m_msg, a.
- by right; left; exists m_msg.
- by left; exists m_msg, a.
- by right; left; exists m_msg.
- right; right; left.
  repeat split => //.
  by exists a.
- by right; right; right; right; right; left.
- right; right; right; left.
  repeat split => //.
  exists a.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; left.
  repeat split => //.
  exists a.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; right; right; left.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; right; right; right; left.
  move: Heqb.
  by case: olv_eq_dec.
- move => ms0 H_eq.
  find_injection.
  right; right; right; right; right; right; right; right; left.
  split => //.
  by exists olv_msg.
- right; right; right; right; right; right; right; right; right; left.
  split => //.
  exists l2.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; left.
  split => //.
  exists l2.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; right; left.
  move: Heqb.
  by case: olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; right; right.
  move: Heqb.
  by case: olv_eq_dec.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    exists lb, IOHandler h i d = (lb, os, d', ms).
Proof.
intros.
simpl in *.
unfold unlabeled_input_handlers, lb_input_handlers in *.
simpl in *.
repeat break_let.
find_inversion.
by exists l0; auto.
Qed.

Lemma send_level_fold_app :
  forall ns st olv nm lb,
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (lb, [], s, nm)) st) = 
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (lb, [], s, [])) st) ++ nm.
Proof.
elim => //=.
move => n ns IH st olv nm lb.
rewrite {1}/send_level_fold /=.
monad_unfold.
rewrite /=.
rewrite IH.
rewrite app_assoc.
by rewrite -IH.
Qed.

Instance TreeAggregation_TreeMsg : TreeMsg := 
  {
    tree_msg := Msg ;
    tree_level := Level
  }.

Lemma send_level_adjacent_fst_eq : 
forall fs olv st,
  snd (send_level_adjacent olv fs st) = level_adjacent olv fs.
Proof.
move => fs olv st.
rewrite /send_level_adjacent /level_adjacent.
rewrite 2!NSet.fold_spec.
move: olv st.
elim: NSet.elements => [|n ns IH] //=.
move => olv st.
rewrite {2}/level_fold {2}/send_level_fold.
rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg).
have IH' := IH olv st.
rewrite -IH'.
monad_unfold.
by rewrite -send_level_fold_app.
Qed.

Lemma fst_fst_fst_tt_send_level_fold : 
forall ns nm olv st lb,
fst
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st))) = lb.
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma send_level_adjacent_fst_fst_eq : 
forall fs olv st,
  fst (fst (fst (send_level_adjacent olv fs st))) = Tau.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite fst_fst_fst_tt_send_level_fold.
Qed.

Lemma snd_fst_fst_out_send_level_fold : 
forall ns nm olv st lb,
snd
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st))) = [].
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma snd_fst_st_send_level_fold : 
forall ns nm olv st lb,
snd (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (lb, [], s, nm)) st)) = st.
Proof.
elim => //=.
move => n ns IH nm olv st lb.
by rewrite IH.
Qed.

Lemma send_level_adjacent_snd_fst_fst : 
forall fs olv st,
  snd (fst (fst (send_level_adjacent olv fs st))) = [].
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite snd_fst_fst_out_send_level_fold.
Qed.

Lemma send_level_adjacent_snd_fst : 
forall fs olv st,
  snd (fst (send_level_adjacent olv fs st)) = st.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite snd_fst_st_send_level_fold.
Qed.

Lemma send_level_adjacent_eq : 
  forall fs olv st,
  send_level_adjacent olv fs st = (Tau, [], st, level_adjacent olv fs).
Proof.
move => fs olv st.
case H_eq: send_level_adjacent => [[[u o] s b]].
have H_eq'_1 := send_level_adjacent_fst_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_1.
have H_eq'_2 := send_level_adjacent_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_2.
have H_eq'_3 := send_level_adjacent_snd_fst_fst fs olv st.
rewrite H_eq /= in H_eq'_3.
have H_eq'_4 := send_level_adjacent_snd_fst fs olv st.
rewrite H_eq /= in H_eq'_4.
by rewrite H_eq'_1 H_eq'_2 H_eq'_3 H_eq'_4.
Qed.

Lemma IOHandler_cases :
  forall h i st lb out st' ms,
      IOHandler h i st = (lb, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ lb = DeliverLocal h /\
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = st.(balance) /\
         st'.(broadcast) = st.(broadcast) /\
         st'.(levels) = st.(levels) /\
         out = [] /\ ms = []) \/
      (root h /\ i = SendAggregate /\ lb = DeliverSendAggregate h /\
         st' = st /\
         out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ lb = DeliverSendAggregate h /\
       st.(aggregate) <> 1 /\ 
       exists dst m_dst, parent st.(adjacent) st.(levels) = Some dst /\ NMap.find dst st.(balance) = Some m_dst /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = 1 /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = NMap.add dst (m_dst * st.(aggregate)) st.(balance) /\
       st'.(broadcast) = st.(broadcast) /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (~ root h /\ i = SendAggregate /\ lb = DeliverSendAggregate h /\
       st.(aggregate) = 1 /\
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ lb = DeliverSendAggregate h /\
       st.(aggregate) <> 1 /\
       parent st.(adjacent) st.(levels) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ lb = DeliverSendAggregate h /\
       st.(aggregate) <> 1 /\
       exists dst, parent st.(adjacent) st.(levels) = Some dst /\ NMap.find dst st.(balance) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (i = AggregateRequest /\ lb = DeliverAggregateRequest h /\
       st' = st /\ 
       out = [AggregateResponse (aggregate st)] /\ ms = []) \/
      (root h /\ i = Broadcast /\ st.(broadcast) = true /\ lb = DeliverBroadcastTrue h /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = st.(balance) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (Some 0) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\ st.(broadcast) = true /\ lb = DeliverBroadcastTrue h /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = st.(balance) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (i = Broadcast /\ st.(broadcast) = false /\ lb = DeliverBroadcastFalse h /\
       st' = st /\
       out = [] /\ ms = []) \/
      (root h /\ i = LevelRequest /\ lb = DeliverLevelRequest h /\
       st' = st /\
       out = [LevelResponse (Some 0)] /\ ms = []) \/
      (~ root h /\ i = LevelRequest /\ lb = DeliverLevelRequest h /\
       st' = st /\
       out = [LevelResponse (level st.(adjacent) st.(levels))] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler /RootIOHandler /NonRootIOHandler.
case: i => [m_msg||||]; monad_unfold; case root_dec => /= H_dec H_eq; repeat break_let; repeat find_injection; repeat break_match; repeat break_let; repeat find_injection.
- by left; exists m_msg.
- by left; exists m_msg.
- by right; left.
- unfold sumbool_not in *.
  break_match => //.
  right; right; left.
  repeat split => //.
  by exists n, a.
- unfold sumbool_not in *.
  break_match => //.
  right; right; right; right; right; left.
  repeat split => //.
  by exists n.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; right; right; left.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; right; left.
- by right; right; right; right; right; right; left.
- by right; right; right; right; right; right; left.
- by right; right; right; right; right; right; right; right; right; right; left.
- by right; right; right; right; right; right; right; right; right; right; right.
- find_rewrite_lem send_level_adjacent_eq.
  find_injection.
  right; right; right; right; right; right; right; left.
  by rewrite app_nil_l -2!app_nil_end.
- by right; right; right; right; right; right; right; right; right; left.
- find_rewrite_lem send_level_adjacent_eq.
  find_injection.
  right; right; right; right; right; right; right; right; left.
  simpl.
  by rewrite -app_nil_end.
- by right; right; right; right; right; right; right; right; right; left.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Instance TreeAggregation_Aggregation_name_tot_map : MultiParamsNameTotalMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance TreeAggregation_Aggregation_name_tot_map_bijective : MultiParamsNameTotalMapBijective TreeAggregation_Aggregation_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance TreeAggregation_Aggregation_params_pt_msg_map : MultiParamsMsgPartialMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    pt_map_msg := fun m => 
      match m with 
      | Aggregate m' => Some (AG.Aggregate m')
      | Fail => Some AG.Fail      
      | Level _ => None 
      end   
  }.

Instance TreeAggregation_Aggregation_params_pt_ext_map : MultiParamsPartialExtendedMap TreeAggregation_MultiParams AG.Aggregation_MultiParams :=
  {
    pt_ext_map_data := fun d _ => 
      AG.mkData d.(local) d.(aggregate) d.(adjacent) d.(balance) ;
    pt_ext_map_input := fun i n d =>
      match i with 
      | Local m => Some (AG.Local m)
      | SendAggregate => 
        if root_dec n then None else
          match parent d.(adjacent) d.(levels) with
          | Some p => Some (AG.SendAggregate p)
          | None => None
          end
      | AggregateRequest => (Some AG.AggregateRequest)
      | _ => None
      end
  }.

Lemma pt_ext_map_name_msgs_level_adjacent_empty : 
  forall fs lvo,
  pt_map_name_msgs (level_adjacent lvo fs) = [].
Proof.
move => fs lvo.
rewrite /level_adjacent NSet.fold_spec.
elim: NSet.elements => //=.
move => n ns IH.
rewrite {2}/level_fold /=.
rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) /=.
by rewrite pt_map_name_msgs_app_distr /= -app_nil_end IH.
Qed.

Instance TreeAggregation_Aggregation_multi_params_pt_ext_map_congruency : MultiParamsPartialExtendedMapCongruency TreeAggregation_Aggregation_name_tot_map TreeAggregation_Aggregation_params_pt_msg_map TreeAggregation_Aggregation_params_pt_ext_map :=
  {
    pt_ext_init_handlers_eq := _ ;
    pt_ext_net_handlers_some := _ ;
    pt_ext_net_handlers_none := _ ;
    pt_ext_input_handlers_some := _ ;
    pt_ext_input_handlers_none := _ 
  }.
Proof.
- by move => n; rewrite /= /InitData /=; break_if.
- move => me src mg st mg' out st' ps H_eq H_eq'.
  rewrite /pt_ext_mapped_net_handlers.
  repeat break_let.
  rewrite /net_handlers /= /runGenHandler_ignore /= /unlabeled_net_handlers /lb_net_handlers /= /runGenHandler /id in H_eq' Heqp.
  repeat break_let.
  repeat tuple_inversion.
  destruct u, st'.
  by net_handler_cases; AG.net_handler_cases; simpl in *; congruence.
- move => me src mg st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= /unlabeled_net_handlers /lb_net_handlers /= /runGenHandler /id in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  by net_handler_cases; simpl in *; congruence.
- move => me inp st inp' out st' ps H_eq H_eq'.
  rewrite /pt_ext_mapped_input_handlers.
  repeat break_let.
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler /id in H_eq' Heqp.
  repeat break_let.
  repeat tuple_inversion.
  destruct u.
  have H_eq_inp: inp = SendAggregate \/ inp <> SendAggregate by destruct inp; (try by right); left.
  case: H_eq_inp => H_eq_inp.
    subst_max.
    rewrite /= in H_eq.
    move: H_eq.
    case H_p: (parent st.(adjacent) st.(levels)) => [dst|].
      have H_p' := H_p.
      rewrite /parent in H_p'.
      break_match_hyp => //.
      destruct s.
      simpl in *.
      find_injection.
      inversion m0.
      inversion H.
      destruct st'.
      io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; unfold id in *; try congruence.
      move: Heqb.
      by case root_dec.
    by io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; congruence.
  destruct st'.
  simpl in *.
  by io_handler_cases; AG.io_handler_cases; simpl in *; repeat break_match; repeat find_injection; congruence.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler /id in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  io_handler_cases; simpl in *; unfold is_left in *; repeat break_if; try break_match; try congruence.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
Qed.
  
Instance TreeAggregation_Aggregation_fail_msg_params_pt_ext_map_congruency : FailMsgParamsPartialMapCongruency TreeAggregation_FailMsgParams AG.Aggregation_FailMsgParams TreeAggregation_Aggregation_params_pt_msg_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance TreeAggregation_Aggregation_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency TreeAggregation_NameOverlayParams AG.Aggregation_NameOverlayParams TreeAggregation_Aggregation_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem TreeAggregation_Aggregation_pt_ext_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_failure_star _ _ TreeAggregation_NameOverlayParams TreeAggregation_FailMsgParams step_ordered_failure_init (failed, net) tr ->
    exists tr', @step_ordered_failure_star _ _ AG.Aggregation_NameOverlayParams AG.Aggregation_FailMsgParams step_ordered_failure_init (failed, pt_ext_map_onet net) tr'.
Proof.
move => onet failed tr H_st.
apply step_ordered_failure_pt_ext_mapped_simulation_star_1 in H_st.
move: H_st => [tr' H_st].
rewrite map_id in H_st.
by exists tr'.
Qed.

Instance TreeAggregation_Tree_base_params_pt_map : BaseParamsPartialMap TreeAggregation_BaseParams TR.Tree_BaseParams :=
  {
    pt_map_data := fun d => TR.mkData d.(adjacent) d.(broadcast) d.(levels) ;
    pt_map_input := fun i =>
                   match i with
                   | LevelRequest => Some TR.LevelRequest
                   | Broadcast => Some TR.Broadcast
                   | _ => None
                   end ;
    pt_map_output := fun o => 
                    match o with
                    | LevelResponse olv => Some (TR.LevelResponse olv)
                    | _ => None
                    end
  }.

Instance TreeAggregation_Tree_name_tot_map : MultiParamsNameTotalMap TreeAggregation_MultiParams TR.Tree_MultiParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id ;
  }.

Instance TreeAggregation_Tree_name_tot_map_bijective : MultiParamsNameTotalMapBijective TreeAggregation_Tree_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => Logic.eq_refl ;
    tot_map_name_inverse_inv := fun _ => Logic.eq_refl
  }.

Instance TreeAggregation_Tree_multi_params_pt_map : MultiParamsMsgPartialMap TreeAggregation_MultiParams TR.Tree_MultiParams :=
  {
    pt_map_msg := fun m => match m with 
                        | Fail => Some TR.Fail 
                        | Level lvo => Some (TR.Level lvo)
                        | _ => None 
                        end ;
  }.

Instance TreeAggregation_Tree_multi_params_pt_map_congruency : MultiParamsPartialMapCongruency TreeAggregation_Tree_base_params_pt_map TreeAggregation_Tree_name_tot_map TreeAggregation_Tree_multi_params_pt_map :=
  {
    pt_init_handlers_eq := _ ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
- by move => n; rewrite /= /InitData /= /TR.InitData /= /id /=; break_if.
- move => me src mg st mg' H_eq.
  rewrite /pt_mapped_net_handlers.
  repeat break_let.
  case H_n: net_handlers => [[out st'] ps].
  rewrite /net_handlers /= /runGenHandler_ignore /= /unlabeled_net_handlers /lb_net_handlers /= /runGenHandler /id in Heqp H_n.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  by net_handler_cases; TR.net_handler_cases; simpl in *; congruence.
- move => me src mg st out st' ps H_eq H_eq'.
  rewrite /net_handlers /= /runGenHandler_ignore /= /unlabeled_net_handlers /lb_net_handlers /= /runGenHandler /id in H_eq'.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  by net_handler_cases; simpl in *; congruence.
- move => me inp st inp' H_eq.
  rewrite /pt_mapped_input_handlers.
  repeat break_let.  
  case H_i: input_handlers => [[out st'] ps].
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler /id in Heqp H_i.
  repeat break_let.
  repeat tuple_inversion.
  destruct st'.
  io_handler_cases; TR.io_handler_cases; simpl in *; try congruence.
    set ptl := pt_map_name_msgs _.
    set ptl' := level_adjacent _ _.
    suff H_suff: ptl = ptl' by repeat find_rewrite.
    rewrite /ptl /ptl' /level_adjacent 2!NSet.fold_spec.
    elim: NSet.elements => //=.
    move => n ns IH.
    rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) pt_map_name_msgs_app_distr /= /id /=.
    by rewrite (@fold_left_level_fold_eq TR.Tree_TreeMsg) /= IH.
  set ptl := pt_map_name_msgs _.
  set ptl' := level_adjacent _ _.
  suff H_suff: ptl = ptl' by repeat find_rewrite.
  rewrite /ptl /ptl' /level_adjacent 2!NSet.fold_spec.
  elim: NSet.elements => //=.
  move => n ns IH.
  rewrite (@fold_left_level_fold_eq TreeAggregation_TreeMsg) pt_map_name_msgs_app_distr /= /id /=.
  by rewrite (@fold_left_level_fold_eq TR.Tree_TreeMsg) /= IH.
- move => me inp st out st' ps H_eq H_eq'.
  rewrite /= /runGenHandler_ignore /= /unlabeled_input_handlers /lb_input_handlers /= /runGenHandler in H_eq'.
  repeat break_let.  
  repeat tuple_inversion.
  destruct st'.
  by io_handler_cases; simpl in *; congruence.
Qed.

Instance TreeAggregation_Tree_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency TreeAggregation_FailMsgParams TR.Tree_FailMsgParams TreeAggregation_Tree_multi_params_pt_map := 
  {
    pt_fail_msg_fst_snd := Logic.eq_refl
  }.

Instance TreeAggregation_Tree_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency TreeAggregation_NameOverlayParams TR.Tree_NameOverlayParams TreeAggregation_Tree_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

Theorem TreeAggregation_Tree_pt_mapped_simulation_star_1 :
forall net failed tr,
    @step_ordered_failure_star _ _ TreeAggregation_NameOverlayParams TreeAggregation_FailMsgParams step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ TR.Tree_NameOverlayParams TR.Tree_FailMsgParams step_ordered_failure_init (failed, pt_map_onet net) (pt_map_traces tr).
Proof.
move => onet failed tr H_st.
apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
by rewrite map_id in H_st.
Qed.

Instance AggregationData_Data : AggregationData Data :=
  {
    aggr_local := local ;
    aggr_aggregate := aggregate ;
    aggr_adjacent := adjacent ;
    aggr_balance := balance
  }.

Instance AggregationMsg_TreeAggregation : AggregationMsg :=
  {
    aggr_msg := msg ;
    aggr_msg_eq_dec := msg_eq_dec ;
    aggr_fail := Fail ;
    aggr_of := fun mg => match mg with | Aggregate m' => m' | _ => 1 end
  }.

Instance AggregationMsgMap_Aggregation_TreeAggregation : AggregationMsgMap AggregationMsg_TreeAggregation AG.AggregationMsg_Aggregation :=
  {
    map_msgs := pt_map_msgs ;    
  }.
Proof.
- elim => //=.
  case => [m'||olv] ms IH /=.
  * by rewrite /aggregate_sum_fold /= IH.
  * by rewrite /aggregate_sum_fold /= IH.
  * by rewrite /aggregate_sum_fold /= IH; gsimpl.
- elim => //=.
  case => [m'||olv] ms IH /=.
  * by split => H_in; case: H_in => H_in //; right; apply IH.
  * by split => H_in; left.
  * split => H_in; last by right; apply IH.
    case: H_in => H_in //.
    by apply IH.
Defined.

Lemma TreeAggregation_conserves_network_mass : 
  forall onet failed tr,
  step_ordered_failure_star step_ordered_failure_init (failed, onet) tr ->
  conserves_network_mass (remove_all name_eq_dec failed nodes) nodes onet.(onwPackets) onet.(onwState).
Proof.
move => onet failed tr H_st.
have [tr' H_st'] := TreeAggregation_Aggregation_pt_ext_mapped_simulation_star_1 H_st.
have H_inv := AG.Aggregation_conserves_network_mass H_st'.
rewrite /= /id /= /conserves_network_mass in H_inv.
rewrite /conserves_network_mass.
move: H_inv.
set state := fun n : name => _.
set packets := fun src dst : name => _.
rewrite (sum_local_aggr_local_eq _ (onwState onet)) //.
move => H_inv.
rewrite H_inv {H_inv}.
rewrite (sum_aggregate_aggr_aggregate_eq _ (onwState onet)) //.
rewrite sum_aggregate_msg_incoming_active_map_msgs_eq /map_msgs /= -/packets.
rewrite (sum_fail_balance_incoming_active_map_msgs_eq _ state) /map_msgs /= -/packets //.
Qed.

Instance TreeAggregation_Tree_label_tot_map : LabeledMultiParamsLabelTotalMap TreeAggregation_LabeledMultiParams TR.Tree_LabeledMultiParams :=
  {
    tot_map_label := fun lb =>
                      match lb with
                      | Tau => TR.Tau
                      | RecvFail dst src => TR.RecvFail dst src
                      | RecvLevel dst src => TR.RecvLevel dst src
                      | RecvAggregate _ _ => TR.Tau
                      | DeliverBroadcastTrue dst => TR.DeliverBroadcastTrue dst
                      | DeliverBroadcastFalse dst => TR.DeliverBroadcastFalse dst
                      | DeliverLevelRequest dst => TR.DeliverLevelRequest dst
                      | DeliverSendAggregate _ => TR.Tau               
                      | DeliverLocal _ => TR.Tau
                      | DeliverAggregateRequest _ => TR.Tau
                      end
  }.

Instance TreeAggregation_Tree_labeled_partial_map_congruency : LabeledMultiParamsPartialMapCongruency TreeAggregation_Tree_base_params_pt_map TreeAggregation_Tree_name_tot_map TreeAggregation_Tree_multi_params_pt_map TreeAggregation_Tree_label_tot_map :=
  {
    pt_lb_label_silent_fst_snd := Logic.eq_refl ;
    pt_lb_net_handlers_some := _ ;
    pt_lb_net_handlers_none := _ ;
    pt_lb_input_handlers_some := _ ;
    pt_lb_input_handlers_none := _
  }.
Proof.
- move => me src m st m' out st' ps lb H_m H_eq.
  rewrite /lb_net_handlers /= /runGenHandler /= /id /= in H_eq.
  rewrite /tot_mapped_lb_net_handlers_label /= /runGenHandler /=.
  case H_n: NetHandler => [[[lb' out'] st''] ps'].
  by net_handler_cases; TR.net_handler_cases; simpl in *; congruence.
- move => me src m st H_eq.
  rewrite /tot_mapped_lb_net_handlers_label /= /runGenHandler /=.
  case H_n: NetHandler => [[[lb out] st'] ps].
  by net_handler_cases.
- move => me inp st inp' out st' ps lb H_i H_eq.
  rewrite /tot_mapped_lb_input_handlers_label /= /runGenHandler /=.
  case H_inp: IOHandler => [[[lb' out'] st''] ps'].
  rewrite /tot_mapped_lb_input_handlers_label /= /runGenHandler /= /id in H_eq.
  by io_handler_cases; TR.io_handler_cases; simpl in *; congruence.
- move => me inp st H_eq.
  rewrite /tot_mapped_lb_input_handlers_label /= /runGenHandler /=.
  case H_inp: IOHandler => [[[lb' out'] st''] ps'].
  by io_handler_cases.
Qed.

Lemma TreeAggregation_Tree_lb_step_execution_pt_map : forall s,
  lb_step_execution lb_step_ordered_failure s ->
  lb_step_execution lb_step_ordered_failure (map pt_map_onet_event s).
Proof.
apply: lb_step_execution_lb_step_ordered_failure_pt_map_onet_infseq.
exact: TR.Label_eq_dec.
Qed.

Lemma TreeAggregation_Tree_pt_map_onet_hd_step_ordered_failure_star_ex_always : 
  forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) ->
       lb_step_execution lb_step_ordered_failure s ->
       always (now (event_step_star step_ordered_failure step_ordered_failure_init)) (map pt_map_onet_event s).
Proof.
apply: pt_map_onet_hd_step_ordered_failure_star_always.
exact: TR.Label_eq_dec.
Qed.

(*
Lemma TreeAggregation_Tree_enabled :  
  forall l, tot_map_label l <> TR.Tau ->
  forall net net' net0 pt_net failed failed' failed0 pt_failed tr0 tr ptr l',    
    lb_step_ordered_failure (failed, net) l (failed0, net0) tr0 ->
    lb_step_ordered_failure (failed, net) l' (failed', net') tr ->
    lb_step_ordered_failure (List.map tot_map_name failed', pt_map_onet net') (tot_map_label l) (pt_failed, pt_net) ptr ->
    enabled lb_step_ordered_failure l (failed', net').
Proof.
case => //= [dst src|dst src|h|h|h] H_neq net net' net0 pt_net failed failed' failed0 pt_failed tr0 tr ptr l' {H_neq}; rewrite map_id /=.
Admitted.
*)

(* input labels are enabled right away, need to show other's enabledness depend only on message availability *)
(* suffices: if message is incoming, eventually it is the first message *)
(*
Lemma TreeAggregation_Tree_lb_step_ordered_failure_enabled_weak_fairness_pt_map_onet_eventually :
forall l, tot_map_label l <> TR.Tau ->
  forall s, lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  l_enabled lb_step_ordered_failure (tot_map_label l) (pt_map_onet_event (hd s)) ->
  eventually (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
case => //= [dst src|dst src|h|h|h] H_neq {H_neq} s H_exec H_fair H_en.
- by admit.
- by admit.
- destruct s as [[[failed net] l] s].
  apply: E0.
  rewrite /= /l_enabled /=.
  rewrite /= /l_enabled /= map_id /enabled in H_en.
  move: H_en => [[failed' net'] [tr H_st]].
  invcs H_st; unfold runGenHandler, id in *; first by TR.net_handler_cases.
  TR.io_handler_cases => //.
    find_injection.
    simpl in *.
    by admit.
  find_injection.
  simpl in *.
  by admit.
- destruct s as [[[failed net] l] s].
  apply: E0.
  rewrite /= /l_enabled /=.
  rewrite /= /l_enabled /= map_id /enabled in H_en.
  move: H_en => [[failed' net'] [tr H_st]].
  invcs H_st; unfold runGenHandler, id in *; first by TR.net_handler_cases.
  TR.io_handler_cases => //.
  find_injection.
  simpl in *.
  by admit.
- destruct s as [[[failed net] l] s].
  apply: E0.
  rewrite /= /l_enabled /=.
  rewrite /= /l_enabled /= map_id /enabled in H_en.
  move: H_en => [[failed' net'] [tr H_st]].
  invcs H_st; unfold runGenHandler, id in *; first by TR.net_handler_cases.
  TR.io_handler_cases => //.
    find_injection.
    by admit.
  find_injection.
  by admit.
Admitted.
*)

Lemma TreeAggregation_Tree_pt_map_onet_always_weak_local_fairness_continuously :
forall l : label,
  tot_map_label l <> label_silent ->
  forall s : infseq (event (list Net.name * ordered_network) label (Net.name * (input + output))),
  lb_step_execution lb_step_ordered_failure s ->
  weak_local_fairness lb_step_ordered_failure label_silent s ->
  always (now (l_enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) ->
  continuously (now (l_enabled lb_step_ordered_failure l)) s.
Proof.
Admitted.

Lemma TreeAggregation_Tree_pt_map_onet_tot_map_label_event_state_weak_local_fairness : 
  forall s, lb_step_execution lb_step_ordered_failure s ->
       weak_local_fairness lb_step_ordered_failure label_silent s ->
       weak_local_fairness lb_step_ordered_failure label_silent (map pt_map_onet_event s).
Proof.
apply: pt_map_onet_tot_map_label_event_state_weak_local_fairness.
- case.
  * by exists Tau.
  * by move => dst src; exists (RecvFail dst src).
  * by move => dst src; exists (RecvLevel dst src).
  * by move => h; exists (DeliverBroadcastTrue h).
  * by move => h; exists (DeliverBroadcastFalse h).
  * by move => h; exists (DeliverLevelRequest h).
- exact: TreeAggregation_Tree_pt_map_onet_always_weak_local_fairness_continuously.
Qed.

End TreeAggregation.
