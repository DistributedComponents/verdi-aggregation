Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.

Require Import AggregationDefinitions.
Require Import TreeAux.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module TreeAggregation (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import CFG : CommutativeFinGroup) 
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap)
 (Import AD : ADefs NT NOT NSet NOTC NMap CFG).

Import GroupScope.

Inductive Msg : Type := 
| Aggregate : m -> Msg
| Fail : Msg
| Level : option lv -> Msg
| New : Msg.

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
| AggregateRequest : nat -> Input
| LevelRequest : nat -> Input
| Broadcast : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality; auto using Nat.eq_dec, m_eq_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : nat -> m -> Output
| LevelResponse : nat -> option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality; auto using Nat.eq_dec; first exact: m_eq_dec.
case: o; case: o0.
- move => lv0 lv1.
  case (lv_eq_dec lv0 lv1) => H_dec; first by rewrite H_dec; left.
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
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := NSet.empty ;
     balance := NMap.empty m ; 
     broadcast := false ;
     levels := NMap.empty lv |}.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition RootNetHandler (src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Aggregate m_msg => 
  match NMap.find src st.(balance) with
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_msg)^-1) st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  | None => nop
  end
| Level _ => nop 
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
  end
| New =>
  put {| local := st.(local) ;
         aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
         balance := NMap.add src 1 st.(balance) ;
         broadcast := st.(broadcast) ;
         levels := st.(levels) |} ;;
  send (src, Level (Some 0))
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match NMap.find src st.(balance) with
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           balance := NMap.add src (m_src * (m_msg)^-1) st.(balance) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  | None => nop
  end
| Level None =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.remove src st.(levels))) then
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
           levels := NMap.remove src st.(levels) |}
| Level (Some lv') =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (NMap.add src lv' st.(levels))) then
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
           levels := NMap.add src lv' st.(levels) |}
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
  end
| New =>
  put {| local := st.(local) ;
         aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
         balance := NMap.add src 1 st.(balance) ;
         broadcast := st.(broadcast) ;
         levels := st.(levels) |} ;;
  when (sumbool_not _ _ (olv_eq_dec (level st.(adjacent) st.(levels)) None))
    (send (src, Level (level st.(adjacent) st.(levels))))
end.

Definition NetHandler (me src : name) (msg : Msg) : Handler Data :=
if root_dec me then RootNetHandler src msg 
else NonRootNetHandler me src msg.

Definition send_level_fold (lvo : option lv) (n : name) (res : Handler Data) : Handler Data :=
send (n, Level lvo) ;; res.

Definition send_level_adjacent (lvo : option lv) (fs : NS) : Handler Data :=
NSet.fold (send_level_fold lvo) fs nop.

Definition RootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg ;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1 ;
         adjacent := st.(adjacent) ;
         balance := st.(balance) ;
         broadcast := st.(broadcast);
         levels := st.(levels) |}
| SendAggregate => nop
| AggregateRequest client_id => 
  write_output (AggregateResponse client_id st.(aggregate))
| Broadcast => nop  
| LevelRequest client_id => 
  write_output (LevelResponse client_id (Some 0))
end.

Definition NonRootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg; 
         aggregate := st.(aggregate) * m_msg * st.(local)^-1;
         adjacent := st.(adjacent); 
         balance := st.(balance);
         broadcast := st.(broadcast);
         levels := st.(levels) |}
| SendAggregate => 
  when (sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match parent st.(adjacent) st.(levels) with
  | None => nop
  | Some dst => 
    match NMap.find dst st.(balance) with
    | Some m_dst =>   
      send (dst, (Aggregate st.(aggregate))) ;;
      put {| local := st.(local);
             aggregate := 1;
             adjacent := st.(adjacent);
             balance := NMap.add dst (m_dst * st.(aggregate)) st.(balance);
             broadcast := st.(broadcast);
             levels := st.(levels) |}
    | None => nop
    end
  end)
| AggregateRequest client_id => 
  write_output (AggregateResponse client_id st.(aggregate))
| Broadcast =>
  when st.(broadcast)
  (send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent) ;; 
  put {| local := st.(local);
         aggregate := st.(aggregate);
         adjacent := st.(adjacent);
         balance := st.(balance);
         broadcast := false;
         levels := st.(levels) |})
| LevelRequest client_id =>   
  write_output (LevelResponse client_id (level st.(adjacent) st.(levels)))
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler i 
else NonRootIOHandler i.

Instance TreeAggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance TreeAggregation_MultiParams : MultiParams TreeAggregation_BaseParams :=
  {
    name := name ;
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    name_eq_dec := name_eq_dec ;
    nodes := nodes ;
    all_names_nodes := all_names_nodes ;
    no_dup_nodes := no_dup_nodes ;
    init_handlers := InitData ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

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

Instance TreeAggregation_NewMsgParams : NewMsgParams TreeAggregation_MultiParams :=
  {
    msg_new := New
  }.

Lemma net_handlers_NetHandler :
  forall dst src m st os st' ms,
    net_handlers dst src m st = (os, st', ms) ->
    NetHandler dst src m st = (tt, os, st', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ NMap.find src st.(balance) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = NMap.add src (m_src * (m_msg)^-1) st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ NMap.find src st.(balance) = None /\ 
     st' = st /\ 
     out = [] /\ ms = []) \/
    (root dst /\ msg = Fail /\ exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     exists m_bal, NMap.find src st.(balance) = Some m_bal /\
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_bal /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = NMap.remove src st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ msg = Fail /\ NMap.find src st.(balance) = None /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ NMap.find src st.(balance) = None /\
     level st.(adjacent) st.(levels) = level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ NMap.find src st.(balance) = None /\
     level st.(adjacent) st.(levels) <> level (NSet.remove src st.(adjacent)) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.remove src st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ 
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (NMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(balance) = st.(balance) /\
     st'.(broadcast) = true /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ msg = New /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(balance) = NMap.add src 1 st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = [(src, Level (Some 0))]) \/
    (~ root dst /\ msg = New /\ level st.(adjacent) st.(levels) = None /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(balance) = NMap.add src 1 st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = New /\ exists lv, level st.(adjacent) st.(levels) = Some lv /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(balance) = NMap.add src 1 st.(balance) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = [(src, Level (Some lv))]).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg => [m_msg||olv_msg|]; monad_unfold; case root_dec => /= H_dec H_eq; repeat break_let; repeat break_match; repeat break_if; repeat find_injection.
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
  simpl.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; left.
  repeat split => //.
  exists a.
  simpl.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; left.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; right; left.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; right; right; left.
  split => //.
  by exists olv_msg.
- right; right; right; right; right; right; right; right; right; left.
  split => //.
  exists l1.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; left.
  split => //.
  exists l1.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; right; left.
  move: Heqb.
  by case olv_eq_dec.
- right; right; right; right; right; right; right; right; right; right; right; right; left.
  move: Heqb.
  by case olv_eq_dec.
- by right; right; right; right; right; right; right; right; right; right; right; right; right; left.
- unfold sumbool_not in *.
  break_match => //.
  right; right; right; right; right; right; right; right; right; right; right; right; right; right; right.
  move: n {Heqb}.
  case H_lv: level => [lv|] H_neq //.
  repeat split => //.
  by exists lv.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; right; right; right; right; right; right; right; right; right; right; right; right; left.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    IOHandler h i d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma send_level_fold_app :
  forall ns st olv nm,
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, nm)) st) = 
snd (fold_left 
       (fun (a : Handler Data) (e : NSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, [])) st) ++ nm.
Proof.
elim => //=.
move => n ns IH st olv nm.
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
forall ns nm olv st,
fst
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = tt.
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma send_level_adjacent_fst_fst_eq : 
forall fs olv st,
  fst (fst (fst (send_level_adjacent olv fs st))) = tt.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite NSet.fold_spec.
by rewrite fst_fst_fst_tt_send_level_fold.
Qed.

Lemma snd_fst_fst_out_send_level_fold : 
forall ns nm olv st,
snd
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = [].
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma snd_fst_st_send_level_fold : 
forall ns nm olv st,
snd (fst
        (fold_left
           (fun (a : Handler Data) (e : NSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st)) = st.
Proof.
elim => //=.
move => n ns IH nm olv st.
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
  send_level_adjacent olv fs st = (tt, [], st, level_adjacent olv fs).
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
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(balance) = st.(balance) /\
         st'.(broadcast) = st.(broadcast) /\
         st'.(levels) = st.(levels) /\
         out = [] /\ ms = []) \/
      (root h /\ i = SendAggregate /\ 
         st' = st /\
         out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ 
       st.(aggregate) <> 1 /\ 
       exists dst m_dst, parent st.(adjacent) st.(levels) = Some dst /\ NMap.find dst st.(balance) = Some m_dst /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = 1 /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = NMap.add dst (m_dst * st.(aggregate)) st.(balance) /\
       st'.(broadcast) = st.(broadcast) /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) = 1 /\
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 1 /\
       parent st.(adjacent) st.(levels) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 1 /\
       exists dst, parent st.(adjacent) st.(levels) = Some dst /\ NMap.find dst st.(balance) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (exists client_id, i = AggregateRequest client_id /\ 
       st' = st /\ 
       out = [AggregateResponse client_id (aggregate st)] /\ ms = []) \/
      (root h /\ i = Broadcast /\ st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = Broadcast /\ st.(broadcast) = true /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(balance) = st.(balance) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\ st.(broadcast) = false /\
       st' = st /\
       out = [] /\ ms = []) \/
      (root h /\ exists client_id, i = LevelRequest client_id /\
       st' = st /\
       out = [LevelResponse client_id (Some 0)] /\ ms = []) \/
      (~ root h /\ exists client_id, i = LevelRequest client_id /\
       st' = st /\
       out = [LevelResponse client_id (level st.(adjacent) st.(levels))] /\ ms = []).
Proof.
move => h i st u out st' ms.
rewrite /IOHandler /RootIOHandler /NonRootIOHandler.
case: i => [m_msg||client_id|client_id|]; monad_unfold; case root_dec => /= H_dec H_eq; repeat break_let; repeat find_injection; repeat break_match; repeat break_let; repeat find_injection.
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
- right; right; right; right; right; right; left.
  by exists client_id.
- right; right; right; right; right; right; left.
  by exists client_id.
- right; right; right; right; right; right; right; right; right; right; left.
  split => //.
  by exists client_id.
- right; right; right; right; right; right; right; right; right; right; right.
  split => //.
  by exists client_id.
- by right; right; right; right; right; right; right; left.
- find_rewrite_lem send_level_adjacent_eq.
  find_injection.
  right; right; right; right; right; right; right; right; left.
  by rewrite app_nil_l -2!app_nil_end.
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

End TreeAggregation.
