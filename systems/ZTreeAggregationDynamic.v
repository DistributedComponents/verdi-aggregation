Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.

Require Import TreeAux.

Require Import Sumbool.
Require String.

Require Import ZArith.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module ZTreeAggregation (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap).

Inductive Msg : Type := 
| Aggregate : Z -> Msg
| Level : option lv -> Msg
| New : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality; first exact: Z_eq_dec.
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
| SendAggregate : Input
| AggregateRequest : String.string -> Input
| LevelRequest : String.string -> Input
| Broadcast : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality; auto using String.string_dec.
Defined.

Inductive Output : Type :=
| AggregateResponse : String.string -> Z -> Output
| LevelResponse : String.string -> option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality; auto using String.string_dec; first exact: Z_eq_dec.
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
  aggregate : Z ; 
  adjacent : NS ; 
  levels : NL
}.

Definition InitData (n : name) :=
  {| aggregate := 1%Z ;
     adjacent := NSet.empty ;
     levels := NMap.empty lv |}.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition RootNetHandler (src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Aggregate m_msg => 
  put {| aggregate := st.(aggregate) + m_msg ;
         adjacent := st.(adjacent) ;
         levels := st.(levels) |}
| Level _ => nop 
| New =>
  put {| aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
         levels := st.(levels) |} ;;
  send (src, Level (Some 0))
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  put {| aggregate := st.(aggregate) + m_msg ;
         adjacent := st.(adjacent) ;
         levels := st.(levels) |}
| Level None =>
  put {| aggregate := st.(aggregate) ;
         adjacent := st.(adjacent) ;
         levels := NMap.remove src st.(levels) |}
| Level (Some lv') =>
  put {| aggregate := st.(aggregate) ;
         adjacent := st.(adjacent) ;
         levels := NMap.add src lv' st.(levels) |}
| New =>
  put {| aggregate := st.(aggregate) ;
         adjacent := NSet.add src st.(adjacent) ;
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
| SendAggregate => 
  when (sumbool_not _ _ (Z_eq_dec st.(aggregate) 0%Z))
  (match parent st.(adjacent) st.(levels) with
  | None => nop
  | Some dst => 
    send (dst, (Aggregate st.(aggregate))) ;;
    put {| aggregate := 0%Z;
           adjacent := st.(adjacent);
           levels := st.(levels) |}
  end)
| AggregateRequest client_id => 
  write_output (AggregateResponse client_id st.(aggregate))
| Broadcast =>
  send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)
| LevelRequest client_id =>   
  write_output (LevelResponse client_id (level st.(adjacent) st.(levels)))
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler i 
else NonRootIOHandler i.

Instance ZTreeAggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance ZTreeAggregation_MultiParams : MultiParams ZTreeAggregation_BaseParams :=
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

Instance ZTreeAggregation_NameOverlayParams : NameOverlayParams ZTreeAggregation_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance ZTreeAggregation_NewMsgParams : NewMsgParams ZTreeAggregation_MultiParams :=
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
    (exists m_msg, msg = Aggregate m_msg /\
     st'.(aggregate) = (st.(aggregate) + m_msg)%Z /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ 
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(levels) = NMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(levels) = NMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ msg = New /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = [(src, Level (Some 0))]) \/
    (~ root dst /\ msg = New /\ level st.(adjacent) st.(levels) = None /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = New /\ exists lv, level st.(adjacent) st.(levels) = Some lv /\
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = NSet.add src st.(adjacent) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = [(src, Level (Some lv))]).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg => [m_msg|olv_msg|]; monad_unfold; case root_dec => /= H_dec H_eq; repeat break_let; repeat break_match; repeat break_if; repeat find_injection.
- by left; exists m_msg.
- by left; exists m_msg.
- right; left.
  split => //.
  by exists olv_msg.
- right; right; left.
  split => //.
  by exists l1.
- by right; right; right; left.
- by right; right; right; right; left.
- unfold sumbool_not in *.
  break_match => //=.
  right; right; right; right; right; right.
  move: n {Heqb}.
  case H_lv: level => [lv|] H_neq //.
  repeat split => //.
  by exists lv.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; right; right; right; left.
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
      (root h /\ i = SendAggregate /\ 
         st' = st /\
         out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ 
       st.(aggregate) <> 0%Z /\ 
       exists dst, parent st.(adjacent) st.(levels) = Some dst /\
       st'.(aggregate) = 0%Z /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) = 0%Z /\
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 0%Z /\
       parent st.(adjacent) st.(levels) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 0%Z /\
       exists dst, parent st.(adjacent) st.(levels) = Some dst /\
       st' = st /\
       out = [] /\ ms = []) \/
      (exists client_id, i = AggregateRequest client_id /\ 
       st' = st /\ 
       out = [AggregateResponse client_id (aggregate st)] /\ ms = []) \/
      (root h /\ i = Broadcast /\ st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = Broadcast /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\
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
case: i => [|client_id|client_id|]; monad_unfold; case root_dec => /= H_dec H_eq; repeat break_let; repeat find_injection; repeat break_match; repeat break_let; repeat find_injection.
- by left.
- unfold sumbool_not in *.
  break_match => //.
  right; left.
  repeat split => //.
  by exists n.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; right; left.
- unfold sumbool_not in *.
  break_match => //.
  by right; right; left.
- unfold sumbool_not in *.
  right; right; right; right; right; left.
  by exists client_id.
- right; right; right; right; right; left.
  by exists client_id.
- right; right; right; right; right; right; right; right; right; left.
  split => //.
  by exists client_id.
- right; right; right; right; right; right; right; right; right; right.
  split => //.
  by exists client_id.
- by right; right; right; right; right; right; left.
- find_rewrite_lem send_level_adjacent_eq.
  find_injection.
  by right; right; right; right; right; right; right; left.
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

End ZTreeAggregation.
