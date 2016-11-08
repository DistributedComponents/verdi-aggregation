Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module FailureRecorder (Import NT : NameType) 
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (Import ANT : AdjacentNameType NT).

Inductive Msg : Set := 
| Fail : Msg
| New : Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Input : Set := .

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Output : Set := .

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
Defined.

Definition NS := NSet.t.

Record Data := mkData { adjacent : NS }.

Definition InitData (n : name) := mkData NSet.empty.

Inductive Label : Type :=
| Tau : Label
| RecvFail : name -> name -> Label
| RecvNew : name -> name -> Label.

Definition Label_eq_dec : forall x y : Label, {x = y} + {x <> y}.
decide equality; exact: name_eq_dec.
Defined.

Definition Handler (S : Type) := GenHandler (name * Msg) S Output Label.

Definition NetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| New =>
  put {| adjacent := NSet.add src st.(adjacent) |} ;;
  ret (RecvNew me src)
| Fail => 
  put {| adjacent := NSet.remove src st.(adjacent) |} ;;
  ret (RecvFail me src)
end.

Definition IOHandler (me : name) (i : Input) : Handler Data := ret Tau.

Instance FailureRecorder_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance FailureRecorder_LabeledMultiParams : LabeledMultiParams FailureRecorder_BaseParams :=
  {
    lb_name := name ;
    lb_msg := Msg ;
    lb_msg_eq_dec := Msg_eq_dec ;
    lb_name_eq_dec := name_eq_dec ;
    lb_nodes := nodes ;
    lb_all_names_nodes := all_names_nodes ;
    lb_no_dup_nodes := no_dup_nodes ;
    label := Label ;
    label_silent := Tau ;
    lb_init_handlers := InitData ;
    lb_net_handlers := (fun dst src msg s => runGenHandler s (NetHandler dst src msg)) ;
    lb_input_handlers := fun nm msg s => runGenHandler s (IOHandler nm msg) ;
  }.

Instance FailureRecorder_MultiParams : MultiParams FailureRecorder_BaseParams := unlabeled_multi_params.

Instance FailureRecorder_NameOverlayParams : NameOverlayParams FailureRecorder_MultiParams :=
  {
    adjacent_to := adjacent_to ;
    adjacent_to_dec := adjacent_to_dec ;
    adjacent_to_symmetric := adjacent_to_symmetric ;
    adjacent_to_irreflexive := adjacent_to_irreflexive
  }.

Instance FailureRecorder_FailMsgParams : FailMsgParams FailureRecorder_MultiParams :=
  {
    msg_fail := Fail
  }.

Instance FailureRecorder_NewMsgParams : NewMsgParams FailureRecorder_MultiParams :=
  {
    msg_new := New
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
monad_unfold.
repeat break_let.
find_inversion.
by exists l0; auto.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    exists lb, IOHandler h i d = (lb, os, d', ms).
Proof. by []. Qed.

Lemma IOHandler_cases :
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) -> False.
Proof. by move => h; case. Qed.

Lemma NetHandler_cases : 
  forall dst src msg st lb out st' ms,
    NetHandler dst src msg st = (lb, out, st', ms) ->
    (msg = Fail /\ lb = RecvFail dst src /\ out = [] /\ ms = [] /\ st'.(adjacent) = NSet.remove src st.(adjacent)) \/
    (msg = New /\ lb = RecvNew dst src /\ out = [] /\ ms = [] /\ st'.(adjacent) = NSet.add src st.(adjacent)).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler.
case: msg; monad_unfold => /= H_eq.
- by left; find_inversion.
- by right; find_inversion.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases.

End FailureRecorder.
