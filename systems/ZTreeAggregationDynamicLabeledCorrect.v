Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import Verdi.NameOverlay.
Require Import Verdi.LabeledNet.

Require Import TreeAux.
Require Import ZTreeAggregationDynamicLabeled.

Require Import InfSeqExt.infseq.

Require Import Sumbool.
Require String.

Require Import ZArith.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Implicit Arguments.

Module ZTreeAggregationCorrect (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) 
 (Import RNT : RootNameType NT) 
 (Import ANT : AdjacentNameType NT) 
 (Import TA : TAux NT NOT NSet NOTC NMap).

Module ZTA := ZTreeAggregation NT NOT NSet NOTC NMap RNT ANT TA.
Import ZTA.

Definition connected net := net.(odnwNodes) = net.(odnwNodes). (* FIXME *)

Definition node_aggregate (state : name -> option data) (n : name) : Z :=
match state n with
| None => 0%Z
| Some d => d.(aggregate)
end.

Lemma churn_free_stabilization : 
  forall s, event_step_star step_ordered_dynamic step_ordered_dynamic_init (hd s) ->
       connected (evt_a (hd s)) ->
       lb_step_execution lb_step_ordered_dynamic s ->
       weak_fairness lb_step_ordered_dynamic Tau s ->
       forall n, root n -> In n (evt_a (hd s)).(odnwNodes) ->
       eventually (always (now (fun e => Z_of_nat (length e.(evt_a).(odnwNodes)) = node_aggregate e.(evt_a).(odnwState) n))) s.
Proof.
Admitted.

End ZTreeAggregationCorrect.
