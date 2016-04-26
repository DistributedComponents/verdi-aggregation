Require Import Verdi.
Require Import NPeano.
Require Import PeanoNat.
Require Import StructTact.Fin.

Require Import NameOverlay.
Require Import AggregationAux.
Require Import TreeAggregationStatic.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.
Require Import mathcomp.algebra.zmodp.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extract Inlined Constant Nat.max => "Pervasives.max".
Extract Inlined Constant Nat.min => "Pervasives.min".

Extract Inlined Constant length => "List.length".
Extract Inlined Constant negb => "not".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".
Extract Inlined Constant in_dec => "(fun h -> List.mem)".
Extract Inlined Constant leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.pred => "(fun n -> if n <= 0 then 0 else n - 1)".

Extract Inlined Constant fin => int.

Extract Inlined Constant fin_eq_dec => "(fun _ -> (=))".
Extract Inlined Constant all_fin => "(fun n -> (Obj.magic (seq 1 n)))".
(* FIXME: fin_compare *)
(* FIXME: fin_comparison *)

Import GroupScope.

Module N5 : NatValue. Definition n := 5. End N5.

Module FN_N5 : FinNameType N5 := FinName N5.
Module NOT_N5 : NameOrderedType FN_N5 := FinNameOrderedType N5 FN_N5.
Module NOTC_N5 : NameOrderedTypeCompat FN_N5 := FinNameOrderedTypeCompat N5 FN_N5.
Module ANC_N5 := FinCompleteAdjacentNameType N5 FN_N5.

Require Import MSetList.
Module N5Set <: MSetInterface.S := MSetList.Make NOT_N5.

Require Import FMapList.
Module N5Map <: FMapInterface.S := FMapList.Make NOTC_N5.
Module RNT_N5 := FinRootNameType N5 FN_N5.

Module CFG : CommutativeFinGroup.
Definition gT := [finGroupType of 'I_128].
Definition commutes : forall x y : gT, commute x y. exact: Zp_mulgC. Defined.
End CFG.

Module TA := TreeAggregation FN_N5 NOT_N5 N5Set NOTC_N5 N5Map RNT_N5 CFG ANC_N5.

Extraction "TreeAggregation.ml" TA.TreeAggregation_BaseParams TA.TreeAggregation_MultiParams.
