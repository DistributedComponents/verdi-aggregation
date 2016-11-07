Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import AggregationDefinitions.
Require Import AggregationAux.
Require Import TreeAux.
Require Import TreeAggregationDynamic.

Require Import StructTact.Fin.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.fingroup.fingroup.
Require Import mathcomp.algebra.zmodp.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import ExtrOcamlBasicExt.
Require Import ExtrOcamlNatIntExt.

Require Import ExtrOcamlBool.
Require Import ExtrOcamlList.
Require Import ExtrOcamlFin.

Module NumNames : NatValue. Definition n := 5. End NumNames.
Module Names := FinName NumNames.
Module NamesOT := FinNameOrderedType NumNames Names.
Module NamesOTCompat := FinNameOrderedTypeCompat NumNames Names.
Module RootNames := FinRootNameType NumNames Names.
Module AdjacentNames := FinCompleteAdjacentNameType NumNames Names.

Require Import MSetList.
Module NamesSet <: MSetInterface.S := MSetList.Make NamesOT.

Require Import FMapList.
Module NamesMap <: FMapInterface.S := FMapList.Make NamesOTCompat.

Module CFG <: CommutativeFinGroup.
Definition gT := [finGroupType of 'I_128].
Lemma mulgC : @commutative gT _ mulg. exact: Zp_mulgC. Qed.
End CFG.

Module TAuxNames := FinTAux NumNames Names NamesOT NamesSet NamesOTCompat NamesMap.

Module TreeAggregationNames := TreeAggregation Names NamesOT NamesSet NamesOTCompat NamesMap RootNames CFG AdjacentNames TAuxNames.
Import TreeAggregationNames.

Extraction "extraction/aggregation-dynamic/ocaml/TreeAggregation.ml" List.seq TreeAggregation_BaseParams TreeAggregation_MultiParams.
