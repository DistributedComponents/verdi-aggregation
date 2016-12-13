Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import AggregationDefinitions.
Require Import TreeAux.
Require Import TreeAggregationDynamic.

Require Import StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import ExtrOcamlBasicExt.
Require Import ExtrOcamlNatIntExt.

Require Import ExtrOcamlBool.
Require Import ExtrOcamlList.
Require Import ExtrOcamlFin.

Require Import mathcomp.ssreflect.ssreflect.

Module NumNames : NatValue. Definition n := 3. End NumNames.
Module Names := FinName NumNames.
Module NamesOT := FinNameOrderedType NumNames Names.
Module NamesOTCompat := FinNameOrderedTypeCompat NumNames Names.
Module RootNames := FinRootNameType NumNames Names.
Module AdjacentNames := FinCompleteAdjacentNameType NumNames Names.

Require Import MSetList.
Module NamesSet <: MSetInterface.S := MSetList.Make NamesOT.

Require Import FMapList.
Module NamesMap <: FMapInterface.S := FMapList.Make NamesOTCompat.

Module TAuxNames := NameTypeTAux Names NamesOT NamesSet NamesOTCompat NamesMap.

Require Import ZpCommutativeFinGroup.
Module NumZp : NatValue. Definition n := 127. End NumZp.
Module AggregationGroup : CommutativeFinGroup := CFG NumZp.

Module ADefNames := NameTypeADefs Names NamesOT NamesSet NamesOTCompat NamesMap AggregationGroup.
Module TreeAggregationNames := TreeAggregation Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AggregationGroup AdjacentNames TAuxNames ADefNames.
Import TreeAggregationNames.

Extraction "extraction/aggregation-dynamic/ocaml/TreeAggregation.ml" List.seq TreeAggregation_BaseParams TreeAggregation_MultiParams.
