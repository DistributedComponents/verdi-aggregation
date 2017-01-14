Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFin.

Require Import ExtractionDeps.

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

Module ADefNames := NameTypeADefs Names NamesOT NamesSet NamesOTCompat NamesMap AggregationGroup.
Module TreeAggregationNames := TreeAggregation Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AggregationGroup AdjacentNames TAuxNames ADefNames.
Import TreeAggregationNames.

Extraction "extraction/aggregation-dynamic/ocaml/TreeAggregation.ml" List.seq TreeAggregation_BaseParams TreeAggregation_MultiParams.
