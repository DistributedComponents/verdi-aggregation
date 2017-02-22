Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFin.

Require Import ExtractZTreeAggregationDynamicDeps.

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

Module ZTreeAggregationNames := ZTreeAggregation Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AdjacentNames TAuxNames.
Import ZTreeAggregationNames.

Extraction "extraction/zaggregation-dynamic/ocaml/ZTreeAggregation.ml" List.seq ZTreeAggregation_BaseParams ZTreeAggregation_MultiParams.
