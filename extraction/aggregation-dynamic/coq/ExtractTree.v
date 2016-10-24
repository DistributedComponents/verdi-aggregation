Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import TreeDynamic.

Require Import StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import ExtrOcamlBasicExt.
Require Import ExtrOcamlNatIntExt.

Require Import ExtrOcamlBool.
Require Import ExtrOcamlList.
Require Import ExtrOcamlFin.

Module NumNames : NatValue. Definition n := 5. End NumNames.
Module Names : FinNameType NumNames := FinName NumNames.
Module NamesOT : NameOrderedType Names := FinNameOrderedType NumNames Names.
Module NamesOTCompat : NameOrderedTypeCompat Names := FinNameOrderedTypeCompat NumNames Names.
Module RootNames := FinRootNameType NumNames Names.
Module AdjacentNames : AdjacentNameType Names := FinCompleteAdjacentNameType NumNames Names.

Require Import MSetList.
Module NamesSet <: MSetInterface.S := MSetList.Make NamesOT.

Require Import FMapList.
Module NamesMap <: FMapInterface.S := FMapList.Make NamesOTCompat.

Module TreeNames := Tree Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AdjacentNames.
Import TreeNames.

Extraction "extraction/aggregation-dynamic/ocaml/Tree.ml" seq Tree_BaseParams Tree_MultiParams.
