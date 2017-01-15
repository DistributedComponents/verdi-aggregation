Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import TreeStatic.
Require Import NameAdjacency.
Require Import TreeAux.
Require Import StructTact.Fin.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFin.

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

Module AdjacencyNames := FinAdjacency NumNames Names NamesOT NamesSet AdjacentNames.

Module TAuxNames := NameTypeTAux Names NamesOT NamesSet NamesOTCompat NamesMap.

Module TreeNames :=
  Tree Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AdjacentNames AdjacencyNames TAuxNames.
Import TreeNames.

Extraction "extraction/tree/ocaml/Tree.ml" seq Tree_BaseParams Tree_MultiParams.
