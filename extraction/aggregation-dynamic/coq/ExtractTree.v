Require Import Verdi.
Require Import NPeano.
Require Import PeanoNat.
Require Import StructTact.Fin.

Require Import NameOverlay.
Require Import TreeDynamic.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import ExtrOcamlBasicExt.
Require Import ExtrOcamlNatIntExt.

Require Import ExtrOcamlBool.
Require Import ExtrOcamlList.
Require Import ExtrOcamlFin.

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

Module T := Tree FN_N5 NOT_N5 N5Set NOTC_N5 N5Map RNT_N5 ANC_N5.
Import T.

Extraction "extraction/aggregation-dynamic/coq/Tree.ml" seq Tree_BaseParams Tree_MultiParams.
