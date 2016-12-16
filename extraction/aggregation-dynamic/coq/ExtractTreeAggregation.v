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
Definition num_zp := 0.
Module NumZp : NatValue. Definition n := num_zp. End NumZp.
Module AggregationGroup <: CommutativeFinGroup := CFG NumZp.
Extract Inlined Constant num_zp => "65535".

(*
Require Import ZpCommutativeFinGroup.
Require Import ProdCommutativeFinGroup.
Module NumZp1 : NatValue. Definition n := 20. End NumZp1.
Module ZpCFG1 : CommutativeFinGroup := CFG NumZp1.
Module NumZp2 : NatValue. Definition n := 127. End NumZp2.
Module ZpCFG2 : CommutativeFinGroup := CFG NumZp2.
Module AggregationGroup : CommutativeFinGroup := ProdCFG ZpCFG1 ZpCFG2.*)

(*
Require Import ZpProdCommutativeFinGroup.
Module NumZp1 : NatValue. Definition n := 20. End NumZp1.
Module NumZp2 : NatValue. Definition n := 127. End NumZp2.
Module AggregationGroup <: CommutativeFinGroup := CFG NumZp1 NumZp2.
*)

(*Require Import Bvector BDef.*)
(*Require Import BvectorCommutativeFinGroup.*)

(*
Extract Inlined Constant Bvector => "int32".
Extract Inlined Constant add => "(fun _ -> Int32.add)".
Extract Inlined Constant opp => "(fun _ -> Int32.neg)".
Extract Inlined Constant zero => "(fun _ -> 0l)".
*)

(*
Module NumBits : NatValue. Definition n := 32. End NumBits.
Module AggregationGroup <: CommutativeFinGroup := CFG NumBits.
*)

Module ADefNames := NameTypeADefs Names NamesOT NamesSet NamesOTCompat NamesMap AggregationGroup.
Module TreeAggregationNames := TreeAggregation Names NamesOT NamesSet NamesOTCompat NamesMap RootNames AggregationGroup AdjacentNames TAuxNames ADefNames.
Import TreeAggregationNames.

Extraction "extraction/aggregation-dynamic/ocaml/TreeAggregation.ml" List.seq TreeAggregation_BaseParams TreeAggregation_MultiParams.
