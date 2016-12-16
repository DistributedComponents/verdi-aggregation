Require Export AggregationDefinitions.
Require Export TreeAux.
Require Export TreeAggregationDynamic.

Require Import StructTact.Fin.

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

(*
Require Import Bvector BDef.
Require Import BvectorCommutativeFinGroup.
Extract Inlined Constant Bvector => "int32".
Extract Inlined Constant add => "(fun _ -> Int32.add)".
Extract Inlined Constant opp => "(fun _ -> Int32.neg)".
Extract Inlined Constant zero => "(fun _ -> 0l)".
Module NumBits : NatValue. Definition n := 1. End NumBits.
Module AggregationGroup <: CommutativeFinGroup := CFG NumBits.
*)
