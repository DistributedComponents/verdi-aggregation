Require Export AggregationDefinitions.
Require Export TreeAux.
Require Export TreeAggregationDynamic.

Require Import StructTact.Fin.

(*
Require Import ZpCommutativeFinGroup.
Definition num_zp := 0.
Module NumZp : NatValue. Definition n := num_zp. End NumZp.
Module AggregationGroup <: CommutativeFinGroup := CFG NumZp.
Extract Inlined Constant num_zp => "16777215".
Extract Inlined Constant fintype.ord_enum => "(fun _ -> [])".
*)

(*
Require Import ZpCommutativeFinGroup.
Require Import ProdCommutativeFinGroup.
Definition num_zp := 0.
Module NumZp1 : NatValue. Definition n := num_zp. End NumZp1.
Module ZpCFG1 : CommutativeFinGroup := CFG NumZp1.
Module NumZp2 : NatValue. Definition n := num_zp. End NumZp2.
Module ZpCFG2 : CommutativeFinGroup := CFG NumZp2.
Module AggregationGroup : CommutativeFinGroup := ProdCFG ZpCFG1 ZpCFG2.
Extract Inlined Constant num_zp => "16777215".
Extract Inlined Constant fintype.ord_enum => "(fun _ -> [])".
*)

(*
Require Import ZpProdCommutativeFinGroup.
Definition num_zp := 0.
Module NumZp1 : NatValue. Definition n := num_zp. End NumZp1.
Module NumZp2 : NatValue. Definition n := num_zp. End NumZp2.
Module AggregationGroup <: CommutativeFinGroup := CFG NumZp1 NumZp2.
Extract Inlined Constant num_zp => "16777215".
Extract Inlined Constant fintype.ord_enum => "(fun _ -> [])".
*)

(* Extraction of Bvector to int *)

(*
Require Import Bvector.
Require BDef BAddGroup.

Extract Inlined Constant fintype.ord_enum => "(fun _ -> [])".
Extract Inlined Constant Bvector => "int".
Extract Inlined Constant seq.bitseq => "int".
Extract Inlined Constant BAddGroup.Bvector_eq_dec => "(fun _ -> (=))".
Extract Inlined Constant BAddGroup.Bvector_to_bitseq => "(fun _ i -> i)".
Extract Inlined Constant BAddGroup.bitseq_to_Bvector => "(fun _ i -> Some i)".
Extract Inlined Constant BAddGroup.Bvector_to_I2k => "(fun _ i -> i)".
Extract Inlined Constant BAddGroup.I2k_to_Bvector => "(fun _ i -> i)".
Extract Inlined Constant BDef.add => "(fun _ -> (+))".
Extract Inlined Constant BDef.opp => "(fun _ -> (-) 0)".
Extract Inlined Constant BDef.zero => "(fun _ -> 0)".

Require Import BvectorCommutativeFinGroup.
Module NumBits : NatValue. Definition n := 31. End NumBits.
Module AggregationGroup <: CommutativeFinGroup := CFG NumBits.
*)

(* Extraction of Bvector to Int32 *)

Require Import Bvector.
Require BDef BAddGroup.

Extract Inlined Constant fintype.ord_enum => "(fun _ -> [])".
Extract Inlined Constant Bvector => "Int32.t".
Extract Inlined Constant seq.bitseq => "int".
Extract Inlined Constant BAddGroup.Bvector_eq_dec => "(fun _ -> (=))".
Extract Inlined Constant BAddGroup.Bvector_to_bitseq => "(fun _ i -> Int32.to_int i)".
Extract Inlined Constant BAddGroup.bitseq_to_Bvector => "(fun _ i -> Some (Int32.of_int i))".
Extract Inlined Constant BAddGroup.Bvector_to_I2k => "(fun _ i -> Int32.to_int i)".
Extract Inlined Constant BAddGroup.I2k_to_Bvector => "(fun _ i -> Int32.of_int i)".
Extract Inlined Constant BDef.add => "(fun _ -> Int32.add)".
Extract Inlined Constant BDef.opp => "(fun _ -> Int32.neg)".
Extract Inlined Constant BDef.zero => "(fun _ -> Int32.zero)".

Require Import BvectorCommutativeFinGroup.
Module NumBits : NatValue. Definition n := 32. End NumBits.
Module AggregationGroup <: CommutativeFinGroup := CFG NumBits.
