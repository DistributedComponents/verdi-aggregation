Require Export AggregationDefinitions.
Require Export NameAdjacency.
Require Export TreeAux.
Require Export TreeAggregationStatic.

Require Import ZpCommutativeFinGroup.

Module AggregationGroup <: CommutativeFinGroup.
Definition gT := Zp_commFinGroup 127.
End AggregationGroup.
