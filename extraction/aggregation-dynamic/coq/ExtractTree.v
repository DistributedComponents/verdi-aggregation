Require Import Verdi.
Require Import NPeano.
Require Import PeanoNat.
Require Import StructTact.Fin.

Require Import NameOverlay.
Require Import TreeDynamic.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extract Inlined Constant leb => "(<=)".
Extract Inlined Constant negb => "not".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant Nat.max => "Pervasives.max".
Extract Inlined Constant Nat.min => "Pervasives.min".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.pred => "(fun n -> if n <= 0 then 0 else n - 1)".

Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".
Extract Inlined Constant in_dec => "(fun h -> List.mem)".

Extract Inlined Constant fin => int.
Extract Inlined Constant fin_eq_dec => "(fun _ -> (=))".
Extract Inlined Constant all_fin => "(fun n -> (Obj.magic (seq 1 n)))".
Extract Inlined Constant fin_compare => "(fun _ n m -> if n = m then EQ else if n < m then LT else GT)".
Extract Inlined Constant fin_comparison => "(fun _ n m -> if n = m then Eq else if n < m then Lt else Gt)".
Extract Inlined Constant fin_to_nat => "(fun _ n -> n)".

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
