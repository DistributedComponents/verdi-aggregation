Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import ssreflect.

Set Implicit Arguments.

Module Tree (N : NatValue) <: NatValue
  with Definition n := N.n.

Definition num_sources := N.n.

Require Import OrderedTypeEx.
Require Import FMapList.
Module fin_n_compat_OT := fin_OT_compat N.
Module FinNMap <: FMapInterface.S := FMapList.Make fin_n_compat_OT.

Require Import Orders.
Require Import MSetList.
Module fin_n_OT := fin_OT N.
Module FinNSet <: MSetInterface.S := MSetList.Make fin_n_OT.

Require Import MSetFacts.
Module FinNSetFacts := Facts FinNSet.

Require Import MSetProperties.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.
Require Import FMapFacts.
Module FinNMapFacts := Facts FinNMap.

Definition lv := nat.
Definition lv_eq_dec := Nat.eq_dec.

Definition FinNL := FinNMap.t lv.

Definition FinNS := FinNSet.t.

Definition Name := (fin num_sources).

Definition list_sources := (all_fin num_sources).

Parameter is_root : Name -> bool.

Parameter root_unique : forall n n', is_root n = true -> is_root n' = true -> n = n'.

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
exact: fin_eq_dec.
Defined.

Definition Name_neq_bool (x y : Name) : bool :=
match Name_eq_dec x y with
| left _ => false
| right _ => true
end.

Lemma Name_neq_bool_true_neq : forall (x y : Name),
  Name_neq_bool x y = true -> x <> y.
Proof.
move => x y.
rewrite /Name_neq_bool.
by case (Name_eq_dec _ _).
Qed.

Lemma Name_neq_bool_neq_true : forall (x y : Name),
  x <> y -> Name_neq_bool x y = true.
Proof.
move => x y.
rewrite /Name_neq_bool.
by case (Name_eq_dec _ _).
Qed.

Inductive Msg := 
| Level : option lv -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
case: o; case: o0.
- move => n m.
  case (lv_eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Inductive Input :=
| Timeout : Input
| Query : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
Defined.

Inductive Output :=
| Response : option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality.
case: o; case: o0.
- move => n m.
  case (Nat.eq_dec n m) => H_dec; first by rewrite H_dec; left.
  right.
  move => H_eq.
  injection H_eq => H_eq'.
  by rewrite H_eq' in H_dec.
- by right.
- by right.
- by left.
Defined.

Record Data := mkData { broadcast : bool ; adjacent : FinNS ; levels : FinNL }.

Parameter adjacency : Name -> FinNS.

Parameter not_adjacent_self : forall (n : Name), ~ FinNSet.In n (adjacency n).

Parameter adjacency_mutual : forall (n n' : Name), FinNSet.In n (adjacency n') -> FinNSet.In n' (adjacency n).
    
Definition init_Data (n : Name) := 
if is_root n then mkData true (adjacency n) (FinNMap.empty lv)
else mkData false (adjacency n) (FinNMap.empty lv).

Inductive level_in (fs : FinNS) (fl : FinNL) (n : Name) (lv' : lv) : Prop :=
| in_level_in : FinNSet.In n fs -> FinNMap.find n fl = Some lv' -> level_in fs fl n lv'.

Inductive min_level (fs : FinNS) (fl : FinNL) (n : Name) (lv' : lv) : Prop :=
| min_lv_min : level_in fs fl n lv' -> 
  (forall (lv'' : lv) (n' : Name), level_in fs fl n' lv'' -> ~ lv'' < lv') ->
  min_level fs fl n lv'.

Record st_par := mk_st_par { st_par_set : FinNS ; st_par_map : FinNL }.

Record nlv := mk_nlv { nlv_n : Name ; nlv_lv : lv }.

Definition st_par_lt (s s' : st_par) : Prop :=
FinNSet.cardinal s.(st_par_set) < FinNSet.cardinal s'.(st_par_set).

Lemma st_par_lt_well_founded : well_founded st_par_lt.
Proof.
apply (well_founded_lt_compat _ (fun s => FinNSet.cardinal s.(st_par_set))).
by move => x y; rewrite /st_par_lt => H.
Qed.

Definition par_t (s : st_par) := 
{ nlv' | min_level s.(st_par_set) s.(st_par_map) nlv'.(nlv_n) nlv'.(nlv_lv) }+
{ ~ exists nlv', level_in s.(st_par_set) s.(st_par_map) nlv'.(nlv_n) nlv'.(nlv_lv) }.

Definition par_F : forall s : st_par, 
  (forall s' : st_par, st_par_lt s' s -> par_t s') ->
  par_t s.
rewrite /par_t.
refine 
  (fun (s : st_par) par_rec => 
   match FinNSet.choose s.(st_par_set) as sopt return (_ = sopt -> _) with
   | Some n => fun (H_eq : _) => 
     match par_rec (mk_st_par (FinNSet.remove n s.(st_par_set)) s.(st_par_map)) _ with
     | inleft (exist nlv' H_min) =>
       match FinNMap.find n s.(st_par_map) as n' return (_ = n' -> _) with
       | Some lv' => fun (H_find : _) => 
         match lt_dec lv' nlv'.(nlv_lv)  with
         | left H_dec => inleft _ (exist _ (mk_nlv n lv') _)
         | right H_dec => inleft _ (exist _ nlv' _)
         end
       | None => fun (H_find : _) => inleft _ (exist _ nlv' _)
       end (refl_equal _)
     | inright H_min =>
       match FinNMap.find n s.(st_par_map) as n' return (_ = n' -> _) with
       | Some lv' => fun (H_find : _) => inleft _ (exist _ (mk_nlv n lv') _)
       | None => fun (H_find : _) => inright _ _
       end (refl_equal _)
     end
   | None => fun (H_eq : _) => inright _ _
   end (refl_equal _)) => /=.
- rewrite /st_par_lt /=.
  apply FinNSet.choose_spec1 in H_eq.
  set sr := FinNSet.remove _ _.
  have H_notin: ~ FinNSet.In n sr by move => H_in; apply FinNSetFacts.remove_1 in H_in.
  have H_add: FinNSetProps.Add n sr s.(st_par_set).
    rewrite /FinNSetProps.Add.
    move => n'.
    split => H_in.
      case (Name_eq_dec n n') => H_eq'; first by left.
      by right; apply FinNSetFacts.remove_2.
    case: H_in => H_in; first by rewrite -H_in.
    by apply FinNSetFacts.remove_3 in H_in.
  have H_card := FinNSetProps.cardinal_2 H_notin H_add.
  rewrite H_card {H_notin H_add H_card}.
  by auto with arith.
- apply FinNSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  apply min_lv_min; first exact: in_level_in.
  move => lv'' n' H_lv.
  inversion H_lv => {H_lv}.
  inversion H_min => {H_min}.
  case (Name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H0.
    rewrite H_find in H0.
    injection H0 => H_eq_lt.
    rewrite H_eq_lt.
    by auto with arith.
  suff H_suff: ~ lv'' < nlv'.(nlv_lv) by omega.
  apply: (H2 _ n').
  apply: in_level_in => //.
  by apply FinNSetFacts.remove_2.
- apply FinNSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  inversion H_min => {H_min}.
  inversion H => {H}.
  apply min_lv_min.
    apply: in_level_in => //.
    by apply FinNSetFacts.remove_3 in H1.
  move => lv'' n' H_lv.
  inversion H_lv => {H_lv}.
  case (Name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H3.
    rewrite H_find in H3.
    injection H3 => H_eq_lv.
    by rewrite -H_eq_lv.
  apply: (H0 _ n').
  apply: in_level_in => //.
  exact: FinNSetFacts.remove_2.
- apply FinNSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  inversion H_min => {H_min}.
  inversion H => {H}.
  apply min_lv_min.
    apply: in_level_in => //.
    by apply FinNSetFacts.remove_3 in H1.
  move => lv' n' H_lv.
  inversion H_lv => {H_lv}.
  case (Name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H3.
    by rewrite H_find in H3.
  apply: (H0 _ n').
  apply: in_level_in => //.
  exact: FinNSetFacts.remove_2.
- apply FinNSet.choose_spec1 in H_eq.
  rewrite /= in H_min.
  apply min_lv_min; first exact: in_level_in.
  move => lv'' n' H_lv.
  inversion H_lv.
  case (Name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H0.
    rewrite H_find in H0.
    injection H0 => H_eq_lv.
    rewrite H_eq_lv.  
    by auto with arith.
  move => H_lt.
  case: H_min.
  exists (mk_nlv n' lv'') => /=.
  apply: in_level_in => //.
  exact: FinNSetFacts.remove_2.
- apply FinNSet.choose_spec1 in H_eq.
  rewrite /= in H_min.
  move => [nlv' H_lv].
  inversion H_lv => {H_lv}.
  case: H_min.
  exists nlv'.
  case (Name_eq_dec n nlv'.(nlv_n)) => H_eq'.
    rewrite -H_eq' in H0.
    by rewrite H_find in H0.
  apply: in_level_in => //.
  exact: FinNSetFacts.remove_2.
- apply FinNSet.choose_spec2 in H_eq.
  move => [nlv' H_lv].
  inversion H_lv => {H_lv}.
  by case (H_eq nlv'.(nlv_n)).
Defined.

Definition par : forall (s : st_par), par_t s :=
  @well_founded_induction_type
  st_par
  st_par_lt
  st_par_lt_well_founded
  par_t
  par_F.

Definition lev : forall (s : st_par),
{ lv' | exists n, exists lv'', min_level s.(st_par_set) s.(st_par_map) n lv'' /\ lv' = lv'' + 1%nat }+
{ ~ exists n, exists lv', level_in s.(st_par_set) s.(st_par_map) n lv' }.
refine
  (fun (s : st_par) =>
   match par s with
   | inleft (exist nlv' H_min) => inleft _ (exist _ (1 + nlv'.(nlv_lv)) _)
   | inright H_ex => inright _ _
   end).
- rewrite /= in H_min.
  exists nlv'.(nlv_n); exists nlv'.(nlv_lv); split => //.
  by omega.
- move => [n [lv' H_lv] ].
  case: H_ex => /=.
  by exists (mk_nlv n lv').
Defined.

Definition parent (fs : FinNS) (fl : FinNL) : option Name :=
match par (mk_st_par fs fl) with
| inleft (exist nlv' _) => Some nlv'.(nlv_n)
| inright _ => None
end.

Definition level (fs : FinNS) (fl : FinNL) : option lv :=
match lev (mk_st_par fs fl) with
| inleft (exist lv' _) => Some lv'
| inright _ => None
end.

Definition olv_eq_dec : forall (lvo lvo' : option lv), { lvo = lvo' }+{ lvo <> lvo' }.
decide equality.
exact: lv_eq_dec.
Defined.

Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition RootNetHandler (src : Name) (msg : Msg) : Handler Data :=
match msg with 
| Level _ => nop 
end.

Definition NonRootNetHandler (src : Name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Level None =>
  let new_levels := FinNMap.remove src st.(levels) in
  match olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) new_levels) with
  | left _ => put (mkData st.(broadcast) st.(adjacent) new_levels)
  | right _ => put (mkData true st.(adjacent) new_levels)
  end
| Level (Some lv') => 
  let new_levels := FinNMap.add src lv' st.(levels) in
  match olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) new_levels) with
  | left _ => put (mkData st.(broadcast) st.(adjacent) new_levels)
  | right _ => put (mkData true st.(adjacent) new_levels)
  end
end.

Definition NetHandler (me src: Name) (msg : Msg) : Handler Data :=
if is_root me then RootNetHandler src msg 
else NonRootNetHandler src msg.

Definition send_level_fold (lvo : option lv) (n : Name) (res : Handler Data) : Handler Data :=
res ;; send (n, (Level lvo)).

Definition send_level_adjacent (lvo : option lv) (fs : FinNS) : Handler Data :=
FinNSet.fold (send_level_fold lvo) fs nop.

Definition RootIOHandler (i : Input) : Handler Data :=
match i with
| Timeout => 
  st <- get ;;
  when st.(broadcast)
  (send_level_adjacent (Some 0) st.(adjacent))
| Query => write_output (Response (Some 0))
end.

Definition NonRootIOHandler (i : Input) : Handler Data :=
match i with
| Timeout =>
  st <- get ;;
  when st.(broadcast)
  (send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent))
| Query =>   
  st <- get ;;
  write_output (Response (level st.(adjacent) st.(levels)))
end.

Definition IOHandler (me : Name) (i : Input) : Handler Data :=
if is_root me then RootIOHandler i 
else NonRootIOHandler i.
