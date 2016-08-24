Require Import Verdi.
Require Import NameOverlay.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import FMapInterface.

Set Implicit Arguments.

Module TAux (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC).

Module NSetFacts := Facts NSet.
Module NSetProps := Properties NSet.
Module NSetOrdProps := OrdProperties NSet.

Require Import FMapFacts.
Module NMapFacts := Facts NMap.

Definition lv := nat.
Definition lv_eq_dec := Nat.eq_dec.

Definition NS := NSet.t.
Definition NL := NMap.t lv.

Inductive level_in (fs : NS) (fl : NL) (n : name) (lv' : lv) : Prop :=
| in_level_in : NSet.In n fs -> NMap.find n fl = Some lv' -> level_in fs fl n lv'.

Inductive min_level (fs : NS) (fl : NL) (n : name) (lv' : lv) : Prop :=
| min_lv_min : level_in fs fl n lv' -> 
  (forall (lv'' : lv) (n' : name), level_in fs fl n' lv'' -> ~ lv'' < lv') ->
  min_level fs fl n lv'.

Record st_par := mk_st_par { st_par_set : NS ; st_par_map : NL }.

Record nlv := mk_nlv { nlv_n : name ; nlv_lv : lv }.

Definition st_par_lt (s s' : st_par) : Prop :=
NSet.cardinal s.(st_par_set) < NSet.cardinal s'.(st_par_set).

Lemma st_par_lt_well_founded : well_founded st_par_lt.
Proof.
apply (well_founded_lt_compat _ (fun s => NSet.cardinal s.(st_par_set))).
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
   match NSet.choose s.(st_par_set) as sopt return (_ = sopt -> _) with
   | Some n => fun (H_eq : _) => 
     match par_rec (mk_st_par (NSet.remove n s.(st_par_set)) s.(st_par_map)) _ with
     | inleft (exist nlv' H_min) =>
       match NMap.find n s.(st_par_map) as n' return (_ = n' -> _) with
       | Some lv' => fun (H_find : _) => 
         match lt_dec lv' nlv'.(nlv_lv)  with
         | left H_dec => inleft _ (exist _ (mk_nlv n lv') _)
         | right H_dec => inleft _ (exist _ nlv' _)
         end
       | None => fun (H_find : _) => inleft _ (exist _ nlv' _)
       end (refl_equal _)
     | inright H_min =>
       match NMap.find n s.(st_par_map) as n' return (_ = n' -> _) with
       | Some lv' => fun (H_find : _) => inleft _ (exist _ (mk_nlv n lv') _)
       | None => fun (H_find : _) => inright _ _
       end (refl_equal _)
     end
   | None => fun (H_eq : _) => inright _ _
   end (refl_equal _)) => /=.
- rewrite /st_par_lt /=.
  apply NSet.choose_spec1 in H_eq.
  set sr := NSet.remove _ _.
  have H_notin: ~ NSet.In n sr by move => H_in; apply NSetFacts.remove_1 in H_in.
  have H_add: NSetProps.Add n sr s.(st_par_set).
    rewrite /NSetProps.Add.
    move => n'.
    split => H_in.
      case (name_eq_dec n n') => H_eq'; first by left.
      by right; apply NSetFacts.remove_2.
    case: H_in => H_in; first by rewrite -H_in.
    by apply NSetFacts.remove_3 in H_in.
  have H_card := NSetProps.cardinal_2 H_notin H_add.
  rewrite H_card {H_notin H_add H_card}.
  by auto with arith.
- apply NSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  apply min_lv_min; first exact: in_level_in.
  move => lv'' n' H_lv.
  inversion H_lv => {H_lv}.
  inversion H_min => {H_min}.
  case (name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H0.
    rewrite H_find in H0.
    injection H0 => H_eq_lt.
    rewrite H_eq_lt.
    by auto with arith.
  suff H_suff: ~ lv'' < nlv'.(nlv_lv) by omega.
  apply: (H2 _ n').
  apply: in_level_in => //.
  by apply NSetFacts.remove_2.
- apply NSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  inversion H_min => {H_min}.
  inversion H => {H}.
  apply min_lv_min.
    apply: in_level_in => //.
    by apply NSetFacts.remove_3 in H1.
  move => lv'' n' H_lv.
  inversion H_lv => {H_lv}.
  case (name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H3.
    rewrite H_find in H3.
    injection H3 => H_eq_lv.
    by rewrite -H_eq_lv.
  apply: (H0 _ n').
  apply: in_level_in => //.
  exact: NSetFacts.remove_2.
- apply NSet.choose_spec1 in H_eq.
  rewrite /= {s0} in H_min.
  inversion H_min => {H_min}.
  inversion H => {H}.
  apply min_lv_min.
    apply: in_level_in => //.
    by apply NSetFacts.remove_3 in H1.
  move => lv' n' H_lv.
  inversion H_lv => {H_lv}.
  case (name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H3.
    by rewrite H_find in H3.
  apply: (H0 _ n').
  apply: in_level_in => //.
  exact: NSetFacts.remove_2.
- apply NSet.choose_spec1 in H_eq.
  rewrite /= in H_min.
  apply min_lv_min; first exact: in_level_in.
  move => lv'' n' H_lv.
  inversion H_lv.
  case (name_eq_dec n n') => H_eq'.
    rewrite -H_eq' in H0.
    rewrite H_find in H0.
    injection H0 => H_eq_lv.
    rewrite H_eq_lv.  
    by auto with arith.
  move => H_lt.
  case: H_min.
  exists (mk_nlv n' lv'') => /=.
  apply: in_level_in => //.
  exact: NSetFacts.remove_2.
- apply NSet.choose_spec1 in H_eq.
  rewrite /= in H_min.
  move => [nlv' H_lv].
  inversion H_lv => {H_lv}.
  case: H_min.
  exists nlv'.
  case (name_eq_dec n nlv'.(nlv_n)) => H_eq'.
    rewrite -H_eq' in H0.
    by rewrite H_find in H0.
  apply: in_level_in => //.
  exact: NSetFacts.remove_2.
- apply NSet.choose_spec2 in H_eq.
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

Definition parent (fs : NS) (fl : NL) : option name :=
match par (mk_st_par fs fl) with
| inleft (exist nlv' _) => Some nlv'.(nlv_n)
| inright _ => None
end.

Definition level (fs : NS) (fl : NL) : option lv :=
match lev (mk_st_par fs fl) with
| inleft (exist lv' _) => Some lv'
| inright _ => None
end.

Definition olv_eq_dec : forall (lvo lvo' : option lv), { lvo = lvo' }+{ lvo <> lvo' }.
decide equality.
exact: lv_eq_dec.
Defined.

Class TreeMsg :=
  {
    tree_msg : Type ;
    tree_level : option lv -> tree_msg
  }.

Section LevelFolds.

Context {tr_msg : TreeMsg}.

Definition level_fold (lvo : option lv) (n : name) (partial : list (name * tree_msg)) : list (name * tree_msg) :=
(n, tree_level lvo) :: partial.

Definition level_adjacent (lvo : option lv) (fs : NS) : list (name * tree_msg) :=
NSet.fold (level_fold lvo) fs [].

Lemma fold_left_level_fold_eq :
forall ns nml olv,
fold_left (fun l n => level_fold olv n l) ns nml = fold_left (fun l n => level_fold olv n l) ns [] ++ nml.
Proof.
elim => //=.
move => n ns IH nml olv.
rewrite /level_fold /=.
rewrite IH.
have IH' := IH ([(n, tree_level olv)]).
rewrite IH'.
set bla := fold_left _ _ _.
rewrite -app_assoc.
by rewrite app_assoc.
Qed.

End LevelFolds.

End TAux.
