Require Import Verdi.Verdi.
Require Import Verdi.NameOverlay.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import FMapInterface.

Set Implicit Arguments.

Module Type TAux (Import NT : NameType)  
 (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
 (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC).

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

  Definition par_t (s : st_par) := 
    { nlv' | min_level s.(st_par_set) s.(st_par_map) nlv'.(nlv_n) nlv'.(nlv_lv) }+
    { ~ exists nlv', level_in s.(st_par_set) s.(st_par_map) nlv'.(nlv_n) nlv'.(nlv_lv) }.

  Parameter par : forall (s : st_par), par_t s.

  Parameter lev : forall (s : st_par),
      { lv' | exists n, exists lv'', min_level s.(st_par_set) s.(st_par_map) n lv'' /\ lv' = lv'' + 1%nat }+
      { ~ exists n, exists lv', level_in s.(st_par_set) s.(st_par_map) n lv' }.

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

  Parameter olv_eq_dec : forall (lvo lvo' : option lv), { lvo = lvo' }+{ lvo <> lvo' }.

  Parameter level_spec_none : 
    forall ns nl, level ns nl = None -> ~ exists n, exists lv', level_in ns nl n lv'.

  Parameter level_spec_some : 
    forall ns nl lv5, level ns nl = Some lv5 -> exists n, exists lv', min_level ns nl n lv' /\ lv5 = lv' + 1.

  Parameter level_add_bot_eq : 
    forall ns nl n, NMap.find n nl = None -> level ns nl = level (NSet.add n ns) nl.

  Parameter level_empty_map_none : 
    forall ns, level ns (NMap.empty lv) = None.

  Parameter levels_some_level_ge : forall ns nl n lv5, 
      NSet.In n ns -> NMap.find n nl = Some lv5 -> 
      exists lv', level ns nl = Some lv' /\ lv' <= lv5 + 1.

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

    Parameter fold_left_level_fold_eq :
      forall ns nml olv,
        fold_left (fun l n => level_fold olv n l) ns nml = fold_left (fun l n => level_fold olv n l) ns [] ++ nml.

  End LevelFolds.
  
End TAux.

Module NameTypeTAux (Import NT : NameType)  
       (NOT : NameOrderedType NT) (NSet : MSetInterface.S with Module E := NOT) 
       (NOTC : NameOrderedTypeCompat NT) (NMap : FMapInterface.S with Module E := NOTC) <:
  TAux NT NOT NSet NOTC NMap.

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

  Lemma level_spec_none : 
    forall ns nl, level ns nl = None ->
             ~ exists n, exists lv', level_in ns nl n lv'.
  Proof.
    move => ns nl.
    rewrite /level.
    case lev => //.
      by case => /= lv' H_lv H_eq.
  Qed.

  Lemma level_spec_some : 
    forall ns nl lv5, level ns nl = Some lv5 ->
                 exists n, exists lv', min_level ns nl n lv' /\ lv5 = lv' + 1.
  Proof.
    move => ns nl lv5.
    rewrite /level.
    case lev => //.
    case => /= lv' H_ex H_eq.
      by find_injection.
  Qed.

  Lemma level_add_bot_eq : forall ns nl n,
      NMap.find n nl = None ->
      level ns nl = level (NSet.add n ns) nl.
  Proof.
    move => ns nl n H_find.
    case H_eq: level => [lv5|].
    apply level_spec_some in H_eq as [n' [lv6 [H_min H_eq]]].
    inversion H_min; subst.
    inversion H; subst.
    case H_eq': level => [lv7|].
    apply level_spec_some in H_eq' as [n'' [lv8 [H_min' H_eq']]].
    inversion H_min'; subst.
    inversion H3; subst.
    apply NSetFacts.add_3 in H5; last by move => H_eq'; rewrite -H_eq' H_find in H6.
    case (lv_eq_dec lv6 lv8) => H_eq; first by rewrite H_eq.
    contradict H_eq.
    have H_lt_lv6: ~ lv8 < lv6.
    apply (H0 _ n'').
    exact: in_level_in.
    have H_lt_lv8: ~ lv6 < lv8.
    apply (H4 _ n').
    apply: in_level_in => //.
    exact: NSetFacts.add_2.
    case (lt_eq_lt_dec lv6 lv8) => //.
      by case.
      apply level_spec_none in H_eq'.
      case: H_eq'.
      exists n'; exists lv6.
      apply: in_level_in => //.
      exact: NSetFacts.add_2.
      apply level_spec_none in H_eq.
      case H_eq': level => [lv6|] //.
      apply level_spec_some in H_eq' as [n' [lv7 [H_min H_eq']]].
      inversion H_min; subst.
      inversion H; subst.
      apply NSetFacts.add_3 in H1.
      case: H_eq.
      exists n'; exists lv7.
      exact: in_level_in.
      move => H_eq'.
        by rewrite -H_eq' H_find in H2.
  Qed.

  Lemma level_empty_map_none : 
    forall ns, level ns (NMap.empty lv) = None.
  Proof.
    move => ns.
    case H_eq: level => [lv5|] //.
    apply level_spec_some in H_eq.
    move: H_eq => [n [lv' [H_min H_eq]]].
    inversion H_min.
    inversion H.
    apply NMapFacts.find_mapsto_iff in H2.
      by apply NMapFacts.empty_mapsto_iff in H2.
  Qed.

  Lemma levels_some_level_ge : 
    forall ns nl n lv5,
      NSet.In n ns ->
      NMap.find n nl = Some lv5 ->
      exists lv', level ns nl = Some lv' /\ lv' <= lv5 + 1.
  Proof.
    move => ns nl n lv5 H_ins H_find.
    rewrite /level.
    case lev.
    case => lv' /=.
    move => [n' [lv'0 [H_min H_eq]]].
    rewrite H_eq {H_eq}.
    case (lt_eq_lt_dec lv5 lv'0) => H_dec; first case: H_dec => H_dec.
    - inversion H_min.
      have H_lv: level_in ns nl n lv5 by exact: in_level_in.
        by apply H0 in H_lv.
    - rewrite H_dec.
        by exists (lv'0 + 1).
             - exists (lv'0 + 1).
               split => //.
                 by auto with arith.
                 move => H_ex.
                 case: H_ex.
                 exists n; exists lv5.
                 rewrite /=.
                 exact: in_level_in.
  Qed.

  Class TreeMsg :=
    {
      tree_msg : Type ;
      tree_level : option lv -> tree_msg
    }.

  Definition level_fold {tr_msg : TreeMsg} (lvo : option lv) (n : name) (partial : list (name * tree_msg)) : list (name * tree_msg) :=
    (n, tree_level lvo) :: partial.

  Definition level_adjacent {tr_msg : TreeMsg} (lvo : option lv) (fs : NS) : list (name * tree_msg) :=
    NSet.fold (level_fold lvo) fs [].

  Lemma fold_left_level_fold_eq {tr_msg : TreeMsg} :
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
End NameTypeTAux.
