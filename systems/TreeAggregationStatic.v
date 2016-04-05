Require Import Verdi.
Require Import HandlerMonad.
Require Import StructTact.Fin.
Require Import NameOverlay.

Require Import TotalMapSimulations.
Require Import PartialMapSimulations.
Require Import PartialExtendedMapSimulations.

Require Import UpdateLemmas.
Local Arguments update {_} {_} _ _ _ _ : simpl never.

Require Import Sumbool.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.fingroup.fingroup.

Require Import Orders.
Require Import MSetFacts.
Require Import MSetProperties.

Require Import Sorting.Permutation.

Require Import AAC_tactics.AAC.

Require Import FailureRecorderStatic.
Require Import AggregationStatic.

Set Implicit Arguments.

Class NameOverlayRootParams `(N : NameOverlayParams) :=
  {
    root : name -> Prop ;
    root_dec : forall n, {root n} + {~ root n} ;
    root_unique : forall n n', root n -> root n' -> n = n'
  }.

Module TreeAggregation (N : NatValue) (CFG : CommutativeFinGroup).

Module AGN := Aggregation N CFG.
Import AGN.FRN.AN.

Import CFG.

Import GroupScope.

Module FinNSetFacts := Facts FinNSet.
Module FinNSetProps := Properties FinNSet.
Module FinNSetOrdProps := OrdProperties FinNSet.

Definition m := gT.

Definition lv := nat.
Definition lv_eq_dec := Nat.eq_dec.

Definition m_eq_dec := AGN.m_eq_dec.

Inductive Msg := 
| Aggregate : m -> Msg
| Fail : Msg
| Level : option lv -> Msg.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality; first exact: m_eq_dec.
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
| Local : m -> Input
| SendAggregate : Input
| AggregateRequest : Input
| LevelRequest : Input
| Broadcast : Input.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
decide equality.
exact: m_eq_dec.
Defined.

Inductive Output :=
| AggregateResponse : m -> Output
| LevelResponse : option lv -> Output.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
decide equality; first exact: m_eq_dec.
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

Definition FinNM := FinNMap.t m.
Definition FinNL := FinNMap.t nat.

Record Data :=  mkData { 
  local : m ; 
  aggregate : m ; 
  adjacent : FinNS ; 
  sent : FinNM ; 
  received : FinNM ;
  broadcast : bool ; 
  levels : FinNL 
}.

Definition init_map := AGN.init_map.

Section RootAdjacency.

Context {fin_nop : NameOverlayParams Fin_n_NameParams}.
Context {root_params : NameOverlayRootParams fin_nop}.

Definition InitData (n : name) := 
if root_dec n then
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     sent := init_map (adjacency n nodes) ;
     received := init_map (adjacency n nodes) ;
     broadcast := true ;
     levels := FinNMap.empty lv |}
else
  {| local := 1 ;
     aggregate := 1 ;
     adjacent := adjacency n nodes ;
     sent := init_map (adjacency n nodes) ;
     received := init_map (adjacency n nodes) ;
     broadcast := false ;
     levels := FinNMap.empty lv |}.
                            
Inductive level_in (fs : FinNS) (fl : FinNL) (n : name) (lv' : lv) : Prop :=
| in_level_in : FinNSet.In n fs -> FinNMap.find n fl = Some lv' -> level_in fs fl n lv'.

Inductive min_level (fs : FinNS) (fl : FinNL) (n : name) (lv' : lv) : Prop :=
| min_lv_min : level_in fs fl n lv' -> 
  (forall (lv'' : lv) (n' : name), level_in fs fl n' lv'' -> ~ lv'' < lv') ->
  min_level fs fl n lv'.

Record st_par := mk_st_par { st_par_set : FinNS ; st_par_map : FinNL }.

Record nlv := mk_nlv { nlv_n : name ; nlv_lv : lv }.

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
      case (fin_eq_dec _ n n') => H_eq'; first by left.
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
  case (fin_eq_dec _ n n') => H_eq'.
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
  case (fin_eq_dec _ n n') => H_eq'.
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
  case (fin_eq_dec _ n n') => H_eq'.
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
  case (fin_eq_dec _ n n') => H_eq'.
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
  case (fin_eq_dec _ n nlv'.(nlv_n)) => H_eq'.
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

Definition parent (fs : FinNS) (fl : FinNL) : option name :=
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

Definition Handler (S : Type) := GenHandler (name * Msg) S Output unit.

Definition RootNetHandler (src : name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with 
| Aggregate m_msg => 
  match FinNMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := FinNMap.add src (m_src * m_msg) st.(received) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end
| Level _ => nop 
| Fail => 
  match FinNMap.find src st.(sent), FinNMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>    
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 ;
           adjacent := FinNSet.remove src st.(adjacent) ;
           sent := FinNMap.remove src st.(sent) ;
           received := FinNMap.remove src st.(received) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  | _, _ =>
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := FinNSet.remove src st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end
end.

Definition NonRootNetHandler (me src: name) (msg : Msg) : Handler Data :=
st <- get ;;
match msg with
| Aggregate m_msg => 
  match FinNMap.find src st.(received) with
  | None => nop
  | Some m_src => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) * m_msg ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := FinNMap.add src (m_src * m_msg) st.(received) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end
| Level None =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (FinNMap.remove src st.(levels))) then
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := st.(broadcast) ;
           levels := FinNMap.remove src st.(levels) |}
  else 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := true ;
           levels := FinNMap.remove src st.(levels) |}
| Level (Some lv') =>
  if olv_eq_dec (level st.(adjacent) st.(levels)) (level st.(adjacent) (FinNMap.add src lv' st.(levels))) then
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := st.(broadcast) ;
           levels := FinNMap.add src lv' st.(levels) |}
  else
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := true ;
           levels := FinNMap.add src lv' st.(levels) |}
| Fail => 
  match FinNMap.find src st.(sent), FinNMap.find src st.(received) with
  | Some m_snt, Some m_rcd =>    
    if olv_eq_dec (level st.(adjacent) st.(levels)) (level (FinNSet.remove src st.(adjacent)) (FinNMap.remove src st.(levels))) then
      put {| local := st.(local) ;
             aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 ;
             adjacent := FinNSet.remove src st.(adjacent) ;
             sent := FinNMap.remove src st.(sent) ;
             received := FinNMap.remove src st.(received) ;
             broadcast := st.(broadcast) ;
             levels := FinNMap.remove src st.(levels) |}
    else
      put {| local := st.(local) ;
             aggregate := st.(aggregate) * m_snt * (m_rcd)^-1 ;
             adjacent := FinNSet.remove src st.(adjacent) ;
             sent := FinNMap.remove src st.(sent) ;
             received := FinNMap.remove src st.(received) ;
             broadcast := true ;
             levels := FinNMap.remove src st.(levels) |}
  | _, _ => 
    put {| local := st.(local) ;
           aggregate := st.(aggregate) ;
           adjacent := FinNSet.remove src st.(adjacent) ;
           sent := st.(sent) ;
           received := st.(received) ;
           broadcast := st.(broadcast) ;
           levels := st.(levels) |}
  end
end.

Definition NetHandler (me src : name) (msg : Msg) : Handler Data :=
if root_dec me then RootNetHandler src msg 
else NonRootNetHandler me src msg.

Definition level_fold (lvo : option lv) (n : name) (partial : list (name * Msg)) : list (name * Msg) :=
(n, Level lvo) :: partial.

Definition level_adjacent (lvo : option lv) (fs : FinNS) : list (name * Msg) :=
FinNSet.fold (level_fold lvo) fs [].

Definition send_level_fold (lvo : option lv) (n : name) (res : Handler Data) : Handler Data :=
send (n, Level lvo) ;; res.

Definition send_level_adjacent (lvo : option lv) (fs : FinNS) : Handler Data :=
FinNSet.fold (send_level_fold lvo) fs nop.

Definition RootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg;
         aggregate := st.(aggregate) * m_msg * st.(local)^-1;
         adjacent := st.(adjacent);
         sent := st.(sent);
         received := st.(received);
         broadcast := st.(broadcast);
         levels := st.(levels) |}
| SendAggregate => nop
| AggregateRequest => 
  write_output (AggregateResponse st.(aggregate))
| Broadcast => 
  when st.(broadcast)
  (send_level_adjacent (Some 0) st.(adjacent) ;;
   put {| local := st.(local);
          aggregate := st.(aggregate);
          adjacent := st.(adjacent);
          sent := st.(sent);
          received := st.(received);
          broadcast := false;
          levels := st.(levels) |})
| LevelRequest => 
  write_output (LevelResponse (Some 0))
end.

Definition NonRootIOHandler (i : Input) : Handler Data :=
st <- get ;;
match i with
| Local m_msg => 
  put {| local := m_msg; 
         aggregate := st.(aggregate) * m_msg * st.(local)^-1;
         adjacent := st.(adjacent); 
         sent := st.(sent);
         received := st.(received);
         broadcast := st.(broadcast);
         levels := st.(levels) |}
| SendAggregate => 
  when (sumbool_not _ _ (m_eq_dec st.(aggregate) 1))
  (match parent st.(adjacent) st.(levels) with
  | None => nop
  | Some dst => 
    match FinNMap.find dst st.(sent) with
    | None => nop
    | Some m_dst =>   
      send (dst, (Aggregate st.(aggregate))) ;;
      put {| local := st.(local);
             aggregate := 1;
             adjacent := st.(adjacent);
             sent := FinNMap.add dst (m_dst * st.(aggregate)) st.(sent);
             received := st.(received);
             broadcast := st.(broadcast);
             levels := st.(levels) |}
    end
  end)
| AggregateRequest => 
  write_output (AggregateResponse st.(aggregate))
| Broadcast =>
  when st.(broadcast)
  (send_level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent) ;; 
  put {| local := st.(local);
         aggregate := st.(aggregate);
         adjacent := st.(adjacent);
         sent := st.(sent);
         received := st.(received);
         broadcast := false;
         levels := st.(levels) |})
| LevelRequest =>   
  write_output (LevelResponse (level st.(adjacent) st.(levels)))
end.

Definition IOHandler (me : name) (i : Input) : Handler Data :=
if root_dec me then RootIOHandler i 
else NonRootIOHandler i.

Instance TreeAggregation_BaseParams : BaseParams :=
  {
    data := Data;
    input := Input;
    output := Output
  }.

Instance TreeAggregation_MultiParams : MultiParams _ _ :=
  {
    msg  := Msg ;
    msg_eq_dec := Msg_eq_dec ;
    init_handlers := InitData ;
    net_handlers := fun dst src msg s =>
                      runGenHandler_ignore s (NetHandler dst src msg) ;
    input_handlers := fun nm msg s =>
                        runGenHandler_ignore s (IOHandler nm msg)
  }.

Instance TreeAggregation_FailMsgParams : FailMsgParams TreeAggregation_MultiParams :=
  {
    msg_fail := Fail
  }.

Lemma net_handlers_NetHandler :
  forall dst src m st os st' ms,
    net_handlers dst src m st = (os, st', ms) ->
    NetHandler dst src m st = (tt, os, st', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma NetHandler_cases : 
  forall dst src msg st out st' ms,
    NetHandler dst src msg st = (tt, out, st', ms) ->
    (exists m_msg m_src, msg = Aggregate m_msg /\ 
     FinNMap.find src st.(received) = Some m_src /\
     st'.(local) = st.(local) /\
     st'.(aggregate) = st.(aggregate) * m_msg /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\     
     st'.(received) = FinNMap.add src (m_src * m_msg) st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (exists m_msg, msg = Aggregate m_msg /\ 
     FinNMap.find src st.(received) = None /\ 
     st' = st /\ 
     out = [] /\ ms = []) \/
    (root dst /\ msg = Fail /\ 
     exists m_snt m_rcd, FinNMap.find src st.(sent) = Some m_snt /\ FinNMap.find src st.(received) = Some m_rcd /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = FinNMap.remove src st.(sent) /\
     st'.(received) = FinNMap.remove src st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     exists m_snt m_rcd, FinNMap.find src st.(sent) = Some m_snt /\ FinNMap.find src st.(received) = Some m_rcd /\
     level st.(adjacent) st.(levels) = level (FinNSet.remove src st.(adjacent)) (FinNMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = FinNMap.remove src st.(sent) /\
     st'.(received) = FinNMap.remove src st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = FinNMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Fail /\ 
     exists m_snt m_rcd, FinNMap.find src st.(sent) = Some m_snt /\ FinNMap.find src st.(received) = Some m_rcd /\
     level st.(adjacent) st.(levels) <> level (FinNSet.remove src st.(adjacent)) (FinNMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) * m_snt * (m_rcd)^-1 /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = FinNMap.remove src st.(sent) /\
     st'.(received) = FinNMap.remove src st.(received) /\
     st'.(broadcast) = true /\
     st'.(levels) = FinNMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (msg = Fail /\ (FinNMap.find src st.(sent) = None \/ FinNMap.find src st.(received) = None) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = FinNSet.remove src st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = st.(levels) /\
     out = [] /\ ms = []) \/
    (root dst /\ exists lvo, msg = Level lvo /\ 
     st' = st /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (FinNMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = FinNMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ exists lv_msg, msg = Level (Some lv_msg) /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (FinNMap.add src lv_msg st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     st'.(broadcast) = true /\
     st'.(levels) = FinNMap.add src lv_msg st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) = level st.(adjacent) (FinNMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     st'.(broadcast) = st.(broadcast) /\
     st'.(levels) = FinNMap.remove src st.(levels) /\
     out = [] /\ ms = []) \/
    (~ root dst /\ msg = Level None /\
     level st.(adjacent) st.(levels) <> level st.(adjacent) (FinNMap.remove src st.(levels)) /\
     st'.(local) = st.(local) /\ 
     st'.(aggregate) = st.(aggregate) /\
     st'.(adjacent) = st.(adjacent) /\
     st'.(sent) = st.(sent) /\
     st'.(received) = st.(received) /\
     st'.(broadcast) = true /\
     st'.(levels) = FinNMap.remove src st.(levels) /\
     out = [] /\ ms = []).
Proof.
move => dst src msg st out st' ms.
rewrite /NetHandler /RootNetHandler /NonRootNetHandler.
case: msg => [m_msg||olv_msg]; monad_unfold.
- case root_dec => /= H_dec; case H_find: (FinNMap.find _ _) => [m_src|] /= H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
  * by left; exists m_msg; exists m_src.
  * by right; left; exists m_msg.
  * by left; exists m_msg; exists m_src.
  * by right; left; exists m_msg.
- case root_dec => /= H_dec; case H_find: (FinNMap.find _ _) => [m_snt|]; case H_find': (FinNMap.find _ _) => [m_rcd|] /=.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; left.
    split => //.
    split => //.
    by exists m_snt; exists m_rcd.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by right.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by left.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by left.
  * case olv_eq_dec => /= H_dec' H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
      right; right; right; left.
      split => //.
      split => //.
      by exists m_snt; exists m_rcd.
    right; right; right; right; left.
    split => //.
    split => //.
    by exists m_snt; exists m_rcd.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by right.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by left.
  * move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; left.
    split => //.
    by split; first by left.
- case root_dec => /= H_dec.
    move => H_eq.
    injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
    right; right; right; right; right; right; left.
    split => //.
    by exists olv_msg.
  case H_olv_dec: olv_msg => [lv_msg|]; case olv_eq_dec => /= H_dec' H_eq; injection H_eq => H_ms H_st H_out; rewrite -H_st /=.
  * right; right; right; right; right; right; right; left.
    split => //.
    by exists lv_msg.
  * right; right; right; right; right; right; right; right; left.
    split => //.
    by exists lv_msg.
  * by right; right; right; right; right; right; right; right; right; left.
  * by right; right; right; right; right; right; right; right; right; right.
Qed.

Lemma input_handlers_IOHandler :
  forall h i d os d' ms,
    input_handlers h i d = (os, d', ms) ->
    IOHandler h i d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u. auto.
Qed.

Lemma fold_left_level_fold_eq :
forall ns nml olv,
fold_left (fun l n => level_fold olv n l) ns nml = fold_left (fun l n => level_fold olv n l) ns [] ++ nml.
Proof.
elim => //=.
move => n ns IH nml olv.
rewrite /level_fold /=.
rewrite IH.
have IH' := IH ([(n, Level olv)]).
rewrite IH'.
set bla := fold_left _ _ _.
rewrite -app_assoc.
by rewrite app_assoc.
Qed.

Lemma send_level_fold_app :
  forall ns st olv nm,
snd (fold_left 
       (fun (a : Handler Data) (e : FinNSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, nm)) st) = 
snd (fold_left 
       (fun (a : Handler Data) (e : FinNSet.elt) => send_level_fold olv e a) ns
       (fun s : Data => (tt, [], s, [])) st) ++ nm.
Proof.
elim => //=.
move => n ns IH st olv nm.
rewrite {1}/send_level_fold /=.
monad_unfold.
rewrite /=.
rewrite IH.
rewrite app_assoc.
by rewrite -IH.
Qed.

Lemma send_level_adjacent_fst_eq : 
forall fs olv st,
  snd (send_level_adjacent olv fs st) = level_adjacent olv fs.
Proof.
move => fs olv st.
rewrite /send_level_adjacent /level_adjacent.
rewrite 2!FinNSet.fold_spec.
move: olv st.
elim: FinNSet.elements => [|n ns IH] //=.
move => olv st.
rewrite {2}/level_fold {2}/send_level_fold.
rewrite fold_left_level_fold_eq.
have IH' := IH olv st.
rewrite -IH'.
monad_unfold.
by rewrite -send_level_fold_app.
Qed.

Lemma fst_fst_fst_tt_send_level_fold : 
forall ns nm olv st,
fst
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : FinNSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = tt.
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma send_level_adjacent_fst_fst_eq : 
forall fs olv st,
  fst (fst (fst (send_level_adjacent olv fs st))) = tt.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite FinNSet.fold_spec.
by rewrite fst_fst_fst_tt_send_level_fold.
Qed.

Lemma snd_fst_fst_out_send_level_fold : 
forall ns nm olv st,
snd
  (fst
     (fst
        (fold_left
           (fun (a : Handler Data) (e : FinNSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st))) = [].
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma snd_fst_st_send_level_fold : 
forall ns nm olv st,
snd (fst
        (fold_left
           (fun (a : Handler Data) (e : FinNSet.elt) =>
              send_level_fold olv e a) ns
           (fun s : Data => (tt, [], s, nm)) st)) = st.
Proof.
elim => //=.
move => n ns IH nm olv st.
by rewrite IH.
Qed.

Lemma send_level_adjacent_snd_fst_fst : 
forall fs olv st,
  snd (fst (fst (send_level_adjacent olv fs st))) = [].
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite FinNSet.fold_spec.
by rewrite snd_fst_fst_out_send_level_fold.
Qed.

Lemma send_level_adjacent_snd_fst : 
forall fs olv st,
  snd (fst (send_level_adjacent olv fs st)) = st.
Proof.
move => fs olv st.
rewrite /send_level_adjacent.
rewrite FinNSet.fold_spec.
by rewrite snd_fst_st_send_level_fold.
Qed.

Lemma send_level_adjacent_eq : 
  forall fs olv st,
  send_level_adjacent olv fs st = (tt, [], st, level_adjacent olv fs).
Proof.
move => fs olv st.
case H_eq: send_level_adjacent => [[[u o] s b]].
have H_eq'_1 := send_level_adjacent_fst_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_1.
have H_eq'_2 := send_level_adjacent_fst_eq fs olv st.
rewrite H_eq /= in H_eq'_2.
have H_eq'_3 := send_level_adjacent_snd_fst_fst fs olv st.
rewrite H_eq /= in H_eq'_3.
have H_eq'_4 := send_level_adjacent_snd_fst fs olv st.
rewrite H_eq /= in H_eq'_4.
by rewrite H_eq'_1 H_eq'_2 H_eq'_3 H_eq'_4.
Qed.

Lemma IOHandler_cases :
  forall h i st u out st' ms,
      IOHandler h i st = (u, out, st', ms) ->
      (exists m_msg, i = Local m_msg /\ 
         st'.(local) = m_msg /\ 
         st'.(aggregate) = st.(aggregate) * m_msg * st.(local)^-1 /\ 
         st'.(adjacent) = st.(adjacent) /\
         st'.(sent) = st.(sent) /\
         st'.(received) = st.(received) /\
         st'.(broadcast) = st.(broadcast) /\
         st'.(levels) = st.(levels) /\
         out = [] /\ ms = []) \/
      (root h /\ i = SendAggregate /\ 
         st' = st /\
         out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\ 
       st.(aggregate) <> 1 /\ 
       exists dst m_dst, parent st.(adjacent) st.(levels) = Some dst /\ FinNMap.find dst st.(sent) = Some m_dst /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = 1 /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(sent) = FinNMap.add dst (m_dst * st.(aggregate)) st.(sent) /\
       st'.(received) = st.(received) /\
       st'.(broadcast) = st.(broadcast) /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = [(dst, Aggregate st.(aggregate))]) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) = 1 /\
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 1 /\
       parent st.(adjacent) st.(levels) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (~ root h /\ i = SendAggregate /\
       st.(aggregate) <> 1 /\
       exists dst, parent st.(adjacent) st.(levels) = Some dst /\ FinNMap.find dst st.(sent) = None /\ 
       st' = st /\
       out = [] /\ ms = []) \/
      (i = AggregateRequest /\ 
       st' = st /\ 
       out = [AggregateResponse (aggregate st)] /\ ms = []) \/
      (root h /\ i = Broadcast /\ st.(broadcast) = true /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(sent) = st.(sent) /\
       st'.(received) = st.(received) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (Some 0) st.(adjacent)) \/
      (~ root h /\ i = Broadcast /\ st.(broadcast) = true /\
       st'.(local) = st.(local) /\
       st'.(aggregate) = st.(aggregate) /\ 
       st'.(adjacent) = st.(adjacent) /\
       st'.(sent) = st.(sent) /\
       st'.(received) = st.(received) /\
       st'.(broadcast) = false /\
       st'.(levels) = st.(levels) /\
       out = [] /\ ms = level_adjacent (level st.(adjacent) st.(levels)) st.(adjacent)) \/
      (i = Broadcast /\ st.(broadcast) = false /\
       st' = st /\
       out = [] /\ ms = []) \/
      (root h /\ i = LevelRequest /\
       st' = st /\
       out = [LevelResponse (Some 0)] /\ ms = []) \/
      (~ root h /\ i = LevelRequest /\
       st' = st /\
       out = [LevelResponse (level st.(adjacent) st.(levels))] /\ ms = []).      
Proof.
move => h i st u out st' ms.
rewrite /IOHandler /RootIOHandler /NonRootIOHandler.
case: i => [m_msg||||]; monad_unfold.
- by case root_dec => /= H_dec H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=; left; exists m_msg.
- case root_dec => /= H_dec. 
    by move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=; right; left.
  case sumbool_not => /= H_not; last first. 
    by move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=; right; right; right; left.
  case H_p: parent => [dst|]; last first. 
    by move => H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=; right; right; right; right; left.
  case H_find: FinNMap.find => [m_dst|] H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    right; right; left.
    split => //.
    split => //.
    split => //.
    by exists dst; exists m_dst.
  right; right; right; right; right; left.
  split => //.
  split => //.
  split => //.
  by exists dst.
- by case root_dec => /= H_dec H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=; right; right; right; right; right; right; left.
- case root_dec => /= H_dec H_eq; injection H_eq => H_ms H_st H_out H_tt; rewrite -H_st /=.
    by right; right; right; right; right; right; right; right; right; right; left.
  by right; right; right; right; right; right; right; right; right; right; right.
- case root_dec => /= H_dec; case H_b: broadcast => /=.
  * right; right; right; right; right; right; right; left.
    repeat break_let.
    injection Heqp => H_ms H_st H_out H_tt.
    subst.
    injection Heqp2 => H_ms H_st H_out H_tt.
    subst.
    injection H => H_ms H_st H_out H_tt.
    subst.
    rewrite /=.
    have H_eq := send_level_adjacent_eq st.(adjacent) (Some 0) st.
    rewrite Heqp5 in H_eq.
    injection H_eq => H_eq_ms H_eq_st H_eq_o H_eq_tt.
    rewrite H_eq_ms H_eq_o.
    by rewrite app_nil_l -2!app_nil_end.
  * right; right; right; right; right; right; right; right; right; left.
    injection H => H_ms H_st H_o H_tt.
    by rewrite H_st H_o H_ms.
  * right; right; right; right; right; right; right; right; left.
    repeat break_let.
    injection Heqp => H_ms H_st H_out H_tt.
    subst.
    injection Heqp2 => H_ms H_st H_out H_tt.
    subst.
    injection H => H_ms H_st H_out H_tt.
    subst.
    rewrite /=.
    have H_eq := send_level_adjacent_eq st.(adjacent) (level st.(adjacent) st.(levels)) st.
    rewrite Heqp5 in H_eq.
    injection H_eq => H_eq_ms H_eq_st H_eq_o H_eq_tt.
    rewrite H_eq_ms H_eq_o.
    by rewrite app_nil_l -2!app_nil_end.
  * right; right; right; right; right; right; right; right; right; left.
    injection H => H_ms H_st H_o H_tt.
    by rewrite H_st H_o H_ms.
Qed.

Ltac net_handler_cases := 
  find_apply_lem_hyp NetHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Ltac io_handler_cases := 
  find_apply_lem_hyp IOHandler_cases; 
  intuition idtac; try break_exists; 
  intuition idtac; subst; 
  repeat find_rewrite.

Instance TreeAggregation_Aggregation_name_params_tot_map : NameParamsTotalMap Fin_n_NameParams AGN.FRN.AN.Fin_n_NameParams :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

Instance TreeAggregation_Aggregation_params_pt_ext_map : MultiParamsPartialExtendedMap TreeAggregation_Aggregation_name_params_tot_map TreeAggregation_MultiParams AGN.Aggregation_MultiParams :=
  {
    pt_ext_map_data := fun d _ => 
      AGN.mkData d.(local) d.(aggregate) d.(adjacent) d.(sent) d.(received) ;
    pt_ext_map_input := fun i n d =>
      match i with 
      | Local m => Some (AGN.Local m)
      | SendAggregate => 
        if root_dec n then None else
          match parent d.(adjacent) d.(levels) with
          | Some p => Some (AGN.SendAggregate p)
          | None => None
          end
      | AggregateRequest => (Some AGN.AggregateRequest)
      | _ => None
      end ;
    pt_ext_map_output := fun o => 
      match o with 
      | AggregateResponse m => Some (AGN.AggregateResponse m) 
      | _ => None 
      end ;
    pt_ext_map_msg := fun m => 
      match m with 
      | Aggregate m' => Some (AGN.Aggregate m')
      | Fail => Some AGN.Fail      
      | Level _ => None 
      end   
  }.

Lemma tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n.
Proof. by []. Qed.

Lemma tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n.
Proof. by []. Qed.

Lemma pt_ext_init_handlers_eq : forall n,
  @pt_ext_map_data _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map (init_handlers n) n = @init_handlers _ _ AGN.Aggregation_MultiParams (tot_map_name n).
Proof.
move => n.
rewrite /= /InitData /=.
by case root_dec => /= H_dec.
Qed.

Lemma pt_ext_net_handlers_some : forall me src m st m',
  @pt_ext_map_msg _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map m = Some m' ->
  pt_ext_mapped_net_handlers me src m st = net_handlers (tot_map_name me) (tot_map_name src) m' (@pt_ext_map_data _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map st me).
Proof.
move => me src.
case => //.
  move => m' st mg.
  rewrite /pt_ext_map_msg /=.
  rewrite /pt_ext_mapped_net_handlers /=.
  repeat break_let.
  move => H_eq.
  inversion H_eq.
  rewrite /id /=.
  apply net_handlers_NetHandler in Heqp.
  net_handler_cases => //.
    injection H1 => H_eqx.
    rewrite H_eqx.
    monad_unfold.
    repeat break_let.
    rewrite /=.
    move: Heqp.
    rewrite /AGN.NetHandler /=.
    monad_unfold.
    break_let.
    move: Heqp2.
    case H_find: FinNMap.find => /= [m0|]; last by rewrite H in H_find.
    rewrite H in H_find.
    injection H_find => H_eq_m.
    rewrite H_eq_m.
    repeat break_let.
    move => Heqp Heqp'.      
    rewrite Heqp' in Heqp.
    by inversion Heqp.
  rewrite /=.
  monad_unfold.
  repeat break_let.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  case H_find: FinNMap.find => /= [m0|]; first by rewrite H in H_find.
  repeat break_let.
  move => Heqp Heqp'.
  rewrite Heqp' in Heqp.
  by inversion Heqp.
move => st.
case => //.
rewrite /pt_ext_map_msg /=.
rewrite /pt_ext_mapped_net_handlers /=.
repeat break_let.
move => H_eq.
inversion H_eq.
rewrite /id /=.
apply net_handlers_NetHandler in Heqp.
net_handler_cases => //.
* monad_unfold.
  repeat break_let.
  rewrite /=.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  case H_find: FinNMap.find => /= [m0|]; last by rewrite H2 in H_find.
  case H_find': FinNMap.find => /= [m1|]; last by rewrite H1 in H_find'.
  rewrite H2 in H_find.
  injection H_find => H_eq_m.
  rewrite H_eq_m.
  rewrite H1 in H_find'.
  injection H_find' => H_eq'_m.
  rewrite H_eq'_m.
  repeat break_let.
  move => Heqp Heqp'.
  rewrite Heqp' in Heqp.
  by inversion Heqp.
* monad_unfold.
  repeat break_let.
  rewrite /=.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  case H_find: FinNMap.find => /= [m0|]; last by rewrite H2 in H_find.
  case H_find': FinNMap.find => /= [m1|]; last by rewrite H1 in H_find'.
  rewrite H2 in H_find.
  injection H_find => H_eq_m.
  rewrite H_eq_m.
  rewrite H1 in H_find'.
  injection H_find' => H_eq'_m.
  rewrite H_eq'_m.
  repeat break_let.
  move => Heqp Heqp'.
  rewrite Heqp' in Heqp.
  by inversion Heqp.
* monad_unfold.
  repeat break_let.
  rewrite /=.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  case H_find: FinNMap.find => /= [m0|]; last by rewrite H2 in H_find.
  case H_find': FinNMap.find => /= [m1|]; last by rewrite H1 in H_find'.
  rewrite H2 in H_find.
  injection H_find => H_eq_m.
  rewrite H_eq_m.
  rewrite H1 in H_find'.
  injection H_find' => H_eq'_m.
  rewrite H_eq'_m.
  repeat break_let.
  move => Heqp Heqp'.
  rewrite Heqp' in Heqp.
  by inversion Heqp.
* rewrite /=.
  monad_unfold.
  repeat break_let.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  case H_find: FinNMap.find => /= [m0|]; first by rewrite H9 in H_find.
  repeat break_let.
  move => Heqp Heqp'.      
  rewrite Heqp' in Heqp.
  by inversion Heqp.
* rewrite /=.
  monad_unfold.
  repeat break_let.
  move: Heqp.
  rewrite /AGN.NetHandler /=.
  monad_unfold.
  break_let.
  move: Heqp2.
  rewrite /=.
  case H_find': (FinNMap.find _  st.(received)) => /= [m1|]; first by rewrite H9 in H_find'.
  case H_find: FinNMap.find => /= [m0|].
    repeat break_let.
    move => Heqp Heqp'.      
    rewrite Heqp' in Heqp.
    by inversion Heqp.
  repeat break_let.
  move => Heqp Heqp'.      
  rewrite Heqp' in Heqp.
  by inversion Heqp.
Qed.

Lemma pt_ext_net_handlers_none : forall me src m st out st' ps,
  @pt_ext_map_msg _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map m = None ->
  net_handlers me src m st = (out, st', ps) ->
  @pt_ext_map_data _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map st' me = @pt_ext_map_data _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map st me /\ @pt_ext_map_name_msgs _ _ _ _ _ _ _ TreeAggregation_Aggregation_params_pt_ext_map ps = [].
Proof.
move => me src.
case => //.
move => m' d out d' ps H_eq H_eq'.
apply net_handlers_NetHandler in H_eq'.
net_handler_cases => //.
* case: d' H0 H2 H3 H4 H5 H6 H7 H8 => /=. 
  move => local0 aggregate0 adjacent0 sent0 received0 broadcast0 levels0.
  move => H0 H2 H3 H4 H5 H6 H7 H8.
  by rewrite H2 H3 H4 H5 H6.
* case: d' H0 H2 H3 H4 H5 H6 H7 H8 => /=. 
  move => local0 aggregate0 adjacent0 sent0 received0 broadcast0 levels0.
  move => H0 H2 H3 H4 H5 H6 H7 H8.
  by rewrite H2 H3 H4 H5 H6.
* case: d' H0 H2 H3 H4 H5 H6 H7 H8 => /=. 
  move => local0 aggregate0 adjacent0 sent0 received0 broadcast0 levels0.
  move => H0 H2 H3 H4 H5 H6 H7 H8.
  by rewrite H2 H3 H4 H5 H6.
* case: d' H0 H2 H3 H4 H5 H6 H7 H8 => /=. 
  move => local0 aggregate0 adjacent0 sent0 received0 broadcast0 levels0.
  move => H0 H2 H3 H4 H5 H6 H7 H8.
  by rewrite H2 H3 H4 H5 H6.
Qed.

(* BLA *)

Lemma pt_ext_input_handlers_some : forall me inp st inp',
  pt_ext_map_input inp me st = Some inp' ->
  pt_ext_mapped_input_handlers me inp st = input_handlers (tot_map_name me) inp' (pt_ext_map_data st me).
Proof.
move => me.
case => //.
- move => m' st.
  case => //=.
  move => m'' H_eq.
  injection H_eq => H_eq'.
  rewrite H_eq' {H_eq H_eq'}.
  rewrite /pt_ext_mapped_input_handlers.
  repeat break_let.  
  rewrite /id /=.
  apply input_handlers_IOHandler in Heqp.
  io_handler_cases => //.
  monad_unfold.
  repeat break_let.
  move: Heqp.
  injection H0 => H_eq_m.
  rewrite -H_eq_m {H_eq_m H0}.
  rewrite /AM.IOHandler.
  monad_unfold.
  rewrite /=.
  move => Heqp.
  by inversion Heqp.
- move => st.
  case => //=; first by move => m'; case root_dec => H_dec //=; case: parent.
    move => dst.
    case root_dec => H_dec //=.
    case H_p: parent => [dst'|] H_eq //=.
    rewrite /id /=.
    injection H_eq => H_eq'.
    rewrite -H_eq' {H_eq H_eq'}.
    rewrite /pt_ext_mapped_input_handlers.
    repeat break_let.      
    apply input_handlers_IOHandler in Heqp.
    have H_p' := H_p.
    move: H_p'.
    rewrite /parent.
    case par => H_p' H_eq //=.
    move: H_p' H_eq => /= [nlv' H_min].
    inversion H_min.
    inversion H.
    move => H_eq.
    injection H_eq => H_eq'.
    rewrite -H_eq'.
    rewrite -H_eq' in H_p.
    move {H_eq' H_eq dst'}.
    io_handler_cases => //=.
    * rewrite /id /=.
      injection H7 => H_eq.
      rewrite -H_eq in H6.
      rewrite -H_eq.
      monad_unfold.
      repeat break_let.
      move: Heqp.      
      rewrite /AM.IOHandler.
      monad_unfold.
      rewrite /=.
      repeat break_let.
      move: Heqp2.
      case H_mem: FinNSet.mem => /=; last by move/negP: H_mem => H_mem; case: H_mem; apply FinNSetFacts.mem_1.
      case sumbool_not => //= H_not.
      repeat break_let.
      move: Heqp2.
      case H_find: AM.FinNMap.find => [m0|]; last by rewrite H_find in H6.
      rewrite H_find in H6.
      injection H6 => H_eq'.
      rewrite H_eq'.
      move => H_eq_p H_eq'_p H_eq''_p.
      inversion H_eq''_p.
      subst.
      inversion H_eq'_p; subst.
      rewrite -2!app_nil_end.
      by inversion H_eq_p.
    * monad_unfold.
      repeat break_let.
      move: Heqp.      
      rewrite /AM.IOHandler.
      monad_unfold.
      repeat break_let.
      move: Heqp2.
      case H_mem: FinNSet.mem => /=; last by move/negP: H_mem => H_mem; case: H_mem; apply FinNSetFacts.mem_1.
      case sumbool_not => //= H_not.
      move => H_eq H_eq'.
      rewrite H_eq' in H_eq.
      by inversion H_eq.
    * injection H7 => H_eq.
      rewrite -H_eq in H6.
      monad_unfold.
      repeat break_let.
      move: Heqp.
      rewrite /AM.IOHandler.
      monad_unfold.
      repeat break_let.
      move: Heqp2.
      case H_mem: FinNSet.mem => /=; last by move/negP: H_mem => H_mem; case: H_mem; apply FinNSetFacts.mem_1.
      case sumbool_not => //= H_not.
      repeat break_let.
      move: Heqp2.
      case H_find: AM.FinNMap.find => [m0|]; first by rewrite H_find in H6.
      rewrite -2!app_nil_end.
      move => H_eq_1 H_eq_2 H_eq3.
      inversion H_eq3; subst.
      inversion H_eq_2; subst.
      by inversion H_eq_1.
    * by case root_dec => //= H_dec; case: parent.
- move => st.
  case => //.
  rewrite /pt_ext_map_input /= => H_eq.
  rewrite /pt_ext_mapped_input_handlers.
  repeat break_let.  
  rewrite /id /=.
  apply input_handlers_IOHandler in Heqp.
  by io_handler_cases.
Qed.

Lemma pt_ext_map_name_msgs_level_adjacent_empty : 
  forall fs lvo,
  pt_ext_map_name_msgs (level_adjacent lvo fs) = [].
Proof.
move => fs lvo.
rewrite /level_adjacent FinNSet.fold_spec.
elim: FinNSet.elements => //=.
move => n ns IH.
rewrite {2}/level_fold /=.
rewrite fold_left_level_fold_eq /=.
by rewrite pt_ext_map_name_msgs_app_distr /= -app_nil_end IH.
Qed.

Lemma pt_ext_input_handlers_none : forall me inp st out st' ps,
  pt_ext_map_input inp me st = None ->
  input_handlers me inp st = (out, st', ps) ->
  pt_ext_map_data st' me = pt_ext_map_data st me /\ pt_ext_map_name_msgs ps = [].
Proof.
move => me.
case => //=.
- move => st out st' ps.
  case root_dec => /= H_dec.    
    move => H_eq.
    monad_unfold.
    repeat break_let.
    move => H_eq'.
    by io_handler_cases => //=; inversion H_eq'.
  case H_p: parent => [dst'|] H_eq //=.
  monad_unfold.
  repeat break_let.
  move => H_eq'.
  io_handler_cases; inversion H_eq' => //=.
  by rewrite -H4 H1.
- move => st out st' ps H_eq.
  monad_unfold.
  repeat break_let.
  move => H_eq'.
  by io_handler_cases; inversion H_eq' => //=.
- move => st out st' ps H_eq.
  monad_unfold.
  repeat break_let.
  move => H_eq'.
  io_handler_cases; inversion H_eq' => //=.
  * by rewrite -H2 -H3 -H4 -H5 -H6 H11.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
  * by rewrite -H2 -H3 -H4 -H5 -H6 H11.
  * by rewrite pt_ext_map_name_msgs_level_adjacent_empty.
Qed.

Lemma fail_msg_fst_snd : pt_ext_map_msg msg_fail = Some (msg_fail).
Proof. by []. Qed.

Lemma adjacent_to_fst_snd : 
  forall n n', adjacent_to n n' <-> adjacent_to (pt_ext_map_name n) (pt_ext_map_name n').
Proof. by []. Qed.

Theorem TreeAggregation_Aggregation_pt_ext_mapped_simulation_star_1 :
forall net failed tr,
    @step_o_f_star _ _ TreeAggregation_OverlayParams TreeAggregation_FailMsgParams step_o_f_init (failed, net) tr ->
    exists tr', @step_o_f_star _ _ AM.Aggregation_OverlayParams AM.Aggregation_FailMsgParams step_o_f_init (failed, pt_ext_map_onet net) tr'.
Proof.
have H_sim := step_o_f_pt_ext_mapped_simulation_star_1 pt_ext_map_name_inv_inverse pt_ext_map_name_inverse_inv pt_ext_init_handlers_eq pt_ext_net_handlers_some pt_ext_net_handlers_none pt_ext_input_handlers_some pt_ext_input_handlers_none adjacent_to_fst_snd fail_msg_fst_snd.
rewrite /pt_ext_map_name /= /id in H_sim.
move => onet failed tr H_st.
apply H_sim in H_st.
move: H_st => [tr' H_st].
rewrite map_id in H_st.
by exists tr'.
Qed.

End TreeAggregation.

