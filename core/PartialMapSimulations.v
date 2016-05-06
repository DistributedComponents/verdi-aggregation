Require Import List.
Import ListNotations.

Require Import Arith.
Require Import ZArith.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import StructTact.Util.

Require Import TotalMapSimulations.

Require Import UpdateLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import OrderedLemmas.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class BaseParamsPartialMap (P0 : BaseParams) (P1 : BaseParams) := 
  {
    pt_map_data : @data P0 -> @data P1 ;
    pt_map_input : @input P0 -> option (@input P1) ;
    pt_map_output : @output P0 -> option (@output P1)
  }.

Class MultiParamsPartialMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1) :=
  {
    pt_map_msg : @msg B0 P0 -> option (@msg B1 P1)
  }.

Section PartialMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialMap multi_fst multi_snd}.

Definition pt_map_name_msgs :=
  fold_right (fun nm l => 
                match pt_map_msg (snd nm) with
                | Some m => (tot_map_name (fst nm), m) :: l
                | None => l
                end) [].

Definition pt_map_outputs :=
  fold_right (fun o l =>
                match pt_map_output o with
                | Some o' => o' :: l
                | None => l
                end) [].

Definition pt_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (pt_map_outputs out, pt_map_data st', pt_map_name_msgs ps).

Definition pt_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (pt_map_outputs out, pt_map_data st', pt_map_name_msgs ps).

End PartialMapDefs.

Class MultiParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (B : BaseParamsPartialMap B0 B1) 
  (N : MultiParamsNameTotalMap P0 P1)
  (P : MultiParamsPartialMap P0 P1) :=
  {
    pt_init_handlers_eq : forall n, pt_map_data (init_handlers n) = init_handlers (tot_map_name n) ;
    pt_net_handlers_some : forall me src m st m',
        pt_map_msg m = Some m' ->
        pt_mapped_net_handlers me src m st = net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) ;    
    pt_net_handlers_none : forall me src m st out st' ps,
        pt_map_msg m = None ->
        net_handlers me src m st = (out, st', ps) ->
        pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = [] ;
    pt_input_handlers_some : forall me inp st inp',
        pt_map_input inp = Some inp' ->
        pt_mapped_input_handlers me inp st = input_handlers (tot_map_name me) inp' (pt_map_data st) ;
    pt_input_handlers_none : forall me inp st out st' ps,
        pt_map_input inp = None ->
        input_handlers me inp st = (out, st', ps) ->
        pt_map_data st' = pt_map_data st /\ pt_map_name_msgs ps = [] /\ pt_map_outputs out = []
  }.

Class FailMsgParamsPartialMapCongruency 
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailMsgParams P0) (F1 : FailMsgParams P1)
  (P : MultiParamsPartialMap P0 P1) :=
  {
    pt_fail_msg_fst_snd : pt_map_msg msg_fail = Some (msg_fail)
  }.

Section PartialMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map multi_map}.

Definition pt_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) :
 option (@name _ multi_snd * (@input base_snd + list (@output base_snd))) :=
match e with
| (n, inl io) => 
  match pt_map_input io with
  | Some io' => Some (tot_map_name n, inl io')
  | None => None
  end
| (n, inr out) => Some (tot_map_name n, inr (pt_map_outputs out))
end.

Definition pt_map_trace :=
fold_right (fun e l =>
              match pt_map_trace_occ e with
              | Some e' => e' :: l
              | None => l
              end) [].

Definition pt_map_packet (p : @packet _ multi_fst)  :=
match p with
| mkPacket src dst m =>
  match pt_map_msg m with
  | Some m' => Some (mkPacket (tot_map_name src) (tot_map_name dst) m')
  | None => None
  end
end.

Definition pt_map_packets :=
fold_right (fun p l =>
            match pt_map_packet p with
            | Some p' => p' :: l
            | None => l
            end) [].

Definition pt_map_net (net : @network _ multi_fst) : @network _ multi_snd :=
mkNetwork (pt_map_packets net.(nwPackets)) (fun n => pt_map_data (net.(nwState) (tot_map_name_inv n))).

Lemma pt_init_handlers_fun_eq : 
    init_handlers = fun n : name => pt_map_data (init_handlers (tot_map_name_inv n)).
Proof.
apply functional_extensionality => n.
have H_eq := pt_init_handlers_eq.
rewrite H_eq {H_eq}.
by rewrite tot_map_name_inverse_inv.
Qed.

Lemma pt_map_name_msgs_app_distr : 
  forall l l',
  pt_map_name_msgs (l ++ l') = pt_map_name_msgs l ++ pt_map_name_msgs l'.
Proof.
elim => //=.
case => n m l IH l'.
rewrite /= IH.
by case (pt_map_msg _) => [m'|].
Qed.

Lemma pt_map_packets_app_distr : 
  forall l l',
  pt_map_packets (l ++ l') = pt_map_packets l ++ pt_map_packets l'.
Proof.
elim => //=.
move => n l IH l'.
rewrite /= IH.
by case (pt_map_packet _).
Qed.

Lemma pt_map_name_msgs_empty_eq :
  forall l dst,
  pt_map_name_msgs l = [] ->
  pt_map_packets (map (fun m0 : name * msg => {| pSrc := dst; pDst := fst m0; pBody := snd m0 |}) l) = [].
Proof.
elim => //=.
case => n m l IH dst.
case H_m: (pt_map_msg _) => [m'|] //=.
move => H_eq.
by rewrite IH.
Qed.

Lemma pt_map_packet_map_app_eq :
  forall l h ms,
    pt_map_packets (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l ++ ms) = 
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (pt_map_name_msgs l) ++ pt_map_packets ms.
Proof.
move => l h ms.
elim: l => //=.
case => n m l IH.
case (pt_map_msg _) => [m'|] //.
by rewrite IH.
Qed.

Lemma pt_map_packet_app_eq :
  forall l p p' ms ms',
    pt_map_packet p = Some p' ->
    pt_map_packets (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l ++ ms ++ ms') = 
    map (fun m : name * msg => {| pSrc := pDst p'; pDst := fst m; pBody := snd m |}) (pt_map_name_msgs l) ++ pt_map_packets ms ++ pt_map_packets ms'.
Proof.
move => l; case => /= src dst m p ms ms'.
case H_m: (pt_map_msg m) => [m'|] // H_eq.
injection H_eq => H_eq_p.
rewrite -H_eq_p /=.
rewrite -pt_map_packets_app_distr.
exact: pt_map_packet_map_app_eq.
Qed.

Lemma pt_map_update_eq :
forall f h d,
  (fun n : name => pt_map_data (update f h d (tot_map_name_inv n))) =
  update (fun n : name => pt_map_data (f (tot_map_name_inv n))) (tot_map_name h) (pt_map_data d).
Proof.
move => f h d.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
  rewrite -H_dec in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
rewrite H_dec' in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Lemma pt_map_update_eq_some :
  forall net d p p',
    pt_map_packet p = Some p' ->
    (fun n : name => pt_map_data (update (nwState net) (pDst p) d (tot_map_name_inv n))) =
    update (fun n : name => pt_map_data (nwState net (tot_map_name_inv n))) (pDst p') (pt_map_data d).
Proof.
move => net d p p'.
case: p => src dst m.
case: p' => src' dst' m' /=.
case H_eq: (pt_map_msg _) => [m0|] // H_eq'.
inversion H_eq'; subst.
move {H_eq H_eq'}.
exact: pt_map_update_eq.
Qed.

Definition pt_trace_remove_empty_out :=
  fold_right (fun (e : @name _ multi_snd * (@input base_snd + list (@output base_snd))) l => 
                match e with
                | (n, inr []) => l
                | _ => e :: l
                end) [].

Theorem step_m_pt_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    @step_m _ multi_snd (pt_map_net net) (pt_map_net net') (pt_map_trace tr) \/ 
    (pt_map_net net' = pt_map_net net /\ pt_trace_remove_empty_out (pt_map_trace tr) = []).
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /pt_map_trace /=.  
  case H_m: (pt_map_packet p) => [p'|].
    have ->: tot_map_name (pDst p) = pDst p'.
      case: p H_eq H_hnd H_eq' H_m => /= src dst m H_eq H_hnd H_eq'.
      case (pt_map_msg m) => //= m' H_m.
      by inversion H_m.
    left.
    rewrite H_eq' /=.
    apply (@SM_deliver _ _ _ _ _ (pt_map_packets ms) (pt_map_packets ms') (pt_map_outputs out) (pt_map_data d) (pt_map_name_msgs l)).
    * rewrite /= H_eq pt_map_packets_app_distr /=.
      case H_p: (pt_map_packet _) => [p0|].
        rewrite H_p in H_m.
        by injection H_m => H_eq_p; rewrite H_eq_p.
      by rewrite H_p in H_m.
    * rewrite /=.
      case: p H_eq H_hnd H_eq' H_m => /= src dst m H_eq H_hnd H_eq'.
      case H_m: (pt_map_msg m) => [m'|] //.
      case: p' H_eq' => src' dst' m0 H_eq' H_eq_p.
      inversion H_eq_p; subst.
      rewrite /= {H_eq_p}.
      have H_q := pt_net_handlers_some dst src m (nwState net dst) H_m.
      rewrite /pt_mapped_net_handlers in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * rewrite /= /pt_map_net /=.
      rewrite (pt_map_packet_app_eq _ _ _ _ H_m).
      by rewrite (pt_map_update_eq_some _ _ _ H_m).
  right.
  split.
  * rewrite H_eq' {H_eq'}.
    rewrite /pt_map_net /=.
    case: p H_eq H_hnd H_m => /= src dst m H_eq H_hnd.
    case H_m: (pt_map_msg _) => [m'|] // H_eq'.
    rewrite 2!pt_map_packets_app_distr H_eq pt_map_packets_app_distr /=.
    case H_m': (pt_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
    have [H_d [H_l H_o]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
    rewrite (pt_map_name_msgs_empty_eq _ dst H_l) /=.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_s: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 /=.
      apply functional_extensionality => n.
      rewrite /update /=.
      case (name_eq_dec _ _) => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
  * move {H_eq'}.
    case: p H_eq H_hnd H_m => /= src dst m H_eq H_hnd.
    case H_m: (pt_map_msg _) => [m'|] // H_eq'.
    have [H_d [H_l H_o]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
    by rewrite H_o.
- move => h net net' out inp d l H_hnd H_eq.
  rewrite /pt_map_trace /=.  
  case H_i: (pt_map_input inp) => [inp'|].
    left.
    apply (@SM_input _ _ _ _ _ _ _ (pt_map_data d) (pt_map_name_msgs l)).
      rewrite /=.
      have H_q := pt_input_handlers_some h inp (nwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    rewrite /= H_eq /= /pt_map_net /=.  
    rewrite pt_map_packet_map_app_eq.
    by rewrite -pt_map_update_eq.
  right.
  split.
  * rewrite H_eq /pt_map_net /=.
    have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H_hnd.
    rewrite pt_map_packets_app_distr.
    rewrite (pt_map_name_msgs_empty_eq _ h H_l) /=.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_s: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 /=.
      apply functional_extensionality => n.
      rewrite /update /=.
      case (name_eq_dec _ _) => H_dec //.
      by rewrite H_dec H_d.
    by rewrite H_eq_s.
  * rewrite /=.
    have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H_hnd.
    by rewrite H_o.
Qed.

Lemma pt_map_trace_app_distr : 
  forall tr1 tr2,
  pt_map_trace (tr1 ++ tr2) = pt_map_trace tr1 ++ pt_map_trace tr2.
Proof.
elim => //.
case => n.
case.
  move => inp l IH tr2.
  rewrite /=.
  case (pt_map_input _) => [io'|] //. 
  by rewrite IH.
move => out l IH tr2.
rewrite /=.
by rewrite IH.
Qed.

Lemma pt_trace_remove_empty_out_app_distr :
  forall tr1 tr2,
    pt_trace_remove_empty_out (tr1 ++ tr2 ) = pt_trace_remove_empty_out tr1 ++ pt_trace_remove_empty_out tr2.
Proof.
elim => //.
case => n.
case.
  move => inp l IH tr2.
  by rewrite /= IH.
move => out l IH tr2.
rewrite /= IH.
by case: out.
Qed.

Corollary step_m_pt_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    exists tr', @step_m_star _ multi_snd step_m_init (pt_map_net net) tr' /\ 
     pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
move => net tr H_step.
remember step_m_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_m_init /= /pt_map_net /=.
  rewrite pt_init_handlers_fun_eq.
  exists [].
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_m_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ pt_map_trace tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite (app_nil_end (pt_map_trace _)).
    apply: (@RT1nTStep _ _ _ _ (pt_map_net x'')) => //.
    exact: RT1nTBase.
  * rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr H_eq_tr.
    by rewrite pt_trace_remove_empty_out_app_distr.
move: H => [H_eq H_eq'].
rewrite H_eq.
move: IHH_step1 => [tr' [H_star H_tr]].
exists tr'.
split => //.
rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr.
by rewrite H_eq' -app_nil_end.
Qed.

Definition pt_map_msgs :=
fold_right (fun m l =>
            match pt_map_msg m with
            | Some m' => m' :: l
            | None => l
            end) [].

Definition pt_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd :=
mkONetwork (fun src dst => pt_map_msgs (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)))
           (fun n => pt_map_data (onet.(onwState) (tot_map_name_inv n))).

Lemma pt_map_msg_update2 : 
  forall f ms to from,
    (fun src dst => pt_map_msgs (update2 f from to ms (tot_map_name_inv src) (tot_map_name_inv dst))) =
    update2 (fun src0 dst0 : name => pt_map_msgs (f (tot_map_name_inv src0) (tot_map_name_inv dst0)))
        (tot_map_name from) (tot_map_name to) (pt_map_msgs ms).
Proof.
move => f ms to from.
apply functional_extensionality => src.
apply functional_extensionality => dst.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec' //.
  move: H_dec => [H_eq H_eq'].
  case: H_dec' => H_dec'.
    rewrite H_eq in H_dec'.
    by rewrite tot_map_name_inverse_inv in H_dec'.
  rewrite H_eq' in H_dec'.
  by rewrite tot_map_name_inverse_inv in H_dec'.
move: H_dec' => [H_eq H_eq'].
case: H_dec => H_dec.
  rewrite -H_eq in H_dec.
  by rewrite tot_map_name_inv_inverse in H_dec.
rewrite -H_eq' in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
Qed.

Lemma pt_map_msgs_app_distr : 
  forall ms ms',
  pt_map_msgs (ms ++ ms') = pt_map_msgs ms ++ pt_map_msgs ms'.
Proof.
elim => //=.
move => m ms IH ms'.
rewrite /= IH.
by case (pt_map_msg _) => [m'|].
Qed.

Lemma collate_pt_map_eq :
  forall f h l,
    (fun src dst => pt_map_msgs (collate h f l (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate (tot_map_name h) (fun src dst => pt_map_msgs (f (tot_map_name_inv src) (tot_map_name_inv dst))) (pt_map_name_msgs l).
Proof.
move => f h l.
elim: l h f => //.
case => n m l IH h f.
rewrite /= IH /=.
case H_m: (pt_map_msg _) => [m'|] /=.
  rewrite 2!tot_map_name_inv_inverse /=.
  set f1 := fun _ _ => _.
  set f2 := update2 _ _ _ _.
  have H_eq_f: f1 = f2.
    rewrite /f1 /f2 {f1 f2}.
    have H_eq := pt_map_msg_update2 f (f h n ++ [m]) n h.
    move: H_eq.
    rewrite pt_map_msgs_app_distr /=.
    case H_m': (pt_map_msg _) => [m0|]; last by rewrite H_m' in H_m.
    rewrite H_m' in H_m.
    by inversion H_m.
  by rewrite H_eq_f.
rewrite pt_map_msg_update2 /=.
rewrite pt_map_msgs_app_distr /=.
case H_m': (pt_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
rewrite -app_nil_end.
set f1 := update2 _ _ _ _.
set f2 := fun _ _ => _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  apply functional_extensionality => src.
  apply functional_extensionality => dst.
  rewrite /update2 /=.
  case (sumbool_and _ _ _ _) => H_dec //.
  move: H_dec => [H_eq H_eq'].
  by rewrite -H_eq -H_eq' 2!tot_map_name_inv_inverse.
by rewrite H_eq_f.
Qed.

Lemma collate_pt_map_update2_eq :
  forall f from to ms l,
    (fun src dst => pt_map_msgs
            (collate to (update2 f from to ms) l
               (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate (tot_map_name to)
            (update2
               (fun src dst : name =>
                pt_map_msgs
                  (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name from)
               (tot_map_name to) (pt_map_msgs ms)) (pt_map_name_msgs l).
Proof.
move => f from to ms l.
rewrite -pt_map_msg_update2.
by rewrite collate_pt_map_eq.
Qed.

Theorem step_o_pt_mapped_simulation_1 :
  forall net net' tr,
    @step_o _ multi_fst net net' tr ->
    @step_o _ multi_snd (pt_map_onet net) (pt_map_onet net') (pt_map_trace tr) \/ 
    (pt_map_onet net' = pt_map_onet net /\ pt_trace_remove_empty_out (pt_map_trace tr) = []).
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' m ms out d l from to H_eq H_hnd H_eq'.
  case H_m: (pt_map_msg m) => [m'|].
    left.
    rewrite H_eq' /= /pt_map_onet /=.
    apply (@SO_deliver _ _ _ _ m' (pt_map_msgs ms) _ (pt_map_data d) (pt_map_name_msgs l) (tot_map_name from)).
    * rewrite /= 2!tot_map_name_inv_inverse H_eq /=.
      case H_m0: (pt_map_msg _) => [m0|]; last by rewrite H_m0 in H_m.
      rewrite H_m0 in H_m.
      by inversion H_m.
    * rewrite /= tot_map_name_inv_inverse.
      rewrite -(pt_net_handlers_some _ _ _ _ H_m).
      rewrite /pt_mapped_net_handlers /=.
      repeat break_let.
      by inversion H_hnd.
    * by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
  right.
  rewrite /=.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
  rewrite H_out.
  split => //.
  rewrite H_eq' /pt_map_onet /=.
  rewrite pt_map_update_eq /= H_eq_d.
  rewrite collate_pt_map_eq H_ms /=.
  set nwS1 := update _ _ _.
  set nwS2 := fun n => pt_map_data _.
  set nwP1 := fun _ _ => _. 
  set nwP2 := fun _ _ => _. 
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.  
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move: H_dec => [H_eq_from H_eq_to].
    rewrite -H_eq_from -H_eq_to H_eq /=.
    case H_m': (pt_map_msg _) => [m'|] //.
    by rewrite H_m' in H_m.
  by rewrite H_eq_s H_eq_p.
- move => h net net' out inp d l H_hnd H_eq.
  rewrite /pt_map_trace /=.
  case H_i: (pt_map_input inp) => [inp'|].
    left.
    apply (@SO_input _ _ _ _ _ _ _ (pt_map_data d) (pt_map_name_msgs l)).
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite H_eq /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
  right.  
  rewrite /=.  
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H_hnd.
  rewrite H_o.
  split => //.
  rewrite H_eq /= /pt_map_onet /=.
  rewrite pt_map_update_eq /= H_d.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := update _ _ _.
  set nwS2 := fun n => pt_map_data _.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.
  by rewrite H_eq_n.
Qed.

Corollary step_o_pt_mapped_simulation_star_1 :
  forall net tr,
    @step_o_star _ multi_fst step_o_init net tr ->
    exists tr', @step_o_star _ multi_snd step_o_init (pt_map_onet net) tr' /\
    pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
move => net tr H_step.
remember step_o_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_o_init /= /pt_map_net /=.
  rewrite pt_init_handlers_fun_eq.
  exists [].
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_o_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ pt_map_trace tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite (app_nil_end (pt_map_trace _)).
    apply: (@RT1nTStep _ _ _ _ (pt_map_onet x'')) => //.
    exact: RT1nTBase.
  * rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr H_eq_tr.
    by rewrite pt_trace_remove_empty_out_app_distr.
move: H => [H_eq H_eq'].
rewrite H_eq.
move: IHH_step1 => [tr' [H_star H_tr]].
exists tr'.
split => //.
rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr.
by rewrite H_eq' -app_nil_end.
Qed.

Lemma pt_not_in_failed_not_in :
  forall n failed,
    ~ In n failed ->
    ~ In (tot_map_name n) (map tot_map_name failed).
Proof.
move => n.
elim => //=.
move => n' failed IH H_in H_in'.
case: H_in' => H_in'.
  case: H_in.
  left.
  rewrite -(tot_map_name_inv_inverse n').
  rewrite H_in'.
  exact: tot_map_name_inv_inverse.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma pt_msg_in_map :
  forall m l n m',
  (forall nm, In nm l -> snd nm = m) ->
  In (tot_map_name n, m') (fold_right 
         (fun nm l' => 
         match pt_map_msg (snd nm) with
         | Some m => (tot_map_name (fst nm), m) :: l'
         | None => l'
         end) [] l) ->
pt_map_msg m = Some m'.
Proof.
move => m.
elim => //=.
case => /= n m' l IH n' m0 H_in.
case H_m: (pt_map_msg m') => [m1|].
  have H_in_f := H_in (n, m').
  rewrite /= in H_in_f.
  move => H_in_map.
  case: H_in_map => H_in_map.
    inversion H_in_map.    
    rewrite H_in_f in H_m; last by left.
    by rewrite -H1.
  move: H_in_map.
  apply: (IH _ m0) => //.
  move => nm H_in'.
  apply: H_in.
  by right.
apply: (IH _ m0) => //.
move => nm H_in'.
apply: H_in => //.
by right.
Qed.

Lemma pt_map_in_in :
  forall m m0 n l,
  (forall nm, In nm l -> snd nm = m) ->
  ~ In (n, m) l ->  
  ~ In (tot_map_name n, m0) (fold_right 
        (fun nm l' => 
         match pt_map_msg (snd nm) with
         | Some m0 => (tot_map_name (fst nm), m0) :: l'
         | None => l'
         end) [] l).
Proof.
move => m m0 n.
elim => //=.
case => /= n' m' l IH H_fail H_in.
case H_m: (pt_map_msg _) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    have H_nm := H_fail (n', m').
    rewrite /= in H_nm.
    case: H_in.
    left.
    apply tot_map_name_injective in H0.
    rewrite H0.
    rewrite H_nm //.
    by left.
  contradict H_in'.
  apply: IH.
    move => nm H_in_nm.
    apply: H_fail.
    by right.
  move => H_in_nm.
  case: H_in.
  by right.
apply: IH.
  move => nm H_in'.
  apply: H_fail => //.
  by right.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma nodup_pt_map :
  forall m nms,
  (forall nm, In nm nms -> snd nm = m) ->
  NoDup nms ->
  NoDup (fold_right 
         (fun nm l => 
         match pt_map_msg (snd nm) with
         | Some m => (tot_map_name (fst nm), m) :: l
         | None => l
         end) [] nms).
Proof.
move => m.
elim => /=.
  move => H_m H_nd.
  exact: NoDup_nil.
case => n m0 l IH H_m H_nd.
inversion H_nd.
rewrite /=.
have H_m0 := H_m (n, m0) (or_introl (eq_refl _)).
rewrite /= in H_m0.
rewrite H_m0.
rewrite H_m0 {m0 H_m0} in H_m H_nd H1 H.
case H_m': (pt_map_msg _) => [m'|].
  apply NoDup_cons.
    apply: (@pt_map_in_in m) => //.
    move => nm H_in.
    by apply: H_m; right.
  apply: IH => //.
  move => nm H_in.
  by apply: H_m; right.
apply: IH => //.
move => nm H_in.
by apply: H_m; right.
Qed.

Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.

Lemma pt_map_in_snd :
   forall m m' h ns nm,
   pt_map_msg m' = Some m ->
   In nm
      (fold_right
              (fun (nm : name * msg) (l : list (name * msg)) =>
               match pt_map_msg (snd nm) with
               | Some m0 => (tot_map_name (fst nm), m0) :: l
               | None => l
               end) [] (msg_for m' (adjacent_to_node h ns))) ->
   snd nm = m.
Proof.
move => m m' h.
elim => //=.
move => n ns IH.
case (adjacent_to_dec _ _) => H_dec /=.
  case => n' m0 H_eq.
  case H_eq': (pt_map_msg m') => [m1|]; last by rewrite H_eq' in H_eq.
  rewrite H_eq' in H_eq.
  inversion H_eq.
  rewrite H0 in H_eq'.
  move {H_eq H0 m1}.
  move => H_in.
  case: H_in => H_in; first by inversion H_in.
  exact: IH.
exact: IH.
Qed.

Lemma in_tot_map_name :
forall m m' l n,
pt_map_msg m = Some m' ->
(forall nm, In nm l -> snd nm = m) ->
In (n, m') (fold_right
              (fun (nm : name * msg) (l : list (name * msg)) =>
               match pt_map_msg (snd nm) with
               | Some m0 => (tot_map_name (fst nm), m0) :: l
               | None => l
               end) [] l) ->
In (tot_map_name_inv n, m) l.
Proof.
move => m m'.
elim => //=.
case => /= n m0 l IH n' H_eq H_in.
case H_m: (pt_map_msg _) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    rewrite tot_map_name_inv_inverse.
    have H_nm := H_in (n, m0).
    rewrite -H_nm /=; first by left.
    by left.
  right.
  apply: IH => //.
  move => nm H_inn.
  apply: H_in.
  by right.
move => H_in'.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma pt_in_msg_for_adjacent_to :
  forall m ns failed h n,
    In (tot_map_name_inv n, m) (msg_for m (adjacent_to_node h (exclude failed ns))) ->
    In (tot_map_name_inv n) (adjacent_to_node h (exclude failed ns)).
Proof.
move => m.
elim => //=.
move => n l IH failed h n'. 
case (in_dec _ _ _) => H_dec; first exact: IH.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec' /=.
  move => H_in.
  case: H_in => H_in.
    inversion H_in.
    by left.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma pt_in_adjacent_exclude_in_exlude :
  forall ns failed n h,
    In (tot_map_name_inv n) (adjacent_to_node h (exclude failed ns)) ->
    In (tot_map_name_inv n) (exclude failed ns) /\ adjacent_to h (tot_map_name_inv n).
Proof.
elim => //=.
move => n l IH failed n' h.
case (in_dec _ _ _) => /= H_dec.
  move => H_in.
  exact: IH.
case (adjacent_to_dec _ _) => /= H_dec'.
  move => H_in.
  case: H_in => H_in.
    rewrite {1}H_in -{4}H_in.
    split => //.
    by left.
  apply IH in H_in.
  move: H_in => [H_eq H_in].
  split => //.
  by right.
move => H_in.
apply IH in H_in.
move: H_in => [H_eq H_in].
split => //.
by right.
Qed.

Lemma pt_in_failed_exclude :
  forall ns failed n,
  In (tot_map_name_inv n) (exclude failed ns) ->
  ~ In (tot_map_name_inv n) failed /\ In (tot_map_name_inv n) ns.
Proof.
elim => //=.
move => n ns IH failed n'.
case (in_dec _ _ _) => H_dec /=.
  move => H_in.
  apply IH in H_in.
  move: H_in => [H_in H_in'].
  split => //.
  by right.
move => H_in.
case: H_in => H_in.
  rewrite -{1}H_in {2}H_in.
  split => //.
  by left.
apply IH in H_in.
move: H_in => [H_in H_in'].
split => //.
by right.
Qed.

Lemma pt_in_in_adj_msg_for :
  forall m ns failed n h,
    In n ns ->
    ~ In n (map tot_map_name failed) ->
    adjacent_to h n ->
    In (n, m)
     (msg_for m
        (adjacent_to_node h
           (exclude (map tot_map_name failed) ns))).
Proof.
move => m.
elim => //=.
move => n ns IH failed n' h H_in H_in' H_adj.
case (in_dec _ _ _) => H_dec.
  case: H_in => H_in; first by rewrite -H_in in H_in'.
  exact: IH.
case: H_in => H_in.
  rewrite H_in.
  rewrite /=.
  case (adjacent_to_dec _ _) => H_dec' //.
  rewrite /=.
  by left.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
  rewrite /=.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma pt_in_exclude_not_in_failed_map :
  forall ns n failed,
  In n (exclude (map tot_map_name failed) ns) ->
  ~ In n (map tot_map_name failed) /\ In n ns.
Proof.
elim => //=.
move => n ns IH n' failed.
case (in_dec _ _ _) => H_dec.
  move => H_in.
  apply IH in H_in.
  move: H_in => [H_nin H_in].
  split => //.
  by right.
rewrite /=.
move => H_in.
case: H_in => H_in.
  rewrite H_in.
  rewrite H_in in H_dec.
  split => //.
  by left.
apply IH in H_in.
move: H_in => [H_nin H_in].
split => //.
by right.
Qed.

Lemma pt_not_in_map_not_in_failed :
    forall failed n,
    ~ In n (map tot_map_name failed) ->
    ~ In (tot_map_name_inv n) failed.
Proof.
elim => //=.
move => n ns IH n' H_in H_in'.
case: H_in' => H_in'.
  case: H_in.
  left.
  by rewrite H_in' tot_map_name_inverse_inv.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma in_pt_map_msg_for :
  forall m m' l n,
    pt_map_msg m = Some m' ->
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name_inv n, m) l ->
    In (n, m') (fold_right
                 (fun (nm : name * msg) (l : list (name * msg)) =>
                  match pt_map_msg (snd nm) with
                  | Some m0 => (tot_map_name (fst nm), m0) :: l
                  | None => l
                  end) [] l).
Proof.
move => m m'.
elim => //=.
case => n m0 /= l IH n' H_eq H_in.
case H_m: (pt_map_msg m0) => [m1|].
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    rewrite H1 in H_m.
    rewrite H_m in H_eq.
    inversion H_eq.
    left.
    by rewrite tot_map_name_inverse_inv.
  right.
  apply: IH => //.
  move => nm H_inn.
  apply: H_in.
  by right.
move => H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  rewrite H1 in H_m.
  by rewrite H_m in H_eq.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma pt_adjacent_in_in :
  forall m ns n h,
    adjacent_to h (tot_map_name_inv n) ->
    In (tot_map_name_inv n) ns ->
    In (tot_map_name_inv n, m) (msg_for m (adjacent_to_node h ns)).
Proof.
move => m.
elim => //=.
move => n ns IH n' h H_adj H_in.
case (adjacent_to_dec _ _) => H_dec; case: H_in => H_in.
- rewrite /=.
  left.
  by rewrite H_in.
- rewrite /=.
  right.
  exact: IH.
- by rewrite H_in in H_dec.
- exact: IH.
Qed.

Lemma pt_not_in_failed_in_exclude :
  forall ns n failed,
  ~ In (tot_map_name_inv n) failed ->
  In (tot_map_name_inv n) ns ->
  In (tot_map_name_inv n) (exclude failed ns).
Proof.
elim => //=.
move => n ns IH n' failed H_in H_in'.
case (in_dec _ _ _) => H_dec; case: H_in' => H_in'.
- by rewrite H_in' in H_dec.
- exact: IH.
- rewrite /=.
  by left.
- right.
  exact: IH.
Qed.

Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Lemma pt_map_msg_for_eq :
  forall m m' h failed,
  pt_map_msg m = Some m' ->
  Permutation 
    (fold_right
              (fun (nm : name * msg) (l : list (name * msg)) =>
               match pt_map_msg (snd nm) with
               | Some m0 => (tot_map_name (fst nm), m0) :: l
               | None => l
               end) [] (msg_for m (adjacent_to_node h (exclude failed nodes))))
    (msg_for m' (adjacent_to_node (tot_map_name h) (exclude (map tot_map_name failed) nodes))).
Proof.
move => m m' h failed H_eq.
apply NoDup_Permutation; last split.
- apply (@nodup_pt_map m); first exact: in_for_msg.
  apply nodup_msg_for.
  apply nodup_exclude.
  exact: no_dup_nodes.
- apply nodup_msg_for.
  apply nodup_exclude.
  exact: no_dup_nodes.
- case: x => n m0 H_in.
  have H_eq' := pt_map_in_snd _ _ _ _ H_eq H_in.
  rewrite /= in H_eq'.
  rewrite H_eq' in H_in.
  rewrite H_eq' {H_eq' m0}.
  apply (@in_tot_map_name m) in H_in => //.
    apply pt_in_msg_for_adjacent_to in H_in.
    apply pt_in_adjacent_exclude_in_exlude in H_in.
    move: H_in => [H_in H_adj].
    apply pt_in_failed_exclude in H_in.
    move: H_in => [H_in H_in'].
    have H_nin: ~ In n (map tot_map_name failed).
      rewrite -(tot_map_name_inverse_inv n).
      exact: pt_not_in_failed_not_in.
    apply tot_adjacent_to_fst_snd in H_adj.
    rewrite tot_map_name_inverse_inv in H_adj.
    have H_inn: In n nodes by exact: all_names_nodes.
    exact: pt_in_in_adj_msg_for.
  exact: in_for_msg.
- case: x => n m0 H_in.
  have H_eq' := in_for_msg _ _ _ _ H_in.
  rewrite /= in H_eq'.
  rewrite H_eq'.
  rewrite H_eq' in H_in.
  apply in_msg_for_adjacent_in in H_in.
  move: H_in => [H_adj H_in].
  rewrite -(tot_map_name_inverse_inv n) in H_adj.
  apply tot_adjacent_to_fst_snd in H_adj.
  apply pt_in_exclude_not_in_failed_map in H_in.
  move: H_in => [H_in_f H_in].
  apply pt_not_in_map_not_in_failed in H_in_f.
  have H_in_n: In (tot_map_name_inv n) nodes by exact: all_names_nodes.
  apply: (@in_pt_map_msg_for m) => //; first by move => nm; apply in_for_msg.
  apply pt_adjacent_in_in => //.
  exact: pt_not_in_failed_in_exclude.
Qed.

Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd multi_map}.

Theorem step_o_f_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_o_f _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_o_f _ _ overlay_snd fail_msg_snd (map tot_map_name failed, pt_map_onet net) (map tot_map_name failed', pt_map_onet net') (pt_map_trace tr) \/ 
    (pt_map_onet net' = pt_map_onet net /\ failed = failed' /\
     pt_trace_remove_empty_out (pt_map_trace tr) = []).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- case H_m: (pt_map_msg m) => [m'|].
    left.
    rewrite /pt_map_onet /=.
    apply (@SOF_deliver _ _ _ _ _ _ _ m' (pt_map_msgs ms) _ (pt_map_data d) (pt_map_name_msgs l) (tot_map_name from)).
    * rewrite /= 2!tot_map_name_inv_inverse /= H3.
      rewrite /=.
      case H_m0: (pt_map_msg _) => [m0|]; last by rewrite H_m in H_m0.
      rewrite H_m in H_m0.
      by inversion H_m0.
    * exact: pt_not_in_failed_not_in.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ H_m)  /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by inversion H6.
    * by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
  right.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ H_m H6.
  rewrite H_out.
  split => //.
  rewrite /pt_map_onet /= pt_map_update_eq H_eq_d collate_pt_map_update2_eq H_ms /=.
  set nwP1 := update2 _ _ _ _.
  set nwS1 := update _ _ _.
  set nwP2 := fun _ _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.  
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    case (sumbool_and _ _ _ _) => H_dec //.
    move: H_dec => [H_eq_from H_eq_to].
    rewrite -H_eq_from -H_eq_to /= 2!tot_map_name_inv_inverse H3 /=.
    case H_m': (pt_map_msg _) => [m'|] //.
    by rewrite H_m' in H_m.
  by rewrite H_eq_s H_eq_p.
- case H_i: (pt_map_input _) => [inp'|].
    left.
    apply (@SOF_input _ _ _ _ _ _ _ _ _ _ (pt_map_data d) (pt_map_name_msgs l)).
    * exact: pt_not_in_failed_not_in.
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H5 in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
  right.
  rewrite /= /pt_map_onet /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H5.
  rewrite H_o.
  split => //.
  rewrite pt_map_update_eq /= H_d.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := update _ _ _.
  set nwS2 := fun n => pt_map_data _.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec tot_map_name_inv_inverse.
  by rewrite H_eq_n.
- left.
  rewrite /pt_map_onet /=.  
  set l := msg_for _ _.
  have H_nd: NoDup (map (fun nm => fst nm) (pt_map_name_msgs l)).
    rewrite /pt_map_name_msgs /=.
    rewrite /l {l}.
    apply nodup_snd_fst.
      apply (@nodup_pt_map msg_fail); first exact: in_for_msg.
      apply nodup_msg_for.
      apply nodup_exclude.
      exact: no_dup_nodes.
    move => nm nm' H_in H_in'.
    by rewrite (pt_map_in_snd  _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
  apply: SOF_fail => //.
  * exact: pt_not_in_failed_not_in.
  * rewrite /= /l collate_pt_map_eq /pt_map_name_msgs.
    by rewrite (nodup_perm_collate_eq _ _ H_nd (pt_map_msg_for_eq msg_fail h failed pt_fail_msg_fst_snd)).
Qed. 

Corollary step_o_f_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_o_f_star _ _ overlay_fst fail_msg_fst step_o_f_init (failed, net) tr ->
    exists tr', @step_o_f_star _ _ overlay_snd fail_msg_snd step_o_f_init (map tot_map_name failed, pt_map_onet net) tr' /\
    pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
move => net failed tr H_step.
remember step_o_f_init as y in *.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_n {H_eq_n}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_o_f_init /= /pt_map_onet /=.
  exists [].
  rewrite -pt_init_handlers_fun_eq.
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_o_f_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ pt_map_trace tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite (app_nil_end (pt_map_trace _)).
    apply: (@RT1nTStep _ _ _ _ (map tot_map_name failed'', pt_map_onet net'')) => //.
    exact: RT1nTBase.
  * rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr H_eq_tr.
    by rewrite pt_trace_remove_empty_out_app_distr.
move: H => [H_eq_n [H_eq_f H_eq]].
rewrite H_eq_n -H_eq_f.
move: IHH_step1 => [tr' [H_star H_tr]].
exists tr'.
split => //.
rewrite pt_map_trace_app_distr pt_trace_remove_empty_out_app_distr.
by rewrite H_eq -app_nil_end.
Qed.

End PartialMapSimulations.
