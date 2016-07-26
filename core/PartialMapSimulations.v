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

Class MultiParamsMsgPartialMap
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
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.

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
  (P : MultiParamsMsgPartialMap P0 P1) :=
  {
    pt_init_handlers_eq : forall n, 
      pt_map_data (init_handlers n) = init_handlers (tot_map_name n) ;
    pt_net_handlers_some : forall me src m st m',
      pt_map_msg m = Some m' ->
      pt_mapped_net_handlers me src m st = 
        net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) ;
    pt_net_handlers_none : forall me src m st out st' ps,
      pt_map_msg m = None ->
      net_handlers me src m st = (out, st', ps) ->
      pt_map_data st' = pt_map_data st /\ 
        pt_map_name_msgs ps = [] /\ pt_map_outputs out = [] ;
    pt_input_handlers_some : forall me inp st inp',
      pt_map_input inp = Some inp' ->
      pt_mapped_input_handlers me inp st = 
        input_handlers (tot_map_name me) inp' (pt_map_data st) ;
    pt_input_handlers_none : forall me inp st out st' ps,
      pt_map_input inp = None ->
      input_handlers me inp st = (out, st', ps) ->
      pt_map_data st' = pt_map_data st /\ 
        pt_map_name_msgs ps = [] /\ pt_map_outputs out = []
  }.

Class FailureParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailureParams P0) (F1 : FailureParams P1)
  (B : BaseParamsPartialMap B0 B1) :=
  {
    pt_reboot_eq : forall d, pt_map_data (reboot d) = reboot (pt_map_data d)
  }.

Class FailMsgParamsPartialMapCongruency 
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailMsgParams P0) (F1 : FailMsgParams P1)
  (P : MultiParamsMsgPartialMap P0 P1) :=
  {
    pt_fail_msg_fst_snd : pt_map_msg msg_fail = Some msg_fail
  }.

Class NewMsgParamsPartialMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (N0 : NewMsgParams P0) (N1 : NewMsgParams P1)
  (P : MultiParamsMsgPartialMap P0 P1) :=
  {
    pt_new_msg_fst_snd : pt_map_msg msg_new = Some msg_new
  }.

Section PartialMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.

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
  {| nwPackets := pt_map_packets net.(nwPackets) ;
     nwState := fun n => pt_map_data (net.(nwState) (tot_map_name_inv n)) |}.

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
by break_match.
Qed.

Lemma pt_map_name_msgs_empty_eq :
  forall l dst,
  pt_map_name_msgs l = [] ->
  pt_map_packets (map (fun m0 : name * msg => {| pSrc := dst; pDst := fst m0; pBody := snd m0 |}) l) = [].
Proof.
elim => //=.
case => n m l IH dst.
case H_m: pt_map_msg => [m'|] //=.
move => H_eq.
by rewrite IH.
Qed.

Lemma pt_map_packet_map_eq :
  forall l h,
    pt_map_packets (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (pt_map_name_msgs l).
Proof.
move => l h.
elim: l => //=.
case => n m l IH.
case pt_map_msg => [m'|] //.
by rewrite IH.
Qed.

Lemma pt_map_packet_map_eq_some :
  forall l p p',
    pt_map_packet p = Some p' ->
    pt_map_packets (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := pDst p'; pDst := fst m; pBody := snd m |}) (pt_map_name_msgs l).
Proof.
move => l; case => /= src dst m p.
case H_m: (pt_map_msg m) => [m'|] // H_eq.
injection H_eq => H_eq_p.
rewrite -H_eq_p /=.
exact: pt_map_packet_map_eq.
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
    * rewrite /= /pt_map_net /= 2!pt_map_packets_app_distr.
      by rewrite (pt_map_packet_map_eq_some _ _ H_m) (pt_map_update_eq_some _ _ _ H_m).
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
    rewrite -pt_map_packet_map_eq -pt_map_packets_app_distr.
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

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsPartialMapCongruency fail_fst fail_snd base_map}.

Theorem step_f_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_f _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_f _ _ fail_snd (map tot_map_name failed, pt_map_net net) (map tot_map_name failed', pt_map_net net') (pt_map_trace tr) \/ 
    (pt_map_net net' = pt_map_net net /\ failed = failed' /\ pt_trace_remove_empty_out (pt_map_trace tr) = []).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- rewrite /pt_map_trace /=.
  case H_m: (pt_map_packet p) => [p'|].
    destruct p, p'.
    simpl in *.
    move: H_m.
    case H_m: pt_map_msg => [m|] //.
    move => H_eq.
    find_inversion.
    left.
    rewrite /pt_map_net /= H3 pt_map_packets_app_distr /= H_m /= 2!pt_map_packets_app_distr {H3}.
    set p' := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    have ->: tot_map_name pDst = Net.pDst p' by [].    
    apply (@SF_deliver _ _ _ _ _ _ _ (pt_map_packets xs) (pt_map_packets ys) (pt_map_outputs out) (pt_map_data d) (pt_map_name_msgs l)) => //=.
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ H_m)  /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by find_inversion.
    * pose p := {| pSrc := pSrc ; pDst := pDst ; pBody := pBody |}.
      have H_p: pt_map_packet p = Some p'.
        rewrite /pt_map_packet.
        break_match.
        rewrite /p in Heqp0.
        find_inversion.
        by rewrite H_m.      
      by rewrite (pt_map_packet_map_eq_some _ _ H_p) (pt_map_update_eq_some _ _ _ H_p).
  right.
  rewrite /pt_map_net /=.
  destruct p.
  simpl in *.
  move: H_m.
  case H_m: pt_map_msg => [m|] //.
  move => H_eq.
  have H_m' := @pt_net_handlers_none _ _ _ _ _ name_map msg_map multi_map_congr _ _ _ _ _ _ _ H_m H6.
  break_and.
  rewrite H3 3!pt_map_packets_app_distr H1.    
  rewrite (pt_map_name_msgs_empty_eq _ pDst H0) /= H_m.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update /=.
    case (name_eq_dec _ _) => H_dec //.
    by rewrite H_dec.
  by rewrite H_eq_s.
- rewrite /= /pt_map_net /=.
  case H_i: pt_map_input => [inp'|].
    left.
    apply (@SF_input _ _ _ _ _ _ _ _ _ (pt_map_data d) (pt_map_name_msgs l)).
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_input_handlers_some _ _ _ H_i)  /pt_mapped_input_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by tuple_inversion.
    * rewrite /= -pt_map_packet_map_eq -pt_map_packets_app_distr.
      by rewrite pt_map_update_eq.
  right.
  rewrite /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none _ _ _ H_i H5.
  rewrite H_o.
  split => //.
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
- case H_m: (pt_map_packet p) => [p'|].
    left.
    destruct p, p'.
    simpl in *.
    move: H_m.
    case H_m: pt_map_msg => [m|] //.
    move => H_eq.
    find_inversion.
    rewrite /pt_map_net /=.
    find_rewrite.
    rewrite pt_map_packets_app_distr /= H_m pt_map_packets_app_distr.
    move: H4.
    set p := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    move => H_eq.
    set p' := {| pSrc := _ ; pDst := _ ; pBody := _ |}.
    exact: (@SF_drop _ _ _ _ _ _ p' (pt_map_packets xs) (pt_map_packets ys)).
  right.
  split => //.
  rewrite /pt_map_net /=.
  find_rewrite.
  by rewrite 2!pt_map_packets_app_distr /= H_m.
- rewrite /pt_map_net /=.
  find_rewrite.
  case H_p: pt_map_packet => [p'|]; last by right.
  left.
  rewrite pt_map_packets_app_distr /= H_p.
  exact: (@SF_dup _ _ _ _ _ _ p' (pt_map_packets xs) (pt_map_packets ys)).
- left.
  exact: SF_fail.
- rewrite remove_tot_map_eq /=.
  left.
  rewrite {2}/pt_map_net /=.
  apply: (SF_reboot (tot_map_name h)) => //; first exact: in_failed_in.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  suff H_suff: nwS1 = nwS2 by rewrite H_suff.
  rewrite /nwS1 /nwS2.
  apply functional_extensionality => n.
  break_if; break_if => //.
  * by rewrite /pt_map_net /= pt_reboot_eq.
  * by rewrite -e tot_map_name_inverse_inv in n0.
  * by rewrite e tot_map_name_inv_inverse in n0.
Qed.

Corollary step_f_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_f_star _ _ fail_fst step_f_init (failed, net) tr ->
    exists tr', @step_f_star _ _ fail_snd step_f_init (map tot_map_name failed, pt_map_net net) tr' /\ 
     pt_trace_remove_empty_out (pt_map_trace tr) = pt_trace_remove_empty_out tr'.
Proof.
move => net failed tr H_step.
remember step_f_init as y in *.
have H_eq_f: failed = fst (failed, net) by [].
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_f {H_eq_f}.
rewrite {2}H_eq_n {H_eq_n}.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_f_init /= /pt_map_net /=.
  rewrite -pt_init_handlers_fun_eq.
  exists [].
  split => //.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_f_pt_mapped_simulation_1 in H.
case: H => H.
  move: IHH_step1 => [tr' [H_star H_eq_tr]].
  exists (tr' ++ pt_map_trace tr2).
  split.
  * have H_trans := refl_trans_1n_trace_trans H_star.
    apply: H_trans.
    rewrite (app_nil_end (pt_map_trace _)).
    apply: (@RT1nTStep _ _ _ _ (map tot_map_name failed'', pt_map_net net'')) => //.
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

Definition pt_map_msgs :=
fold_right (fun m l =>
            match pt_map_msg m with
            | Some m' => m' :: l
            | None => l
            end) [].

Definition pt_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd :=
  {| onwPackets := fun src dst => pt_map_msgs (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     onwState := fun n => pt_map_data (onet.(onwState) (tot_map_name_inv n)) |}.

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

Definition pt_map_trace_ev (e : @name _ multi_fst * (@input base_fst + (@output base_fst))) :
 option (@name _ multi_snd * (@input base_snd + (@output base_snd))) :=
match e with
| (n, inl i) => 
  match pt_map_input i with
  | Some i' => Some (tot_map_name n, inl i')
  | None => None
  end
| (n, inr o) => 
  match pt_map_output o with
  | Some o' => Some (tot_map_name n, inr o')
  | None => None
  end
end.

Definition pt_map_traces :=
fold_right (fun e l =>
              match pt_map_trace_ev e with
              | Some e' => e' :: l
              | None => l
              end) [].

Lemma pt_map_traces_app : forall tr tr',
  pt_map_traces (tr ++ tr') = pt_map_traces tr ++ pt_map_traces tr'.
Proof.
elim => //=.
move => occ tr IH tr'.
by case pt_map_trace_ev => [p|]; rewrite IH.
Qed.

Lemma pt_map_traces_outputs_eq :
  forall out to,
  pt_map_traces (map (fun o : output => (to, inr o)) out) =
  map (fun o : output => (tot_map_name to, inr o)) (pt_map_outputs out).
Proof.
elim => //=.
move => o out IH to.
by case pt_map_output => [o'|]; rewrite IH.
Qed.

Theorem step_o_pt_mapped_simulation_1 :
  forall net net' tr,
    @step_o _ multi_fst net net' tr ->
    @step_o _ multi_snd (pt_map_onet net) (pt_map_onet net') (pt_map_traces tr) \/ 
    pt_map_onet net' = pt_map_onet net /\ pt_map_traces tr = [].
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' tr m ms out d l from to H_eq H_hnd H_eq' H_eq_tr.
  case H_m: (pt_map_msg m) => [m'|].
    left.
    rewrite H_eq' /= /pt_map_onet /=.
    apply (@SO_deliver _ _ _ _ _ m' (pt_map_msgs ms) (pt_map_outputs out) (pt_map_data d) (pt_map_name_msgs l) (tot_map_name from) (tot_map_name to)).
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
    * by rewrite H_eq_tr /= pt_map_traces_outputs_eq.
  right.
  rewrite /=.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ H_m H_hnd.
  rewrite H_eq_tr pt_map_traces_outputs_eq H_out /=.
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
- move => h net net' tr out inp d l H_hnd H_eq H_eq_tr.
  case H_i: (pt_map_input inp) => [inp'|].
    left.
    apply (@SO_input _ _ (tot_map_name h) _ _ _ (pt_map_outputs out) inp' (pt_map_data d) (pt_map_name_msgs l)).
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      rewrite H_hnd in H_q.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite H_eq /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
    * by rewrite H_eq_tr /= H_i pt_map_traces_outputs_eq.
  right.  
  rewrite /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H_hnd.
  rewrite H_eq_tr /= pt_map_traces_outputs_eq H_i H_o /=.
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
    @step_o_star _ multi_snd step_o_init (pt_map_onet net) (pt_map_traces tr).
Proof.
move => net tr H_step.
remember step_o_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_o_init /= /pt_map_net /=.
  rewrite pt_init_handlers_fun_eq.
  exact: RT1nTBase.
rewrite pt_map_traces_app.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_o_pt_mapped_simulation_1 in H.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite (app_nil_end (pt_map_traces _)).
  apply: (@RT1nTStep _ _ _ _ (pt_map_onet x'')) => //.
  exact: RT1nTBase.
move: H => [H_eq H_eq'].
by rewrite H_eq H_eq' -app_nil_end.
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
               end) [] (map_pair m' (filter_rel h ns))) ->
   snd nm = m.
Proof.
move => m m' h.
elim => //=.
move => n ns IH.
case (rel_dec _ _) => H_dec /=.
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

Lemma pt_in_tot_map_name :
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

Lemma in_pt_map_map_pair :
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

Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Lemma pt_nodup_perm_map_map_pair_perm :
  forall m m' h failed ns ns',
  NoDup ns ->
  Permutation (map tot_map_name ns) ns' ->
  pt_map_msg m = Some m' ->
  Permutation 
    (fold_right
              (fun (nm : name * msg) (l : list (name * msg)) =>
               match pt_map_msg (snd nm) with
               | Some m0 => (tot_map_name (fst nm), m0) :: l
               | None => l
               end) [] (map_pair m (filter_rel h (exclude failed ns))))
    (map_pair m' (filter_rel (tot_map_name h) (exclude (map tot_map_name failed) ns'))).
Proof.
move => m m' h failed ns ns' H_nd H_pm H_eq.
apply NoDup_Permutation; last split.
- apply (@nodup_pt_map m); first exact: in_for_msg.
  apply nodup_map_pair.
  exact: nodup_exclude.
- apply nodup_map_pair.
  apply nodup_exclude.
  move: H_pm.
  apply: NoDup_Permutation_NoDup.
  exact: nodup_to_map_name.
- case: x => n m0 H_in.
  have H_eq' := pt_map_in_snd _ _ _ _ H_eq H_in.
  rewrite /= in H_eq'.
  rewrite H_eq' in H_in.
  rewrite H_eq' {H_eq' m0}.
  apply (@pt_in_tot_map_name m) in H_in => //.
    apply in_map_pair_adjacent_to in H_in.
    apply in_adjacent_exclude_in_exlude in H_in.
    move: H_in => [H_in H_adj].
    apply in_failed_exclude in H_in.
    move: H_in => [H_in H_in'].
    have H_nin: ~ In n (map tot_map_name failed).
      rewrite -(tot_map_name_inverse_inv n).
      exact: not_in_failed_not_in.
    apply tot_adjacent_to_fst_snd in H_adj.
    rewrite tot_map_name_inverse_inv in H_adj.
    have H_inn: In n ns'.
      apply (Permutation_in n) in H_pm => //.
      rewrite -(tot_map_name_inverse_inv n).
      exact: in_failed_in.
    exact: in_in_adj_map_pair.
  exact: in_for_msg.
- case: x => n m0 H_in.
  have H_eq' := in_for_msg _ _ _ _ H_in.
  rewrite /= in H_eq'.
  rewrite H_eq'.
  rewrite H_eq' in H_in.
  apply in_map_pair_related_in in H_in.
  move: H_in => [H_adj H_in].
  rewrite -(tot_map_name_inverse_inv n) in H_adj.
  apply tot_adjacent_to_fst_snd in H_adj.
  apply in_exclude_not_in_failed_map in H_in.
  move: H_in => [H_in_f H_in].
  apply not_in_map_not_in_failed in H_in_f.
  have H_in_n: In (tot_map_name_inv n) ns.
    apply Permutation_sym in H_pm.
    apply (Permutation_in n) in H_pm => //.
    apply: tot_map_name_in.
    by rewrite tot_map_name_inverse_inv.
  apply: (@in_pt_map_map_pair m) => //; first by move => nm; apply in_for_msg.
  apply adjacent_in_in_msg => //.
  exact: not_in_failed_in_exclude.
Qed.

Lemma pt_map_map_pair_eq :
  forall m m' h failed,
  pt_map_msg m = Some m' ->
  Permutation 
    (fold_right
              (fun (nm : name * msg) (l : list (name * msg)) =>
               match pt_map_msg (snd nm) with
               | Some m0 => (tot_map_name (fst nm), m0) :: l
               | None => l
               end) [] (map_pair m (filter_rel h (exclude failed nodes))))
    (map_pair m' (filter_rel (tot_map_name h) (exclude (map tot_map_name failed) nodes))).
Proof.
move => m m' h failed H_eq.
apply pt_nodup_perm_map_map_pair_perm => //; first exact: no_dup_nodes.
apply Permutation_sym.
exact: permutation_nodes.
Qed.

Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.

Theorem step_o_f_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_o_f _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_o_f _ _ overlay_snd fail_msg_snd (map tot_map_name failed, pt_map_onet net) (map tot_map_name failed', pt_map_onet net') (pt_map_traces tr) \/ 
    pt_map_onet net' = pt_map_onet net /\ failed = failed' /\ pt_map_traces tr = [].
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- case H_m: (pt_map_msg m) => [m'|].
    left.
    rewrite /pt_map_onet /=.
    apply (@SOF_deliver _ _ _ _ _ _ _ _ m' (pt_map_msgs ms) (pt_map_outputs out) (pt_map_data d) (pt_map_name_msgs l) (tot_map_name from) (tot_map_name to)).
    * rewrite /= 2!tot_map_name_inv_inverse /=.
      find_rewrite.
      rewrite /=.
      case H_m0: (pt_map_msg _) => [m0|]; last by rewrite H_m in H_m0.
      rewrite H_m in H_m0.
      by inversion H_m0.
    * exact: not_in_failed_not_in.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ H_m)  /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
      repeat break_let.
      by find_inversion.
    * by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
    * by rewrite pt_map_traces_outputs_eq.
  right.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ H_m H5.
  rewrite pt_map_traces_outputs_eq /= H_out /=.
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
    apply (@SOF_input _ _ _ _ (tot_map_name h) _ _ _ _ (pt_map_outputs out) inp' (pt_map_data d) (pt_map_name_msgs l)).
    * exact: not_in_failed_not_in.
    * rewrite /=.
      have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      find_rewrite.
      rewrite H_q.
      by rewrite tot_map_name_inv_inverse.
    * by rewrite /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
    * by rewrite pt_map_traces_outputs_eq.
  right.
  rewrite /= /pt_map_onet /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H4.
  rewrite pt_map_traces_outputs_eq H_o /=.
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
  set l := map_pair _ _.
  have H_nd: NoDup (map (fun nm => fst nm) (pt_map_name_msgs l)).
    rewrite /pt_map_name_msgs /=.
    rewrite /l {l}.
    apply nodup_snd_fst.
      apply (@nodup_pt_map msg_fail); first exact: in_for_msg.
      apply nodup_map_pair.
      apply nodup_exclude.
      exact: no_dup_nodes.
    move => nm nm' H_in H_in'.
    by rewrite (pt_map_in_snd  _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
  apply: SOF_fail => //.
  * exact: not_in_failed_not_in.
  * rewrite /= /l collate_pt_map_eq /pt_map_name_msgs.
    by rewrite (nodup_perm_collate_eq _ _ H_nd (pt_map_map_pair_eq msg_fail h failed pt_fail_msg_fst_snd)).
Qed.

Corollary step_o_f_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_o_f_star _ _ overlay_fst fail_msg_fst step_o_f_init (failed, net) tr ->
    @step_o_f_star _ _ overlay_snd fail_msg_snd step_o_f_init (map tot_map_name failed, pt_map_onet net) (pt_map_traces tr).
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
  rewrite -pt_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_o_f_pt_mapped_simulation_1 in H.
rewrite pt_map_traces_app.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite (app_nil_end (pt_map_traces _)).
  apply: (@RT1nTStep _ _ _ _ (map tot_map_name failed'', pt_map_onet net'')) => //.
  exact: RT1nTBase.
move: H => [H_eq_n [H_eq_f H_eq]].
by rewrite H_eq_n -H_eq_f H_eq -app_nil_end.
Qed.

Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.

Definition pt_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd :=
  {| odnwNodes := map tot_map_name net.(odnwNodes) ;
     odnwPackets := fun src dst => pt_map_msgs (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     odnwState := fun n => match net.(odnwState) (tot_map_name_inv n) with
                         | None => None
                         | Some d => Some (pt_map_data d)
                         end |}.

Lemma collate_ls_pt_map_eq :
  forall ns f h m m',
    pt_map_msg m = Some m' ->
    (fun src dst => pt_map_msgs (collate_ls ns f h m (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate_ls (map tot_map_name ns) (fun src dst => pt_map_msgs (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name h) m'.
Proof.
elim => //=.
move => n ns IH f h m m' H_eq.
rewrite /= (IH _ _ _  m') //=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  have H_eq' := pt_map_msg_update2 f (f n h ++ [m]) h n.
  rewrite pt_map_msgs_app_distr in H_eq'.
  by rewrite H_eq' /= H_eq.
by rewrite H_eq_f.
Qed.

Theorem step_o_d_f_pt_mapped_simulation_1 :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_o_d_f _ _ overlay_fst new_msg_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_o_d_f _ _ overlay_snd new_msg_snd fail_msg_snd (map tot_map_name failed, pt_map_odnet net) (map tot_map_name failed', pt_map_odnet net') (pt_map_traces tr) \/ 
    pt_map_odnet net' = pt_map_odnet net /\ failed = failed' /\ pt_map_traces tr = [].
Proof.
move => net net' failed failed' tr H_nd H_step.
invcs H_step.
- left.
  rewrite /pt_map_odnet.
  apply (@SODF_start _ _ _ _ _ _ _ _ (tot_map_name h)) => /=; first exact: not_in_failed_not_in.
  set p1 := fun _ _ => _.
  set p2 := collate_ls _ _ _ _.
  set s1 := fun _ => _.
  set s2 := update_opt _ _ _.
  have H_eq_s: s1 = s2.
    rewrite /s1 /s2 /update_opt {s1 s2}.
    apply functional_extensionality => n.
    rewrite -pt_init_handlers_eq.
    break_match_goal.
      break_if; break_if; try by congruence.
      - by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
      - by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
      - by find_rewrite.
    break_if; break_if; (try by congruence); last by find_rewrite.
    by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
  rewrite H_eq_s /s2 {s1 s2 H_eq_s}.
  have H_eq_p: p1 = p2.
    rewrite /p1 /p2 {p1 p2}.    
    rewrite (collate_ls_pt_map_eq _ _ _ _ pt_new_msg_fst_snd) /=.
    rewrite collate_pt_map_eq.
    set f1 := fun _ _ => _.    
    set c1 := collate _ _ _.
    set c2 := collate _ _ _.
    set f'1 := map tot_map_name _.
    set f'2 := filter_rel (tot_map_name h) _.
    have H_c: c1 = c2.
      rewrite /c1 /c2 {c1 c2}.
      apply: nodup_perm_collate_eq; last first.
        rewrite /pt_map_name_msgs.
        apply: pt_nodup_perm_map_map_pair_perm => //.
        by rewrite pt_new_msg_fst_snd.
      rewrite /pt_map_name_msgs /=.
      apply: nodup_snd_fst => //.
        apply (@nodup_pt_map msg_new); first exact: in_for_msg.
        apply: nodup_map_pair.
        exact: nodup_exclude.
      move => nm nm' H_in H_in'.
      apply (@pt_map_in_snd msg_new _ _ _ _ pt_new_msg_fst_snd) in H_in.
      apply (@pt_map_in_snd msg_new _ _ _ _ pt_new_msg_fst_snd) in H_in'.
      by rewrite H_in H_in'.
    rewrite H_c {H_c}.
    suff H_suff: f'1 = f'2 by rewrite H_suff.
    rewrite /f'1 /f'2.
    elim (odnwNodes net) => //=.
    move => n ns IH.
    repeat break_if => //=.
    * by rewrite IH.
    * by find_apply_lem_hyp tot_adjacent_to_fst_snd.
    * by find_apply_lem_hyp not_in_failed_not_in.
    * by find_apply_lem_hyp tot_adjacent_to_fst_snd.
    * case: n0.
      exact: in_failed_in.  
  by rewrite H_eq_p.
- case H_m: (pt_map_msg m) => [m'|].
    left.
    rewrite /pt_map_odnet /=.
    apply (@SODF_deliver _ _ _ _ _ _ _ _ _ m' (pt_map_msgs ms) (pt_map_outputs out) (pt_map_data d) (pt_map_data d') (pt_map_name_msgs l) (tot_map_name from) (tot_map_name to)).
    * exact: not_in_failed_not_in.
    * exact: in_failed_in. 
    * by rewrite /= tot_map_name_inv_inverse /= H5.
    * rewrite /= 2!tot_map_name_inv_inverse /=.
      find_rewrite.
      by rewrite /= H_m.
    * rewrite /= -(pt_net_handlers_some _ _ _ _ H_m) /pt_mapped_net_handlers /=.
      repeat break_let.
      by tuple_inversion.
    * set u1 := fun _ => match _ with | _ => _ end.
      set u2 := update_opt _ _ _.
      rewrite collate_pt_map_update2_eq.
      suff H_suff: u1 = u2 by rewrite H_suff.
      rewrite /u1 /u2 /update_opt /=.
      apply functional_extensionality => n.
      repeat break_if; try by congruence.
        rewrite -(tot_map_name_inverse_inv n) in n0.
        by rewrite e in n0.
      find_rewrite.
      by find_rewrite_lem tot_map_name_inv_inverse.
    * by rewrite pt_map_traces_outputs_eq.
- right.
  have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ H_m H7.
  rewrite pt_map_traces_outputs_eq H_out /=.
  split => //.
  rewrite /pt_map_odnet /= collate_pt_map_update2_eq H_ms /=.
  set nwP1 := update2 _ _ _ _.
  set nwP2 := fun _ _ => _.
  set nwS1 := fun _ => _.
  set nwS2 := fun _ => _.
  have H_eq_s: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 {nwS1 nwS2}.
    apply functional_extensionality => n.
    rewrite /update_opt /=.
    case eq_dec => H_dec //.
    by rewrite H_dec H5 H_eq_d.
  have H_eq_p: nwP1 = nwP2.
    rewrite /nwP1 /nwP2 /=.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    rewrite /update2 /=.
    break_if => //.
    break_and.
    by rewrite -H -H0 2!tot_map_name_inv_inverse H6 /= H_m.
  by rewrite H_eq_s H_eq_p.
- case H_i: (pt_map_input _) => [inp'|].
    left.
    apply (@SODF_input _ _ _ _ _ (tot_map_name h) _ _ _ _ (pt_map_outputs out) inp' (pt_map_data d) (pt_map_data d') (pt_map_name_msgs l)).
    * exact: not_in_failed_not_in.
    * exact: in_failed_in. 
    * by rewrite /pt_map_odnet /= tot_map_name_inv_inverse H5.
    * have H_q := pt_input_handlers_some h inp d H_i.
      rewrite /pt_mapped_input_handlers /= in H_q.
      find_rewrite.
      by rewrite H_q.
    * rewrite /= /pt_map_odnet /= collate_pt_map_eq.
      set u1 := fun _ => match _ with | _ => _ end.
      set u2 := update_opt _ _ _.
      suff H_suff: u1 = u2 by rewrite H_suff.
      rewrite /u1 /u2 /update_opt /=.
      apply functional_extensionality => n.
      repeat break_if; try by congruence.
        rewrite -(tot_map_name_inverse_inv n) in n0.
        by rewrite e in n0.
      find_rewrite.
      by find_rewrite_lem tot_map_name_inv_inverse.
    * by rewrite pt_map_traces_outputs_eq.
  right.
  rewrite /= /pt_map_odnet /=.
  have [H_d [H_l H_o]] := pt_input_handlers_none h inp d H_i H6.
  rewrite pt_map_traces_outputs_eq H_o /=.
  split => //=.
  rewrite collate_pt_map_eq H_l /=.
  set nwS1 := fun n : name => match _ with | _ => _ end.
  set nwS2 := fun n : name => match _ with | _ => _ end.
  have H_eq_n: nwS1 = nwS2.
    rewrite /nwS1 /nwS2 /=.
    apply functional_extensionality => n.
    rewrite /update_opt /=.
    case eq_dec => H_dec //.
    by rewrite H_dec H5 H_d.
  by rewrite H_eq_n.
- left.
  rewrite /pt_map_odnet /=.
  set l := map_pair _ _.
  have H_nd': NoDup (map (fun nm => fst nm) (pt_map_name_msgs l)).
    rewrite /pt_map_name_msgs /=.
    rewrite /l {l}.
    apply nodup_snd_fst.
      apply (@nodup_pt_map msg_fail); first exact: in_for_msg.
      apply nodup_map_pair.
      exact: nodup_exclude.
    move => nm nm' H_in H_in'.
    by rewrite (pt_map_in_snd  _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
  apply: SODF_fail => //.
  * exact: not_in_failed_not_in.
  * exact: in_failed_in.
  * rewrite /=.
    rewrite /l collate_pt_map_eq.
    have H_pm := pt_nodup_perm_map_map_pair_perm _ h failed H_nd (Permutation_refl (map tot_map_name (odnwNodes net))) pt_fail_msg_fst_snd.
    have H_pm' := H_pm _ _ fail_msg_map_congr.
    have H_eq := nodup_perm_collate_eq  _ _ H_nd' H_pm'.
    by rewrite H_eq.
Qed.

Corollary step_o_d_f_pt_mapped_simulation_star_1 :
  forall net failed tr,
    @step_o_d_f_star _ _ overlay_fst new_msg_fst fail_msg_fst step_o_d_f_init (failed, net) tr ->
    @step_o_d_f_star _ _ overlay_snd new_msg_snd fail_msg_snd step_o_d_f_init (map tot_map_name failed, pt_map_odnet net) (pt_map_traces tr).
Proof.
move => net failed tr H_step.
remember step_o_d_f_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_o_d_f_init /= /step_o_init.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
destruct x'.
destruct x''.
rewrite /=.
find_apply_lem_hyp step_o_d_f_pt_mapped_simulation_1; last by move: H_step1; apply: ordered_dynamic_nodes_no_dup.
simpl in *.
rewrite pt_map_traces_app.
case: H => H.
  have H_trans := refl_trans_1n_trace_trans IHH_step1.
  apply: H_trans.
  rewrite (app_nil_end (pt_map_traces _)).
  apply: (@RT1nTStep _ _ _ _ (map tot_map_name l0, pt_map_odnet o0)) => //.
  exact: RT1nTBase.
move: H => [H_eq_n [H_eq_f H_eq]].
by rewrite H_eq_n -H_eq_f H_eq -app_nil_end.
Qed.

Lemma in_msg_pt_map_msgs :
  forall l m' m0,
    pt_map_msg m0 = Some m' ->
    In m0 l ->
    In m' (pt_map_msgs l).
Proof.
elim => //.
move => m0 l IH.
move => m1 m2 H_eq H_in.
case: H_in => H_in.
  rewrite H_in /= H_eq.
  by left.
have IH' := IH _ _ H_eq H_in.
rewrite /=.
by break_match; first by right.
Qed.

Hypothesis pt_map_msg_injective : 
  forall m0 m1 m, pt_map_msg m0 = Some m -> pt_map_msg m1 = Some m -> m0 = m1.

Lemma in_pt_map_msgs_in_msg :
  forall l m0 m1,
    pt_map_msg m0 = Some m1 ->
    In m1 (pt_map_msgs l) ->
    In m0 l.
Proof.
elim => //=.
move => m0 l IH.
move => m1 m2 H_eq H_in.
have IH' := IH _ _ H_eq.
break_match; last first.
  right.
  exact: IH'.
have IH'' := IH _ _ Heqo.
case: H_in => H_in; last first.
  right.
  exact: IH'.
rewrite H_in in IH'' Heqo.
left.
move: Heqo H_eq.
exact: pt_map_msg_injective.
Qed.

Lemma in_all_before_pt_map_msg :
  forall l m0 m1 m'0 m'1,
    pt_map_msg m0 = Some m'0 ->
    pt_map_msg m1 = Some m'1 ->
    before_all m'0 m'1 (pt_map_msgs l) ->
    before_all m0 m1 l.
Proof.
elim => //=.
move => m l IH m0 m1 m'0 m'1 H_eq H_eq' H_bef.
break_match; simpl in *.
  case: H_bef => H_bef.
    left.
    move => H_in.
    case: H_bef.
    move: H_eq H_in.
    exact: in_msg_pt_map_msgs.
  break_and.
  right.
  split; last first.
    move: H0.
    exact: IH.
  move => H_eq_m.
  rewrite H_eq_m in H_eq'.
  rewrite Heqo in H_eq'.
  by find_injection.
right.
split; last first.
  move: H_bef.
  exact: IH.
by congruence.
Qed.

Lemma count_occ_pt_map_msgs_eq :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  count_occ msg_eq_dec (pt_map_msgs l) m' = count_occ msg_eq_dec l m0.
Proof.
elim => //=.
move => m l IH m' m0 H_eq.
break_if.
  repeat find_rewrite.
  rewrite /=.
  break_if => //.
  have IH' := IH _ _ H_eq.
  by rewrite IH'.
have IH' := IH _ _ H_eq.
rewrite -IH'.
break_match => //.
rewrite /=.
break_if => //.
case: n.
find_rewrite.
move: Heqo H_eq.
exact: pt_map_msg_injective.
Qed.

Lemma hd_error_pt_map_msgs :
  forall l m' m0,
  pt_map_msg m0 = Some m' ->
  hd_error l = Some m0 ->
  hd_error (pt_map_msgs l) = Some m'.
Proof.
case => //=.
move => m l m' m0 H_eq H_eq'.
find_injection.
by break_match.
Qed.

End PartialMapSimulations.
