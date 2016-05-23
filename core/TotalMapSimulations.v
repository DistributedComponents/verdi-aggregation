Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import Net.
Require Import StructTact.Util.

Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Require Import Sumbool.
Require Import FunctionalExtensionality.
Require Import Sorting.Permutation.
Require Import OrderedLemmas.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.

Class BaseParamsTotalMap (P0 : BaseParams) (P1 : BaseParams) := 
  {
    tot_map_data : @data P0 -> @data P1 ;
    tot_map_input : @input P0 -> @input P1 ;
    tot_map_output : @output P0 -> @output P1
  }.

Class MultiParamsNameTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1)  :=
  {
    tot_map_name : @name B0 P0 -> @name B1 P1 ;
    tot_map_name_inv : @name B1 P1 -> @name B0 P0
  }.

Class MultiParamsNameTotalMapBijective `(M : MultiParamsNameTotalMap) :=
  {
    tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n ;
    tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n ;
  }.

Class MultiParamsMsgTotalMap
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : MultiParams B1) :=
  {
    tot_map_msg : @msg B0 P0 -> @msg B1 P1
  }.

Section TotalMapDefs.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.

Definition tot_map_name_msgs :=
  map (fun nm => (tot_map_name (fst nm), tot_map_msg (snd nm))).

Definition tot_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

Definition tot_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).

End TotalMapDefs.

Class MultiParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (B : BaseParamsTotalMap B0 B1) 
  (N : MultiParamsNameTotalMap P0 P1)
  (P : MultiParamsMsgTotalMap P0 P1) :=
  {
    tot_init_handlers_eq : forall n, 
      tot_map_data (init_handlers n) = init_handlers (tot_map_name n) ;
    tot_net_handlers_eq : forall me src m st, 
      tot_mapped_net_handlers me src m st = 
      net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) ;
    tot_input_handlers_eq : forall me inp st, 
      tot_mapped_input_handlers me inp st = 
      input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st) ;
    tot_map_output_injective : forall o o', 
      tot_map_output o = tot_map_output o' -> o = o'
  }.

Class FailureParamsTotalMapCongruency 
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailureParams P0) (F1 : FailureParams P1)
  (B : BaseParamsTotalMap B0 B1) :=
  {
    tot_reboot_eq : forall d, tot_map_data (reboot d) = reboot (tot_map_data d)
  }.

Class NameOverlayParamsTotalMapCongruency
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (O0 : NameOverlayParams P0) (O1 : NameOverlayParams P1)
  (N : MultiParamsNameTotalMap P0 P1) :=
  {
    tot_adjacent_to_fst_snd : forall n n', 
      adjacent_to n n' <-> adjacent_to (tot_map_name n) (tot_map_name n')
  }.

Class FailMsgParamsTotalMapCongruency 
  (B0 : BaseParams) (B1 : BaseParams)
  (P0 : MultiParams B0) (P1 : MultiParams B1)
  (F0 : FailMsgParams P0) (F1 : FailMsgParams P1)
  (P : MultiParamsMsgTotalMap P0 P1) :=
  {
    tot_fail_msg_fst_snd : msg_fail = tot_map_msg msg_fail
  }.

Class MultiOneNodeParamsTotalMap
  (B0 : BaseParams) (P0 : MultiParams B0) (B1 : BaseParams) :=
  {
    tot_one_map_data : @data B0 -> @data B1 ;
    tot_one_map_input : name -> @input B0 -> @input B1 ;
    tot_one_map_msg : name -> name -> msg -> @input B1
  }.

Class MultiOneNodeParamsTotalMapCongruency
 (B0 : BaseParams) (B1 : BaseParams)
 (P0 : MultiParams B0) (P1 : OneNodeParams B1)
 (P : MultiOneNodeParamsTotalMap P0 B1) :=
 {
   tot_init_eq : forall n, tot_one_map_data (init_handlers n) = init ;
   tot_net_handlers_handler_eq : forall me src m st out st' ps out',
     net_handlers me src m st = (out, st', ps) ->
     handler (tot_one_map_msg me src m) (tot_one_map_data st) = (out', tot_one_map_data st') ;
   tot_input_handlers_handler_eq : forall me inp st out st' ps out',
     input_handlers me inp st = (out, st', ps) ->
     handler (tot_one_map_input me inp) (tot_one_map_data st) = (out', tot_one_map_data st')
 }.

Section TotalMapBijective.

Context `{MB : MultiParamsNameTotalMapBijective}.

Lemma tot_map_name_injective : 
  forall n n', tot_map_name n = tot_map_name n' -> n = n'.
Proof.
move => n n'.
case (name_eq_dec n n') => H_dec //.
move => H_eq.
case: H_dec.
by rewrite -(tot_map_name_inv_inverse n) H_eq tot_map_name_inv_inverse.
Qed.

End TotalMapBijective.

Section TotalMapSimulations.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.

Definition tot_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) :=
match e with
| (n, inl io) => (tot_map_name n, inl (tot_map_input io))
| (n, inr lo) => (tot_map_name n, inr (map tot_map_output lo))
end.

Definition tot_map_packet (p : @packet base_fst multi_fst)  :=
match p with
| mkPacket src dst m =>
  mkPacket (tot_map_name src) (tot_map_name dst) (tot_map_msg m)
end.

Definition tot_map_net (net : @network _ multi_fst) : @network _ multi_snd :=
  {| nwPackets := map tot_map_packet net.(nwPackets) ;
     nwState := fun n => tot_map_data (net.(nwState) (tot_map_name_inv n)) |}.

Lemma tot_map_update_eq :
  forall f d h,
    (fun n : name => tot_map_data (update f h d (tot_map_name_inv n))) =
    update (fun n : name => tot_map_data (f (tot_map_name_inv n))) (tot_map_name h) (tot_map_data d).
Proof.
move => net d h.
apply functional_extensionality => n.
rewrite /update /=.
repeat break_match => //.
- by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
- by find_rewrite; find_rewrite_lem tot_map_name_inv_inverse.
Qed.

Corollary tot_map_update_packet_eq :
forall f p d,
  (fun n : name => tot_map_data (update f (pDst p) d (tot_map_name_inv n))) =
  (update (fun n : name => tot_map_data (f (tot_map_name_inv n))) (pDst (tot_map_packet p)) (tot_map_data d)).
Proof.
move => f.
case => src dst m d.
exact: tot_map_update_eq.
Qed.

Lemma tot_map_packet_map_eq :
  forall l h,
    map tot_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) = 
    map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (tot_map_name_msgs l).
Proof.
elim => //=.
case => /= n m' l IH h.
by rewrite IH.
Qed.

Lemma tot_init_handlers_fun_eq : 
    init_handlers = fun n : name => tot_map_data (init_handlers (tot_map_name_inv n)).
Proof.
apply functional_extensionality => n.
by rewrite tot_init_handlers_eq tot_map_name_inverse_inv.
Qed.

Lemma tot_map_trace_occ_inv : 
  forall tr n ol,
    map tot_map_trace_occ tr = [(n, inr ol)] -> 
    exists n', exists lo, tr = [(n', inr lo)] /\ tot_map_name n' = n /\ map tot_map_output lo = ol.
Proof.
case => //=.
case.
move => n ol tr n' lo H_eq.
case: tr H_eq => //=.
case: ol => //=.
move => out H_eq.
exists n; exists out.
split => //.
by inversion H_eq.
Qed.

Lemma tot_map_trace_occ_in_inv : 
  forall tr h inp out,
    map tot_map_trace_occ tr = [(h, inl inp); (h, inr out)] -> 
    exists h', exists inp', exists out', tr = [(h', inl inp'); (h', inr out')] /\ 
      tot_map_name h' = h /\ map tot_map_output out' = out /\ tot_map_input inp' = inp.
Proof.
case => //=.
case.
move => h.
case => //.
move => inp.
case => //.
case.
move => h'.
case => //.
move => out.
case => //=.
move => h0.
move => inp' out' H_eq.
inversion H_eq.
find_apply_lem_hyp tot_map_name_injective.
repeat find_rewrite.
by exists h; exists inp; exists out.
Qed.

Theorem step_m_tot_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    @step_m _ multi_snd (tot_map_net net) (tot_map_net net') (map tot_map_trace_occ tr).
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /tot_map_trace_occ /=.
  have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by case: p H_eq H_hnd H_eq' => src dst m H_eq H_hnd H_eq'.
  apply (@SM_deliver _ _ _ _ _ (map tot_map_packet ms) (map tot_map_packet ms') (map tot_map_output out) (tot_map_data d) (tot_map_name_msgs l)).
  * by rewrite /tot_map_net /= H_eq /= map_app.
  * rewrite /=.
    case: p H_eq H_hnd H_eq' => /= src dst m H_eq H_hnd H_eq'.
    have H_q := tot_net_handlers_eq dst src m (nwState net dst).
    rewrite /tot_mapped_net_handlers in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= H_eq' /= /tot_map_net /=.
    rewrite -tot_map_update_packet_eq.
    rewrite 2!map_app.
    destruct p.
    by rewrite tot_map_packet_map_eq.
- move => h net net' out inp d l H_hnd H_eq.
  apply (@SM_input _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
    rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  rewrite /= H_eq /= /tot_map_net /=.
  by rewrite -tot_map_update_eq map_app tot_map_packet_map_eq.
Qed.

Corollary step_m_tot_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    @step_m_star _ multi_snd step_m_init (tot_map_net net) (map tot_map_trace_occ tr).
Proof.
move => net tr H_step.
remember step_m_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_m_init /= /tot_map_net /=.
  rewrite tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
find_apply_lem_hyp step_m_tot_mapped_simulation_1.
rewrite map_app.
match goal with
| H : step_m_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
end.
rewrite (app_nil_end (map _ _)).
apply: (@RT1nTStep _ _ _ _ (tot_map_net x'')) => //.
exact: RT1nTBase.
Qed.

Theorem step_m_tot_mapped_simulation_2 :
  forall net net' out mnet mout,
      @step_m _ multi_snd net net' out ->
      tot_map_net mnet = net ->
      map tot_map_trace_occ mout = out ->
      exists mnet', @step_m _ multi_fst mnet mnet' mout /\
      tot_map_net mnet' = net'.
Proof.
move => net net' out mnet mout H_step H_eq H_eq'.
invcs H_step.
- destruct p.
  rewrite /tot_map_net /=.
  destruct mnet.
  rewrite /=.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (Net.pDst p) l' ++ pks1 ++ pks2 ; nwState := update nwState (Net.pDst p) d' |}.
  split.
  * match goal with
    | H : _ = map tot_map_trace_occ _ |- _ => 
      have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H)
    end.
    rewrite H_eq_mout.
    have H_eq_dst: n' = Net.pDst p.
      rewrite -(tot_map_name_inv_inverse n') H_eq_n.
      destruct p.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    apply (@SM_deliver _ _ _ _ _ pks1 pks2 _ d' l') => //=.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    simpl in *.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite H_eq_body in H_eq_hnd.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -H_eq_n tot_map_name_inv_inverse H_eq_dst in H ;
        rewrite H in H_eq_hnd
    end.
    find_inversion.
    find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
    by symmetry.
  * rewrite /= /update /=.
    have H_eq_dst: tot_map_name (Net.pDst p) = pDst by destruct p; find_inversion.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; find_inversion.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; find_inversion.
    rewrite 2!map_app.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    simpl in *.       
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H;
        rewrite H in H_eq_hnd
    end.
    find_inversion; clean.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2.
      elim l' => //=.
      case => /= n' m' l0 IH.
      rewrite IH.
      by find_rewrite.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.    
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite. 
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  destruct mnet.
  simpl in *.
  match goal with
  | H: _ = map tot_map_trace_occ _ |- _ => 
    have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H)
  end.
  have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h' inp' (nwState h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  match goal with
    | H: input_handlers _ _ (tot_map_data (_ (tot_map_name_inv h))) = _ |- _ => 
      rewrite -{2}H_eq_n tot_map_name_inv_inverse in H;
        rewrite H in H_q
  end.
  find_inversion.
  find_inversion.
  exists ({| nwPackets := send_packets h' l0 ++ nwPackets ; nwState := update nwState h' d0 |}).
  split.
  * apply (@SM_input _ _ _ _ _ _ _ d0 l0) => //=.
    find_rewrite.
    suff H_suff: l1 = out' by rewrite H_suff.
    by find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {nwP1 nwP2}.
      elim l0 => //=.
      case => /= n m l' IH.
      by rewrite IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite.
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_nwp H_eq_nws.
Qed.

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.

Lemma not_in_failed_not_in :
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

Lemma in_failed_in :
  forall n failed,
    In n failed ->
    In (tot_map_name n) (map tot_map_name failed).
Proof.
move => n.
elim => //.
move => n' l IH H_in.
case: H_in => H_in.
  rewrite H_in.
  by left.
right.
exact: IH.
Qed.

Lemma remove_tot_map_eq :
  forall h failed,
    map tot_map_name (remove name_eq_dec h failed) =
    remove name_eq_dec (tot_map_name h) (map tot_map_name failed).
Proof.
move => h.
elim => //=.
move => n failed IH.
repeat break_if => //.
- by find_rewrite.
- by find_apply_lem_hyp tot_map_name_injective.
- by rewrite /= IH.
Qed.

Lemma tot_map_reboot_eq :
forall h net,
    (fun n : name => 
      tot_map_data 
        (match name_eq_dec (tot_map_name_inv n) h with
         | left _ => reboot (nwState net (tot_map_name_inv n))
         | right _ => nwState net (tot_map_name_inv n)
        end)) =
    (fun nm : name =>
       match name_eq_dec nm (tot_map_name h) with
       | left _ => reboot (tot_map_data (nwState net (tot_map_name_inv nm)))
       | right _ => tot_map_data (nwState net (tot_map_name_inv nm))
       end).
Proof.
move => h net.
apply: functional_extensionality => n.
repeat break_if => //.
- by rewrite tot_reboot_eq.
- find_reverse_rewrite.
  by find_rewrite_lem tot_map_name_inverse_inv.
- find_rewrite.
  by find_rewrite_lem tot_map_name_inv_inverse.
Qed.

Theorem step_f_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_f _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_f _ _ fail_snd (map tot_map_name failed, tot_map_net net) (map tot_map_name failed', tot_map_net net') (map tot_map_trace_occ tr).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by destruct p.
  apply (@SF_deliver _ _ _ _ _ _ _ (map tot_map_packet xs) (map tot_map_packet ys) _ (tot_map_data d) (tot_map_name_msgs l)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * destruct p.
    exact: not_in_failed_not_in.
  * destruct p.
    simpl in *.
    have H_q := tot_net_handlers_eq pDst pSrc pBody (nwState net pDst).
    rewrite /tot_mapped_net_handlers in H_q.
    find_rewrite.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= -tot_map_update_packet_eq /= /tot_map_net /=.
    destruct p.
    by rewrite 2!map_app tot_map_packet_map_eq.
- apply (@SF_input _ _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /=.
    have H_q := tot_input_handlers_eq h inp (nwState net h).
    rewrite /tot_mapped_input_handlers /= in H_q.
    find_rewrite.
    rewrite H_q.
    by rewrite tot_map_name_inv_inverse.
  * rewrite /= /tot_map_net /= -tot_map_update_eq.
    by rewrite map_app tot_map_packet_map_eq.
- apply (@SF_drop _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * by rewrite /tot_map_net /= map_app.
- apply (@SF_dup _ _ _ _ _ _ (tot_map_packet p) (map tot_map_packet xs) (map tot_map_packet ys)).
  * rewrite /tot_map_net /=.
    find_rewrite.
    by rewrite map_app.
  * by rewrite /tot_map_net /= map_app.
- exact: SF_fail.
- apply: (SF_reboot (tot_map_name h)).
  * exact: in_failed_in.
  * by rewrite remove_tot_map_eq.
  * by rewrite /tot_map_net /= tot_map_reboot_eq.
Qed.

Corollary step_f_tot_mapped_simulation_star_1 :
  forall net failed tr,
    @step_f_star _ _ fail_fst step_f_init (failed, net) tr ->
    @step_f_star _ _ fail_snd step_f_init (map tot_map_name failed, tot_map_net net) (map tot_map_trace_occ tr).
Proof.
move => net failed tr H_step.
remember step_f_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /step_f_init /= /step_m_init /tot_map_net /= tot_init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
destruct x'.
destruct x''.
rewrite /=.
find_apply_lem_hyp step_f_tot_mapped_simulation_1.
rewrite map_app.
match goal with
| H : step_f_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H)
end.
rewrite (app_nil_end (map tot_map_trace_occ _)).
apply (@RT1nTStep _ _ _ _ (map tot_map_name l0, tot_map_net n0)) => //.
exact: RT1nTBase.
Qed.

Lemma map_eq_name_eq_eq :
  forall l l', map tot_map_name l = map tot_map_name l' -> l = l'.
Proof.
elim.
case => //=.
move => n l IH.
case => //=.
move => n' l' H_eq.
inversion H_eq.
find_apply_lem_hyp tot_map_name_injective.
find_eapply_lem_hyp IH.
by repeat find_rewrite.
Qed.

Theorem step_f_tot_mapped_simulation_2 :
  forall net net' failed failed' out mnet mfailed mfailed' mout,
      @step_f _ _ fail_snd (failed, net) (failed', net') out ->
      tot_map_net mnet = net ->
      map tot_map_name mfailed = failed ->
      map tot_map_name mfailed' = failed' ->
      map tot_map_trace_occ mout = out ->
      exists mnet', @step_f _ _ fail_fst (mfailed, mnet) (mfailed', mnet') mout /\
      tot_map_net mnet' = net'.
Proof.
move => net net' failed failed' out mnet mfailed mfailed' mout H_step H_eq_net H_eq_f H_eq_f' H_eq_out.
invcs H_step.
- destruct p.
  rewrite /tot_map_net /=.
  destruct mnet.
  simpl in *.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (Net.pDst p) l' ++ pks1 ++ pks2 ; nwState := update nwState (Net.pDst p) d' |}.
  split.
  * match goal with
    | H : _ = map tot_map_trace_occ _ |- _ => 
      have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H)
    end.
    rewrite H_eq_mout.
    have H_eq_dst: n' = Net.pDst p.
      rewrite -(tot_map_name_inv_inverse n') H_eq_n.
      destruct p.
      simpl in *.
      find_inversion.
      by rewrite tot_map_name_inv_inverse.
    rewrite H_eq_dst.
    match goal with
    | H: map tot_map_name _ = map tot_map_name _ |- _ =>
      apply map_eq_name_eq_eq in H; rewrite H
    end.
    apply (@SF_deliver _ _ _ _ _ _ _ pks1 pks2 _ d' l') => //=.
      rewrite -H_eq_dst => H_in.
      find_apply_lem_hyp in_failed_in.
      by find_rewrite_lem H_eq_n.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite H_eq_body in H_eq_hnd.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -H_eq_n tot_map_name_inv_inverse H_eq_dst in H ;
        rewrite H in H_eq_hnd
    end.
    find_inversion.
    find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
    by symmetry.
  * rewrite /= /update /=.
    have H_eq_dst: tot_map_name (Net.pDst p) = pDst by destruct p; simpl in *; find_inversion.
    have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
    have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
    rewrite 2!map_app.
    have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
    rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    simpl in *.
    match goal with
    | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => 
      rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H;
        rewrite H in H_eq_hnd
    end.
    find_inversion; clean.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2.
      elim l' => //=.
      case => /= n' m' l0 IH.
      rewrite IH.
      by find_rewrite.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      repeat break_if => //.
      + find_reverse_rewrite. 
        by find_rewrite_lem tot_map_name_inverse_inv.
      + find_rewrite. 
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_sw.
- rewrite /tot_map_net /=.
  destruct mnet.
  match goal with
  | H: _ = map tot_map_trace_occ _ |- _ => 
    have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H)
  end.
  have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h' inp' (nwState h').
  rewrite /tot_mapped_input_handlers in H_q.
  repeat break_let.
  rewrite H_eq_n H_eq_inp in H_q.
  match goal with
    | H: input_handlers _ _ (tot_map_data (_ (tot_map_name_inv h))) = _ |- _ => 
      rewrite -{2}H_eq_n tot_map_name_inv_inverse in H ;
        rewrite H in H_q
    end.
  inversion H_q.
  simpl in *.
  find_apply_lem_hyp map_eq_name_eq_eq.   
  exists ({| nwPackets := send_packets h' l0 ++ nwPackets ; nwState := update nwState h' d0 |}).
  split.
  * rewrite H_eq_mout.
    match goal with
    | H: mfailed = _ |- _ => rewrite H
    end.
    apply (@SF_input _ _ _ _ _ _ _ _ _ d0 l0) => //.      
      move => H_in.
      apply in_failed_in in H_in.
      by rewrite H_eq_n in H_in.
    rewrite /= Heqp.
    suff H_suff: l1 = out' by rewrite H_suff.
    match goal with
    | H: map tot_map_output _ = _ |- _ => rewrite -H_eq_out in H
    end.    
    by find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
  * rewrite /= map_app.
    set nwP1 := map tot_map_packet _.
    set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := update _ _ _.
    have H_eq_nwp: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {Heqp H_q nwP1 nwP2}.
      elim l0 => //=.
      case => /= n m l' IH.
      by rewrite H_eq_n IH.
    have H_eq_nws: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      rewrite /update /=.
      apply functional_extensionality => n.
      rewrite -H_eq_n.
      repeat break_if => //.
      + match goal with
        | H: _ = h' , H': _ <> tot_map_name h' |- _ => 
          rewrite -H in H'
        end.
        by find_rewrite_lem tot_map_name_inverse_inv.
      + match goal with
        | H: n = _ , H': tot_map_name_inv n <> _ |- _ => 
          rewrite H in H'
        end.
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_nwp H_eq_nws.
- destruct mout => //.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_reverse_rewrite.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := pks1 ++ pks2 ; nwState := nwState mnet |}.
  split; first exact: (@SF_drop _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.
- destruct mout => //.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_rewrite.
  match goal with
  | H : map tot_map_packet _ = _ |- _ => 
    have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H
  end.
  case: pks2 H_eq_pks H_eq_pks2 => //= p' pks2 H_eq_pks H_eq_pks2.
  inversion H_eq_pks2.
  rewrite -H_eq_pks1.
  exists {| nwPackets := p' :: pks1 ++ p' :: pks2 ; nwState := nwState mnet |}.
  split; first exact: (@SF_dup _ _ _ _ _ _ p' pks1 pks2).
  by rewrite /tot_map_net /= map_app.  
- destruct mout => //.
  destruct mfailed' => //.
  simpl in *.
  find_inversion.
  find_apply_lem_hyp map_eq_name_eq_eq.
  find_rewrite.
  exists mnet => //.
  split => //.
  exact: SF_fail.
- destruct mout => //.
  find_copy_apply_lem_hyp in_split.
  break_exists.
  match goal with
  | H: map tot_map_name _ = _ |- _ =>
    have [mns1 [mns2 [H_eq_mns [H_eq_mns1 H_eq_mns2]]]] := map_eq_inv _ _ _ _ H
  end.
  destruct mns2 => //.
  exists {| nwPackets := nwPackets mnet ; 
       nwState := (fun nm => match name_eq_dec nm n with
                           | left _ => (reboot (nwState mnet nm)) 
                           | right _ => (nwState mnet nm) 
                           end) |}.
  split.
  * apply (@SF_reboot _ _ _ n) => //.
    + rewrite H_eq_mns.
      apply in_or_app.
      by right; left.
    + inversion H_eq_mns2.
      have H_eq: remove name_eq_dec h (map tot_map_name mfailed) = map tot_map_name (remove name_eq_dec n mfailed).
        elim mfailed => //=.
        move => n' l IH.
        repeat break_if => //.
        + by find_reverse_rewrite; find_apply_lem_hyp tot_map_name_injective.
        + by find_reverse_rewrite; find_reverse_rewrite.
        + by rewrite /= IH.
      match goal with
      | H: _ = remove _ _ _ |- _ => rewrite H_eq in H
      end.
      by find_apply_lem_hyp map_eq_name_eq_eq.
  * rewrite /tot_map_net /=.
    inversion H_eq_mns2.
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2 {nwS1 nwS2}.
      apply functional_extensionality => n'.
      repeat break_if => //.
      + by rewrite tot_reboot_eq.
      + by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
      + match goal with
        | H: n' = _ , H': tot_map_name_inv n' <> _ |- _ => rewrite H in H'
        end.
        by find_rewrite_lem tot_map_name_inv_inverse.
    by rewrite H_eq_sw.
Qed.

Lemma nodup_to_map_name :
  forall ns, NoDup ns ->
        NoDup (map tot_map_name ns).
Proof.
elim => /=; first by move => H_nd; exact: NoDup_nil.
move => n ns IH H_nd.
inversion H_nd.
find_apply_lem_hyp IH.
by apply NoDup_cons; first exact: not_in_failed_not_in.  
Qed.

Lemma permutation_nodes :
  Permutation nodes (map tot_map_name nodes).
Proof.
apply: NoDup_Permutation; last split.
- exact: no_dup_nodes.
- apply nodup_to_map_name.
  exact: no_dup_nodes.
- move => H_in.
  set x' := tot_map_name_inv x.
  have H_in' := all_names_nodes x'. 
  apply in_split in H_in'.
  move: H_in' => [ns1 [ns2 H_eq]].
  rewrite H_eq map_app /= /x'.
  apply in_or_app.
  right; left.
  by rewrite tot_map_name_inverse_inv.
- move => H_in.
  exact: all_names_nodes.
Qed.

Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.

Lemma tot_map_in_snd :
forall h m ns nm,
   In nm
     (map
        (fun nm0 : name * msg =>
         (tot_map_name (fst nm0), tot_map_msg (snd nm0)))
        (map_pair m (filter_rel h ns))) ->
   snd nm = tot_map_msg m.
Proof.
move => h m.
elim => //=.
move => n ns IH.
case (rel_dec _ _) => H_dec /=.
  case => n' m' H_in.
  case: H_in => H_in.
    by inversion H_in.
  exact: IH.
exact: IH.
Qed.

Lemma tot_map_in_in :
  forall n m l,
  (forall nm, In nm l -> snd nm = m) ->
  ~ In (n, m) l ->
  ~ In (tot_map_name n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof.
move => n m.
elim => //=.
case => /= n' m' l IH H_eq H_in.
move => H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  have H_nm := H_eq (n', m').
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
  apply: H_eq.
  by right.
move => H_in_nm.
case: H_in.
by right.
Qed.

Lemma msg_in_map :
  forall m l n m',
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name n, tot_map_msg m') (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) ->
    tot_map_msg m' = tot_map_msg m.
Proof.
move => m.
elim => //=.
case => /= n m' l IH n' m0 H_in H_in_map.
have H_in_f := H_in (n, m').
rewrite /= in H_in_f.
case: H_in_map => H_in_map.
  inversion H_in_map.
  rewrite H_in_f //.
  by left.
move: H_in_map.
apply: IH.
move => nm H_in'.
apply: H_in.
by right.
Qed.

Lemma nodup_tot_map :
  forall m nms,
  (forall nm, In nm nms -> snd nm = m) ->
  NoDup nms ->
  NoDup (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) nms).
Proof.
move => m'.
elim => /=.
  move => H_fail H_nd.
  exact: NoDup_nil.
case => n m l IH H_fail H_nd.
inversion H_nd.
rewrite /=.
apply NoDup_cons.
  have H_f := H_fail (n, m).
  rewrite /= in H_f.
  move => H_in.
   have H_inf := @msg_in_map m' _ _ _ _ H_in.
   rewrite H_inf in H_in.
     contradict H_in.
     apply tot_map_in_in.
       move => nm H_in_nm.
       apply: H_fail.
       by right.
     rewrite H_f // in H1.
     by left.
   move => nm H_in_f.
   apply: H_fail.
   by right.
apply: IH => //.
move => nm H_in_nm.
apply: H_fail.
by right.
Qed.

Lemma in_tot_map_name :
forall m l n,
  (forall nm, In nm l -> snd nm = m) ->
  In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) ->
  In (tot_map_name_inv n, m) l.
Proof.
move => m.
elim => //=.
case => /= n m' l IH n' H_in H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  rewrite tot_map_name_inv_inverse.
  have H_nm := H_in (n, m').
  rewrite -H_nm /=; first by left.
  by left.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma in_map_pair_adjacent_to :
  forall (m : msg) ns failed h n,
    In (tot_map_name_inv n, m) (map_pair m (filter_rel h (exclude failed ns))) ->
    In (tot_map_name_inv n) (filter_rel h (exclude failed ns)).
Proof.
move => m.
elim => //=.
move => n l IH failed h n'. 
case (in_dec _ _ _) => H_dec; first exact: IH.
rewrite /=.
case (rel_dec _ _) => H_dec' /=.
  move => H_in.
  case: H_in => H_in.
    inversion H_in.
    by left.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma in_adjacent_exclude_in_exlude :
  forall ns failed n h,
    In (tot_map_name_inv n) (filter_rel h (exclude failed ns)) ->
    In (tot_map_name_inv n) (exclude failed ns) /\ adjacent_to h (tot_map_name_inv n).
Proof.
elim => //=.
move => n l IH failed n' h.
case (in_dec _ _ _) => /= H_dec.
  move => H_in.
  exact: IH.
case (rel_dec _ _) => /= H_dec'.
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

Lemma in_failed_exclude :
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

Lemma in_in_adj_map_pair :
  forall (m : msg) ns failed n h,
    In n ns ->
    ~ In n (map tot_map_name failed) ->
    adjacent_to h n ->
    In (n, m)
     (map_pair m
        (filter_rel h
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
  case (rel_dec _ _) => H_dec' //.
  rewrite /=.
  by left.
rewrite /=.
case (rel_dec _ _) => H_dec'.
  rewrite /=.
  right.
  exact: IH.
exact: IH.
Qed.

Lemma in_exclude_not_in_failed_map :
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

Lemma not_in_map_not_in_failed :
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

Lemma in_tot_map_msg :
  forall m l n,
    (forall nm, In nm l -> snd nm = m) ->
    In (tot_map_name_inv n, m) l ->
    In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof.
move => m.
elim => //=.
case => n m' /= l IH n' H_in H_in'.
case: H_in' => H_in'.
  inversion H_in'.
  left.
  by rewrite tot_map_name_inverse_inv.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.
Qed.

Lemma adjacent_in_in_msg :
  forall (m : @msg base_fst multi_fst) ns n h,
    adjacent_to h (tot_map_name_inv n) ->
    In (tot_map_name_inv n) ns ->
    In (tot_map_name_inv n, m) (map_pair m (filter_rel h ns)).
Proof.
move => m.
elim => //=.
move => n ns IH n' h H_adj H_in.
case (rel_dec _ _) => H_dec; case: H_in => H_in.
- rewrite /=.
  left.
  by rewrite H_in.
- rewrite /=.
  right.
  exact: IH.
- by rewrite H_in in H_dec.
- exact: IH.
Qed.

Lemma not_in_failed_in_exclude :
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

Lemma map_map_pair_eq :
  forall h m failed,
  Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map_pair m (filter_rel h (exclude failed nodes)))) 
    (map_pair (tot_map_msg m) (filter_rel (tot_map_name h) (exclude (map tot_map_name failed) nodes))).
Proof.
move => h m failed.
apply NoDup_Permutation; last split.
- apply (@nodup_tot_map m); first exact: in_for_msg.
  apply nodup_map_pair.
  apply nodup_exclude.
  exact: no_dup_nodes.
- apply nodup_map_pair.
  apply nodup_exclude.
  exact: no_dup_nodes.
- case: x => n m' H_in.
  have H_eq := tot_map_in_snd _ _ _ _ H_in.
  rewrite /= in H_eq.
  rewrite H_eq in H_in.
  rewrite H_eq {H_eq}.
  apply in_tot_map_name in H_in.
    apply in_map_pair_related_in in H_in. 
    move: H_in => [H_adj H_in].
    apply in_failed_exclude in H_in.
    move: H_in => [H_in H_in'].
    have H_nin: ~ In n (map tot_map_name failed).
      rewrite -(tot_map_name_inverse_inv n).
      exact: not_in_failed_not_in.
    apply tot_adjacent_to_fst_snd in H_adj.
    rewrite tot_map_name_inverse_inv in H_adj.
    have H_inn: In n nodes by exact: all_names_nodes.
    exact: in_in_adj_map_pair.
  exact: in_for_msg.
- case: x => n m' H_in.
  have H_eq := in_for_msg _ _ _ _ H_in.
  rewrite /= in H_eq.
  rewrite H_eq.
  rewrite H_eq in H_in.
  apply in_map_pair_related_in in H_in.
  move: H_in => [H_adj H_in].
  rewrite -(tot_map_name_inverse_inv n) in H_adj.
  apply tot_adjacent_to_fst_snd in H_adj.
  apply in_exclude_not_in_failed_map in H_in.
  move: H_in => [H_in_f H_in].
  apply not_in_map_not_in_failed in H_in_f.
  have H_in_n: In (tot_map_name_inv n) nodes by exact: all_names_nodes.
  apply in_tot_map_msg; first by move => nm; apply in_for_msg.
  apply: adjacent_in_in_msg => //.
  exact: not_in_failed_in_exclude.
Qed.

Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsTotalMapCongruency fail_msg_fst fail_msg_snd msg_map}.

Lemma map_msg_fail_eq :
  forall h failed,
   Permutation 
    (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map_pair msg_fail (filter_rel h (exclude failed nodes)))) 
    (map_pair msg_fail (filter_rel (tot_map_name h) (exclude (map tot_map_name failed) nodes))).
Proof.
move => h failed.
rewrite tot_fail_msg_fst_snd.
exact: map_map_pair_eq.
Qed.

Definition tot_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd :=
  {| onwPackets := fun src dst => map tot_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ;
     onwState := fun n => tot_map_data (onet.(onwState) (tot_map_name_inv n)) |}.

Lemma map_msg_update2 : 
  forall f ms to from,
    (fun src dst => map tot_map_msg (update2 f from to ms (tot_map_name_inv src) (tot_map_name_inv dst))) =
    update2 (fun src0 dst0 : name => map tot_map_msg (f (tot_map_name_inv src0) (tot_map_name_inv dst0)))
        (tot_map_name from) (tot_map_name to) (map tot_map_msg ms).
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

Lemma collate_tot_map_eq :
  forall f h l,
    (fun src dst => map tot_map_msg (collate h f l (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate (tot_map_name h) (fun src dst => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name_msgs l).
Proof.
move => f h l.
elim: l h f => //.
case => n m l IH h f.
rewrite /= IH /=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _.
have H_eq_f: f1 = f2.
  rewrite /f1 /f2 {f1 f2}.
  have H_eq := map_msg_update2 f (f h n ++ [m]) n h.
  rewrite map_app in H_eq.
  by rewrite H_eq.
by rewrite H_eq_f.
Qed.

Lemma collate_tot_map_update2_eq :
  forall f from to ms l,
    (fun src dst => map tot_map_msg
            (collate to (update2 f from to ms) l
               (tot_map_name_inv src) (tot_map_name_inv dst))) =
    collate (tot_map_name to)
            (update2
               (fun src dst : name =>
                map tot_map_msg
                  (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name from)
               (tot_map_name to) (map tot_map_msg ms)) (tot_map_name_msgs l).
Proof.
move => f from to ms l.
rewrite -map_msg_update2.
by rewrite collate_tot_map_eq.
Qed.

Theorem step_o_f_tot_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_o_f _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    @step_o_f _ _ overlay_snd fail_msg_snd (map tot_map_name failed, tot_map_onet net) (map tot_map_name failed', tot_map_onet net') (map tot_map_trace_occ tr).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- rewrite /tot_map_onet /=.
  apply (@SOF_deliver _ _ _ _ _ _ _ (tot_map_msg m) (map tot_map_msg ms) _ (tot_map_data d) (tot_map_name_msgs l) (tot_map_name from)).
  * by rewrite /tot_map_net /= 2!tot_map_name_inv_inverse /= H3.
  * exact: not_in_failed_not_in.
  * rewrite /= tot_map_name_inv_inverse -tot_net_handlers_eq /tot_mapped_net_handlers /=.
    repeat break_let.
    by inversion H6.
  * by rewrite /= tot_map_update_eq collate_tot_map_update2_eq.
- rewrite /tot_map_onet /=.
  apply (@SOF_input _ _ _ _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /= tot_map_name_inv_inverse -tot_input_handlers_eq /tot_mapped_input_handlers.
    repeat break_let.
    by inversion H5.
  * by rewrite /= /tot_map_onet /= tot_map_update_eq collate_tot_map_eq.
- rewrite /tot_map_onet /=.  
  set l := map_pair _ _.
  have H_nd: NoDup (map (fun nm => fst nm) (tot_map_name_msgs l)).
    rewrite /tot_map_name_msgs /=.
    rewrite /l {l}.
    apply nodup_snd_fst.
      apply (@nodup_tot_map msg_fail); first exact: in_for_msg.
      apply nodup_map_pair.
      apply nodup_exclude.
      exact: no_dup_nodes.
    move => nm nm' H_in H_in'.
    have H_fail := tot_map_in_snd _ _ _ _ H_in.
    have H_fail' := tot_map_in_snd _ _ _ _ H_in'.
    by rewrite H_fail H_fail'.
  have H_pm := map_msg_fail_eq h failed.
  have H_eq := nodup_perm_collate_eq _ _ H_nd H_pm.
  rewrite /l /tot_map_name_msgs in H_eq.
  apply: SOF_fail.
  * exact: not_in_failed_not_in.
  * rewrite /=.
    rewrite /l collate_tot_map_eq /tot_map_name_msgs.
    by rewrite H_eq.
Qed.

Context {one_snd : OneNodeParams base_snd}.
Context {multi_fst_snd : MultiOneNodeParamsTotalMap multi_fst base_snd}.
Context {multi_one : MultiOneNodeParamsTotalMapCongruency one_snd multi_fst_snd}.

Theorem step_m_tot_one_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    forall n, net.(nwState) n = net'.(nwState) n \/
    exists tr', @step_1 _ one_snd (tot_one_map_data (net.(nwState) n)) (tot_one_map_data (net'.(nwState) n)) tr'.
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq' n.
  rewrite H_eq' /= /update.
  break_if; last by left.
  right.
  rewrite -e in H_hnd.
  case H_h: (handler (tot_one_map_msg (pDst p) (pSrc p) (pBody p)) (tot_one_map_data (nwState net (pDst p)))) => [out' st'].
  apply (tot_net_handlers_handler_eq _ _ _ _ out') in H_hnd.
  exists [(tot_one_map_msg (pDst p) (pSrc p) (pBody p), out')].
  apply: S1T_deliver => //.
  by rewrite -H_hnd e.
- move => h net net' out inp d ps H_hnd H_eq n.
  rewrite H_eq /= /update.
  break_if; last by left.
  right.
  rewrite e.
  case (handler (tot_one_map_input h inp) (tot_one_map_data (nwState net h))) => [out' st'].
  apply (tot_input_handlers_handler_eq _ _ _ out') in H_hnd.
  exists [((tot_one_map_input h inp), out')].
  exact: S1T_deliver.
Qed.

Corollary step_m_tot_one_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    forall n, exists tr', @step_1_star _ one_snd init (tot_one_map_data (net.(nwState) n)) tr'.
Proof.
move => net tr H_st.
remember step_m_init as y in *.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => H_init /=.
  move => n.
  rewrite H_init /step_m_init /=.
  rewrite tot_init_eq.
  exists [].
  exact: RT1nTBase.
concludes.
repeat find_rewrite.
move => n.
have H_st' := step_m_tot_one_mapped_simulation_1 H n.
have [tr' H_st] := IHH_st1 n.
case: H_st' => H_st'.
  rewrite -H_st'.
  by exists tr'.
move: H_st' => [tr'' H_st'].
exists (tr' ++ tr'').
have H_trans := refl_trans_1n_trace_trans H_st.
apply: H_trans.
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply: (@RT1nTStep _ _ _ _ (tot_one_map_data (nwState x'' n))) => //.
exact: RT1nTBase.
Qed.

Theorem step_o_f_tot_one_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_o_f _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr ->
    forall n, net.(onwState) n = net'.(onwState) n \/
    exists tr', @step_1 _ one_snd (tot_one_map_data (net.(onwState) n)) (tot_one_map_data (net'.(onwState) n)) tr'.
Proof.
move => net net' failed failed' tr H_step n.
invcs H_step.
- rewrite /update'.
  break_if; last by left.
  right.
  rewrite -e in H6.
  case H_h: (handler (tot_one_map_msg to from m) (tot_one_map_data (onwState net n))) => [out' st'].
  apply (tot_net_handlers_handler_eq _ _ _ _ out') in H6.
  exists [(tot_one_map_msg to from m, out')].
  apply: S1T_deliver => //.
  by rewrite -H6 e.
- rewrite /update'.
  break_if; last by left.
  right.
  rewrite e.
  case (handler (tot_one_map_input h inp) (tot_one_map_data (onwState net h))) => [out' st'].
  apply (tot_input_handlers_handler_eq _ _ _ out') in H5.
  exists [((tot_one_map_input h inp), out')].
  exact: S1T_deliver.
- by left.
Qed.

Corollary step_o_f_tot_one_mapped_simulation_star_1 :
  forall net failed tr,
    @step_o_f_star _ _ overlay_fst fail_msg_fst step_o_f_init (failed, net) tr ->
    forall n, exists tr', @step_1_star _ one_snd init (tot_one_map_data (net.(onwState) n)) tr'.
Proof.
move => net failed tr H_st.
remember step_o_f_init as y in *.
have H_eq_n: net = snd (failed, net) by [].
rewrite H_eq_n {H_eq_n}.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init /=.
  move => n.
  exists [].
  rewrite tot_init_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_st1 H_st2.
case: x' H IHH_st1 H_st1 => failed' net'.
case: x'' H_st2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1 n.
have H_stt := step_o_f_tot_one_mapped_simulation_1 H n.
case: H_stt => H_stt.
  rewrite -H_stt.
  have [tr' H_star] := IHH_step1 n.
  by exists tr'.
have [tr' H_star] := IHH_step1 n.
have [tr'' H_step] := H_stt.
exists (tr' ++ tr'').
have H_trans := refl_trans_1n_trace_trans H_star.
apply: H_trans.
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply RT1nTStep with (x' := (tot_one_map_data (onwState net'' n))) => //.
exact: RT1nTBase.
Qed.

(*
Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.

Theorem step_o_d_f_tot_one_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_o_d_f _ _ overlay_fst new_msg_fst fail_msg_fst (failed, net) (failed', net') tr ->
    forall n, In n net.(odnwNodes) ->
    forall d, net.(odnwState) n = Some d ->
    forall d', net'.(odnwState) n = Some d' ->
    d = d' \/ exists tr', @step_1 _ one_snd (tot_one_map_data d) (tot_one_map_data d') tr'.
Proof.
Admitted.

Corollary step_o_d_f_tot_one_mapped_simulation_star_1 :
  forall net failed tr,
    @step_o_d_f_star _ _ overlay_fst new_msg_fst fail_msg_fst step_o_f_init (failed, net) tr ->
    forall n, In n net.(odnwNodes) ->
    exists tr', @step_1_star _ one_snd init (tot_one_map_data (net.(onwState) n)) tr'.
Proof.
*)

End TotalMapSimulations.
