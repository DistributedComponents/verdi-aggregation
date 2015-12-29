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

Require Import Sumbool.
Require Import FunctionalExtensionality.

Require Import ssreflect.

Set Implicit Arguments.

Class BaseParamsEqMap (P0 : BaseParams) (P1 : BaseParams) := 
  {
    eq_map_data : @data P0 -> @data P1 ;
    eq_map_input : @input P0 -> @input P1 ;
    eq_map_output : @output P0 -> @output P1
  }.

Class MultiParamsEqMap
 (B0 : BaseParams) (B1 : BaseParams) 
 (B : BaseParamsEqMap B0 B1)
 (P0 : MultiParams B0) (P1 : MultiParams B1)  :=
{
   eq_map_msg : @msg B0 P0 -> @msg B1 P1 ;
   eq_map_name : @name B0 P0 -> @name B1 P1 ;
   eq_map_name_inv : @name B1 P1 -> @name B0 P0 ;
   eq_map_name_inv_inverse : forall n, eq_map_name_inv (eq_map_name n) = n ;
   eq_map_name_inverse_inv : forall n, eq_map_name (eq_map_name_inv n) = n
}.

Section SimulOneToOne.

Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsEqMap base_fst base_snd}.
Context {multi_map : MultiParamsEqMap base_map multi_fst multi_snd}.

Definition eq_mapped_init_handlers n := 
  eq_map_data (init_handlers n).

Hypothesis eq_mapped_init_handlers_eq : forall n,
  eq_mapped_init_handlers n = init_handlers (eq_map_name n).

Definition eq_map_name_msgs :=
  map (fun nm => (eq_map_name (fst nm), eq_map_msg (snd nm))).

Definition eq_mapped_net_handlers me src m st :=
  let '(out, st', ps) := net_handlers me src m st in
  (map eq_map_output out, eq_map_data st', eq_map_name_msgs ps).

Hypothesis eq_net_handlers_eq : forall me src m st,
  eq_mapped_net_handlers me src m st = 
  net_handlers (eq_map_name me) (eq_map_name src) (eq_map_msg m) (eq_map_data st).

Definition eq_mapped_input_handlers me inp st :=
  let '(out, st', ps) := input_handlers me inp st in
  (map eq_map_output out, eq_map_data st', eq_map_name_msgs ps).

Hypothesis eq_input_handlers_eq : forall me inp st,
  eq_mapped_input_handlers me inp st = input_handlers (eq_map_name me) (eq_map_input inp) (eq_map_data st).

Definition eq_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) :=
match e with
| (n, inl io) => (eq_map_name n, inl (eq_map_input io))
| (n, inr lo) => (eq_map_name n, inr (map eq_map_output lo))
end.

Definition eq_map_packet (p : @packet base_fst multi_fst)  :=
match p with
| mkPacket src dst m =>
  mkPacket (eq_map_name src) (eq_map_name dst) (eq_map_msg m)
end.

Definition eq_map_net (net : @network _ multi_fst) : @network _ multi_snd :=
mkNetwork (map eq_map_packet net.(nwPackets)) (fun n => eq_map_data (net.(nwState) (eq_map_name_inv n))).

Lemma eq_map_update_eq :
  forall net d h,
    (fun n : name => eq_map_data (update (nwState net) h d (eq_map_name_inv n))) =
    update (fun n : name => eq_map_data (nwState net (eq_map_name_inv n))) (eq_map_name h) (eq_map_data d).
Proof.
move => net d h.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
  rewrite -H_dec in H_dec'.
  by rewrite eq_map_name_inverse_inv in H_dec'.
rewrite H_dec' in H_dec.
by rewrite eq_map_name_inv_inverse in H_dec.
Qed.

Corollary eq_map_update_packet_eq :
forall net p d,
  (fun n : name => eq_map_data (update (nwState net) (pDst p) d (eq_map_name_inv n))) =
  (update (fun n : name => eq_map_data (nwState net (eq_map_name_inv n))) (pDst (eq_map_packet p)) (eq_map_data d)).
Proof.
move => net. 
case => src dst m d.
exact: eq_map_update_eq.
Qed.

Lemma eq_map_packet_app_eq :
  forall l p ms ms',
    map eq_map_packet (map (fun m : name * msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l ++ ms ++ ms') = 
    map (fun m : name * msg => {| pSrc := pDst (eq_map_packet p); pDst := fst m; pBody := snd m |}) (eq_map_name_msgs l) ++ map eq_map_packet ms ++ map eq_map_packet ms'.
Proof.
move => l; case => src dst m ms ms'.
rewrite 2!map_app.
elim: l => //=.
case => /= n m' l IH.
by rewrite IH.
Qed.

Lemma eq_map_packet_eq :
  forall l l' h,
    map eq_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l ++ l') =
    map (fun m : name * msg => {| pSrc := eq_map_name h; pDst := fst m; pBody := snd m |}) (eq_map_name_msgs l) ++ map eq_map_packet l'.
Proof.
elim => //=.
case => n m l IH l' h.
by rewrite IH.
Qed.

Lemma init_handlers_fun_eq : 
    init_handlers = fun n : name => eq_map_data (init_handlers (eq_map_name_inv n)).
Proof.
apply functional_extensionality => n.
have H_eq := eq_mapped_init_handlers_eq.
rewrite /eq_mapped_init_handlers in H_eq.
rewrite H_eq {H_eq}.
by rewrite eq_map_name_inverse_inv.
Qed.

Theorem step_m_eq_mapped_simulation_1 :
  forall net net' tr,
    @step_m _ multi_fst net net' tr ->
    @step_m _ multi_snd (eq_map_net net) (eq_map_net net') (map eq_map_trace_occ tr).
Proof.
move => net net' tr.
case => {net net' tr}.
- move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
  rewrite /eq_map_trace_occ /=.
  have ->: eq_map_name (pDst p) = pDst (eq_map_packet p) by case: p H_eq H_hnd H_eq' => src dst m H_eq H_hnd H_eq'.
  apply (@SM_deliver _ _ _ _ _ (map eq_map_packet ms) (map eq_map_packet ms') (map eq_map_output out) (eq_map_data d) (eq_map_name_msgs l)).
  * by rewrite /eq_map_net /= H_eq /= map_app.
  * rewrite /=.
    case: p H_eq H_hnd H_eq' => /= src dst m H_eq H_hnd H_eq'.
    have H_q := eq_net_handlers_eq dst src m (nwState net dst).
    rewrite /eq_mapped_net_handlers in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite eq_map_name_inv_inverse.
  * rewrite /= H_eq' /= /eq_map_net /=.
    rewrite -eq_map_update_packet_eq.
    by rewrite eq_map_packet_app_eq.
- move => h net net' out inp d l H_hnd H_eq.
  apply (@SM_input _ _ _ _ _ _ _ (eq_map_data d) (eq_map_name_msgs l)).
    rewrite /=.
    have H_q := eq_input_handlers_eq h inp (nwState net h).
    rewrite /eq_mapped_input_handlers /= in H_q.
    rewrite H_hnd in H_q.
    rewrite H_q.
    by rewrite eq_map_name_inv_inverse.
  rewrite /= H_eq /= /eq_map_net /=.
  rewrite -eq_map_update_eq.
  by rewrite eq_map_packet_eq.
Qed.

Lemma map_eq_inv :
  forall (A B : Type) (f : A -> B) (l : list A) xs ys,
    map f l = xs ++ ys ->
    exists l1, exists l2, l = l1 ++ l2 /\ map f l1 = xs /\ map f l2 = ys.
Proof.
move => A B f.
elim => /=.
- case => //.
  case => //.
  move => H_eq.
  by exists []; exists [].
- move => a l IH.
  case => /=.
  * move => ys.
    rewrite /=.
    case: ys => //.
    move => b ys' H_eq.
    inversion H_eq.
    have IH' := IH [] ys'.
    rewrite /= in IH'.
    apply IH' in H1.
    move: H1 => [l1 [l2 [H_eq_l [H_eq_l1 H_eq_l2]]]].   
    exists ([]); exists (a :: l2).
    case: l1 H_eq_l H_eq_l1 => //= H_eq_l H_eq_l1.
    by rewrite /= H_eq_l H_eq_l2.    
  * move => b xs' ys H_eq.
    inversion H_eq.
    apply IH in H1.
    move: H1 => [l1 [l2 [H_eq_l [H_eq_l1 H_eq_l2]]]].
    exists (a :: l1); exists l2.
    rewrite /=.
    by rewrite H_eq_l H_eq_l1 H_eq_l2.
Qed.

Lemma eq_map_trace_occ_inv : 
  forall tr n ol,
    map eq_map_trace_occ tr = [(n, inr ol)] -> 
    exists n', exists lo, tr = [(n', inr lo)] /\ eq_map_name n' = n /\ map eq_map_output lo = ol.
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

Lemma map_eq_inv_eq :
  forall (A B : Type) (f : A -> B),
    (forall a a', f a = f a' -> a = a') ->
    forall l l', map f l = map f l' -> l = l'.
Proof.
move => A B f H_inj.
elim; first by case.
move => a l IH.
case => //=.
move => a' l' H_eq.
inversion H_eq.
have H_eq' := IH _ H1.
apply H_inj in H0.
by rewrite H0 H_eq'.
Qed.

Hypothesis eq_map_output_injective : 
  forall o o', eq_map_output o = eq_map_output o' -> o = o'.

Theorem step_m_eq_mapped_simulation_2 :
  forall net net' out mnet mout,
      @step_m _ multi_snd net net' out ->
      eq_map_net mnet = net ->
      map eq_map_trace_occ mout = out ->
      exists mnet',
        @step_m _ multi_fst mnet mnet' mout /\
        eq_map_net mnet' = net'.
Proof.
move => net net' out mnet mout H_step H_eq H_eq'.
invcs H_step.
- case: p H4 H H0 => /= src dst m H4 H H0.
  rewrite /eq_map_net /=.
  case: mnet H H0 => /= pks sts H_eq H_hnd.
  have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H_eq.
  case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
  rewrite H_eq_pks.
  inversion H_eq_pks2.
  case H_hnd': (net_handlers (pDst p) (pSrc p) (pBody p) (sts (pDst p))) => [dout l'].
  case: dout H_hnd' => out' d' H_hnd'.
  rewrite -H_eq_pks1.
  exists {| nwPackets := send_packets (pDst p) l' ++ pks1 ++ pks2 ; nwState := update sts (pDst p) d' |}.
  split.
  * have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := eq_map_trace_occ_inv _ (eq_sym H4).
    rewrite H_eq_mout.
    have H_eq_dst: n' = pDst p.
      rewrite -(eq_map_name_inv_inverse n').
      rewrite H_eq_n.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      rewrite /=.
      rewrite /= in H0.
      inversion H0.
      by rewrite eq_map_name_inv_inverse.
    rewrite H_eq_dst.
    apply (@SM_deliver _ _ _ _ _ pks1 pks2 _ d' l') => //=.
    suff H_suff: lo = out' by rewrite H_suff.
    have H_eq_hnd := eq_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /eq_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H2 H3 H5 in H_eq_hnd.
    rewrite -{1}H_eq_dst H_eq_n in H_eq_hnd.
    rewrite -H_eq_dst in H_eq_hnd.
    rewrite -(eq_map_name_inv_inverse n') H_eq_n in H_eq_hnd.
    move {Heqp1 Heqp0 H_hnd'}.
    have H_eq_src: eq_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
    have H_eq_body: eq_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_hnd.
      rewrite /=.
      rewrite /= in H0.
      by inversion H0.
    rewrite H_eq_body H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite -H_eq_lo in H6.
    symmetry.
    move: H6.
    apply map_eq_inv_eq.
    exact: eq_map_output_injective.
  * rewrite /=.
    rewrite /update /=.
    have H_eq_dst: eq_map_name (pDst p) = dst.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd'.
      by inversion H0.
    have H_eq_src: eq_map_name (pSrc p) = src.
      case: p H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst => src' dst' m' H_eq_pks H_eq_pks2 H0 H_hnd' H_eq_dst.
      by inversion H0.
    have H_eq_body: eq_map_msg (pBody p) = m.
      case: p H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd' => src' dst' m' H_eq_pks H_eq_pks2 H0 H_eq_dst H_eq_src H_hnd'.
      by inversion H0.
    rewrite 2!map_app.
    have H_eq_hnd := eq_net_handlers_eq (pDst p) (pSrc p) (pBody p) (sts (pDst p)).
    rewrite /eq_mapped_net_handlers /= in H_eq_hnd.
    repeat break_let.
    inversion H_hnd'.
    rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
    rewrite -{2}H_eq_dst eq_map_name_inv_inverse in H_hnd.
    rewrite H_hnd in H_eq_hnd.
    inversion H_eq_hnd.
    rewrite H2 in H6.
    rewrite H3 in H7.
    rewrite H5 in H8.
    rewrite H3 H5.
    set nwP1 := map eq_map_packet _.
    set nwP2 := map (fun _ => _) (eq_map_name_msgs _).
    set nwS1 := fun _ => _.
    set nwS2 := fun _ => _.
    have H_eq_nw: nwP1 = nwP2.
      rewrite /nwP1 /nwP2 {H_hnd' H5 H8 nwP1 nwP2}.
      elim: l' => //=.
      case => /= n' m' l' IH.
      rewrite IH.
      by rewrite H_eq_dst.
    rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
    have H_eq_sw: nwS1 = nwS2.
      rewrite /nwS1 /nwS2.
      apply functional_extensionality => n'.
      rewrite -H_eq_dst.
      case (name_eq_dec _ _) => H_dec.
        rewrite -H_dec.
        rewrite eq_map_name_inverse_inv.
        by case (name_eq_dec _ _).
      case (name_eq_dec _ _) => H_dec' //.
      rewrite H_dec' in H_dec.
      by rewrite eq_map_name_inv_inverse in H_dec.
    by rewrite H_eq_sw.
- rewrite /eq_map_net /=.      
  by admit.
Admitted.

Theorem step_m_eq_mapped_invariant_lift :
  forall P : _ -> Prop,
    (forall net net' out,
       @step_m _ multi_snd net net' out ->
       P net ->
       P net') ->
    (forall net net' out,
       @step_m _ multi_fst net net' out ->
       P (eq_map_net net) ->
       P (eq_map_net net')).
Proof. by move => P; eauto using step_m_eq_mapped_simulation_1. Qed.

Corollary step_m_mapped_simulation_star_1 :
  forall net tr,
    @step_m_star _ multi_fst step_m_init net tr ->
    @step_m_star _ multi_snd step_m_init (eq_map_net net) (map eq_map_trace_occ tr).
Proof.
move => net tr H_step.
remember step_m_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
  rewrite H_init.
  rewrite /step_m_init /= /eq_map_net /=.
  rewrite init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_m_eq_mapped_simulation_1 in H.
rewrite map_app.
have H_trans := refl_trans_1n_trace_trans IHH_step1.
apply: H_trans.
rewrite (app_nil_end (map _ _)).
apply: (@RT1nTStep _ _ _ _ (eq_map_net x'')) => //.
exact: RT1nTBase.
Qed.

Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.

Hypothesis eq_mapped_reboot_eq : forall d,
  eq_map_data (reboot d) = reboot (eq_map_data d).

Lemma not_in_failed_not_in :
  forall n failed,
    ~ In n failed ->
    ~ In (eq_map_name n) (map eq_map_name failed).
Proof.
move => n.
elim => //=.
move => n' failed IH H_in H_in'.
case: H_in' => H_in'.
  case: H_in.
  left.
  rewrite -(eq_map_name_inv_inverse n').
  rewrite H_in'.
  exact: eq_map_name_inv_inverse.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma in_failed_in :
  forall n failed,
    In n failed ->
    In (eq_map_name n) (map eq_map_name failed).
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

Lemma remove_eq_map_eq :
  forall h failed,
    map eq_map_name (remove name_eq_dec h failed) =
    remove name_eq_dec (eq_map_name h) (map eq_map_name failed).
Proof.
move => h.
elim => //=.
move => n failed IH.
case (name_eq_dec _ _) => H_eq; case (name_eq_dec _ _) => H_eq' //.
- by rewrite H_eq in H_eq'.
- rewrite -(eq_map_name_inv_inverse h) in H_eq.
  rewrite H_eq' in H_eq.
  by rewrite eq_map_name_inv_inverse in H_eq.
- by rewrite /= IH.
Qed.

Lemma eq_map_reboot_eq :
forall h net,
    (fun n : name => 
      eq_map_data 
        (match name_eq_dec (eq_map_name_inv n) h with
         | left _ => reboot (nwState net (eq_map_name_inv n))
         | right _ => nwState net (eq_map_name_inv n)
        end)) =
    (fun nm : name =>
       match name_eq_dec nm (eq_map_name h) with
       | left _ => reboot (eq_map_data (nwState net (eq_map_name_inv nm)))
       | right _ => eq_map_data (nwState net (eq_map_name_inv nm))
       end).
Proof.
move => h net.
apply: functional_extensionality => n.
case (name_eq_dec _ _) => H_dec; case (name_eq_dec _ _) => H_dec' //.
- rewrite -H_dec in H_dec'.
  by rewrite eq_map_name_inverse_inv in H_dec'.
- rewrite H_dec' in H_dec.
  by rewrite eq_map_name_inv_inverse in H_dec.
Qed.

Theorem step_f_eq_mapped_simulation_1 :
  forall net net' failed failed' tr,
    @step_f _ _ fail_fst (failed, net) (failed', net') tr ->
    @step_f _ _ fail_snd (map eq_map_name failed, eq_map_net net) (map eq_map_name failed', eq_map_net net') (map eq_map_trace_occ tr).
Proof.
move => net net' failed failed' tr H_step.
invcs H_step.
- have ->: eq_map_name (pDst p) = pDst (eq_map_packet p) by case: p H3 H4 H6 => src dst m.
  apply (@SF_deliver _ _ _ _ _ _ _ (map eq_map_packet xs) (map eq_map_packet ys) _ (eq_map_data d) (eq_map_name_msgs l)).
  * by rewrite /eq_map_net /= H3 /= map_app.
  * case: p H3 H4 H6 => /= src dst m H3 H4 H6.
    exact: not_in_failed_not_in.
  * case: p H3 H4 H6 => /= src dst m H3 H4 H6.        
    have H_q := eq_net_handlers_eq dst src m (nwState net dst).
    rewrite /eq_mapped_net_handlers in H_q.
    rewrite H6 in H_q.
    rewrite H_q.
    by rewrite eq_map_name_inv_inverse.
  * rewrite /= -eq_map_update_packet_eq /=.
    rewrite /eq_map_net /=.
    by rewrite eq_map_packet_app_eq.
- apply (@SF_input _ _ _ _ _ _ _ _ _ (eq_map_data d) (eq_map_name_msgs l)).
  * exact: not_in_failed_not_in.
  * rewrite /=.
    have H_q := eq_input_handlers_eq h inp (nwState net h).
    rewrite /eq_mapped_input_handlers /= in H_q.
    rewrite H5 in H_q.
    rewrite H_q.
    by rewrite eq_map_name_inv_inverse.
  * rewrite /= /eq_map_net /=.
    rewrite -eq_map_update_eq.
    by rewrite eq_map_packet_eq.
- apply (@SF_drop _ _ _ _ _ _ (eq_map_packet p) (map eq_map_packet xs) (map eq_map_packet ys)).
  * by rewrite /eq_map_net /= H4 map_app.
  * by rewrite /eq_map_net /= map_app.
- apply (@SF_dup _ _ _ _ _ _ (eq_map_packet p) (map eq_map_packet xs) (map eq_map_packet ys)).
  * by rewrite /eq_map_net /= H4 map_app.
  * by rewrite /eq_map_net /= map_app.
- exact: SF_fail.
- apply: (SF_reboot (eq_map_name h)).
  * exact: in_failed_in.
  * by rewrite remove_eq_map_eq.
  * rewrite /eq_map_net /=.
    by rewrite eq_map_reboot_eq.
Qed.

Theorem step_f_eq_mapped_invariant_lift :
  forall P : _ -> Prop,
    (forall net net' failed failed' out,
       @step_f _ _ fail_snd (failed, net) (failed', net') out ->
       P net ->
       P net') ->
    (forall net net' failed failed' out,
       @step_f _ _ fail_fst (failed, net) (failed', net') out ->
       P (eq_map_net net) ->
       P (eq_map_net net')).
Proof. by move => P; eauto using step_f_eq_mapped_simulation_1. Qed.

Corollary step_f_mapped_simulation_star_1 :
  forall net failed tr,
    @step_f_star _ _ fail_fst step_f_init (failed, net) tr ->
    @step_f_star _ _ fail_snd step_f_init (map eq_map_name failed, eq_map_net net) (map eq_map_trace_occ tr).
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
  rewrite /step_f_init /= /step_m_init /eq_map_net /=.
  rewrite init_handlers_fun_eq.
  exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_step2 H_step1.
case: x' H IHH_step1 H_step1 => failed' net'.
case: x'' H_step2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
apply step_f_eq_mapped_simulation_1 in H.
rewrite map_app.
have H_trans := refl_trans_1n_trace_trans IHH_step1.
apply: H_trans.
rewrite (app_nil_end (map eq_map_trace_occ _)).
apply (@RT1nTStep _ _ _ _ (map eq_map_name failed'', eq_map_net net'')) => //.
exact: RT1nTBase.
Qed.

End SimulOneToOne.

Section GhostVars.

Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {failure_params : FailureParams multi_params}.
Context {params : GhostFailureParams failure_params}.

Definition refined_net_handlers me src m st :=
  let '(out, st', ps) :=
      net_handlers me src m (snd st) in
  (out, (ghost_net_handlers me src m st, st'), ps).

Definition refined_input_handlers me inp st :=
  let '(out, st', ps) :=
      input_handlers me inp (snd st) in
  (out, (ghost_input_handlers me inp st, st'), ps).

Definition refined_reboot (st : ghost_data * data) :=
  (fst st , reboot (snd st)).

Definition refined_init_handlers (n : name) : ghost_data * data :=
  (ghost_init, init_handlers n).

Instance refined_base_params : BaseParams :=
  {
    data := (ghost_data * data)%type ;
    input := input ;
    output := output
  }.

Instance refined_multi_params : MultiParams _ :=
  {
    name := name ;
    msg := msg ;
    msg_eq_dec := msg_eq_dec ;
    name_eq_dec := name_eq_dec ;
    nodes := nodes ;
    all_names_nodes := all_names_nodes ;
    no_dup_nodes := no_dup_nodes ;
    init_handlers := refined_init_handlers;
    net_handlers := refined_net_handlers ;
    input_handlers := refined_input_handlers
  }.

Instance refined_failure_params : FailureParams _ :=
  {
    reboot := refined_reboot
  }.

Definition deghost_packet p :=
  @mkPacket _ multi_params
            (@pSrc _ refined_multi_params p)
            (pDst p)
            (pBody p).

Definition deghost (net : @network _ refined_multi_params) : (@network _ multi_params).
  refine (@mkNetwork _ multi_params

                     (map deghost_packet
                        (nwPackets net))
                     _
         ).
  intros.
  destruct net.
  concludes.
  destruct nwState. auto.
Defined.

Arguments deghost_packet /_.

Instance refined_base_params_eq_map : BaseParamsEqMap refined_base_params base_params :=
  {
    eq_map_data := snd ;
    eq_map_input := id ;
    eq_map_output := id
  }.

Instance refined_multi_params_eq_map : MultiParamsEqMap refined_base_params_eq_map refined_multi_params multi_params :=
  {
    eq_map_msg := id ;
    eq_map_name := id ;
    eq_map_name_inv := id ;
    eq_map_name_inv_inverse := fun n => eq_refl ;
    eq_map_name_inverse_inv := fun n => eq_refl
  }.

Lemma hyp_eq_mapped_init_handlers_eq : forall n,
  eq_mapped_init_handlers n = init_handlers (eq_map_name n).
Proof. by []. Qed.

Lemma map_fst_snd_id : 
  forall A B l, map (fun t : A * B => (fst t, snd t)) l = l.
Proof.
move => A B.
elim => //.
move => a l IH.
rewrite /= IH.
by case: a.
Qed.

Lemma hyp_eq_net_handlers_eq : 
  forall me src m st,
    eq_mapped_net_handlers me src m st = 
    net_handlers (eq_map_name me) (eq_map_name src) (eq_map_msg m) (eq_map_data st).
Proof.
move => me src m st.
rewrite /eq_mapped_net_handlers /= /refined_net_handlers /= /eq_map_name_msgs /= /id /=.
repeat break_let.
move {p0 Heqp1 p Heqp2}.
inversion Heqp; subst.
rewrite /=.
rewrite -/id.
rewrite map_id.
by rewrite map_fst_snd_id.
Qed.

Lemma hyp_eq_input_handlers_eq : forall me inp st,
  eq_mapped_input_handlers me inp st = input_handlers (eq_map_name me) (eq_map_input inp) (eq_map_data st).
Proof.
move => me inp st.
rewrite /eq_mapped_input_handlers /=.
repeat break_let.
rewrite map_id.
rewrite /refined_input_handlers in Heqp.
repeat break_let.
rewrite /id /= Heqp1.
inversion Heqp; subst.
rewrite /= /eq_map_name_msgs /= /id /=.
by rewrite map_fst_snd_id.
Qed.

Lemma hyp_eq_mapped_reboot_eq : forall d,
  eq_map_data (reboot d) = reboot (eq_map_data d).
Proof. by []. Qed.

Lemma map_id_tr :
forall out,
map (fun e : name * (input + list output) =>
                 let (n, s) := e in
                 match s with
                 | inl io => (n, inl io)
                 | inr lo => (n, inr (map id lo))
                 end) out = out.
elim => //.
move => tr l IH.
rewrite /= IH.
break_let.
case: s Heqp => //=.
move => out H_eq.
by rewrite map_id.
Qed.

Theorem ghost_simulation_1 :
  forall net net' failed failed' out,
    @step_f _ _ refined_failure_params (failed, net) (failed', net') out ->
    @step_f _ _ failure_params (failed, deghost net) (failed', deghost net') out.
Proof.
have H_sim := step_f_eq_mapped_simulation_1 hyp_eq_net_handlers_eq hyp_eq_input_handlers_eq hyp_eq_mapped_reboot_eq.
move => net net' failed failed' out H_step.
apply H_sim in H_step.
rewrite /eq_map_name /eq_map_net /= 2!map_id /id /= in H_step.
rewrite /eq_map_trace_occ /= /id /= in H_step.
rewrite /eq_map_packet /= /id /= in H_step.
rewrite /deghost /=.
rewrite -/id map_id_tr in H_step.
move: H_step.
set fp := fun p : packet => _.
set fp' := fun p : packet => _.
have H_eq: fp = fp' by rewrite /fp /fp'; apply functional_extensionality; case => /= src dst m.
rewrite H_eq {H_eq fp}.
set fs1 := fun n => _.
set fs2 := fun n => _.
set fs1' := fun n => _.
set fs2' := fun n => _.
have H_eq: fs1 = fs1' by rewrite /fs1 /fs1' {fs1 fs1'}; apply functional_extensionality => n; case: net.
rewrite H_eq {H_eq fs1}.
have H_eq: fs2 = fs2' by rewrite /fs2 /fs2' {fs2 fs2'}; apply functional_extensionality => n; case: net'.
by rewrite H_eq {H_eq fs2}.
Qed.



End GhostVars.

Section MsgGhostVars.
  Context {base_params : BaseParams}.
  Context {multi_params : MultiParams base_params}.
  Context {failure_params : FailureParams multi_params}.
  Context {params : MsgGhostFailureParams failure_params}.

Definition add_ghost_msg (me : name) (st : data) (ps : list (name * msg)) :
                                                    list (name * (ghost_msg * msg)) :=
  map (fun m => (fst m, (write_ghost_msg me st, snd m))) ps.

  Definition mgv_refined_net_handlers me src (m : ghost_msg * msg) st :=
    let '(out, st', ps) :=
        net_handlers me src (snd m) st in
    (out, st', add_ghost_msg me st' ps).

  Definition mgv_refined_input_handlers me inp st :=
    let '(out, st', ps) :=
        input_handlers me inp st in
    (out, st', add_ghost_msg me st' ps).

  Definition mgv_msg_eq_dec :
    forall x y : ghost_msg * msg, {x = y} + {x <> y}.
  Proof.
    intros.
    decide equality; auto using msg_eq_dec, ghost_msg_eq_dec.
  Qed.

  Instance mgv_refined_base_params : BaseParams :=
    {
      data := data ;
      input := input ;
      output := output
    }.

  Instance mgv_refined_multi_params : MultiParams _ :=
    {
      name := name ;
      msg := (ghost_msg * msg) ;
      msg_eq_dec := mgv_msg_eq_dec ;
      name_eq_dec := name_eq_dec ;
      nodes := nodes ;
      all_names_nodes := all_names_nodes ;
      no_dup_nodes := no_dup_nodes ;
      init_handlers := init_handlers;
      net_handlers := mgv_refined_net_handlers ;
      input_handlers := mgv_refined_input_handlers
    }.

  Instance mgv_refined_failure_params : FailureParams _ :=
    {
      reboot := (@reboot base_params multi_params failure_params)
    }.

  Definition mgv_deghost_packet p :=
    @mkPacket _ multi_params
              (@pSrc _ mgv_refined_multi_params p)
              (pDst p)
              (snd (pBody p)).

  Definition mgv_deghost (net : @network _ mgv_refined_multi_params) : (@network _ multi_params).
    refine (@mkNetwork _ multi_params
                       (map mgv_deghost_packet
                          (nwPackets net))
                       _
           ).
    intros.
    destruct net.
    concludes.
    auto.
  Defined.

  Arguments mgv_deghost_packet /_.

Instance mgv_refined_base_params_eq_map : BaseParamsEqMap mgv_refined_base_params base_params :=
  {
    eq_map_data := id ;
    eq_map_input := id ;
    eq_map_output := id
  }.

Instance mgv_refined_multi_params_eq_map : MultiParamsEqMap mgv_refined_base_params_eq_map mgv_refined_multi_params multi_params :=
  {
    eq_map_msg := snd ;
    eq_map_name := id ;
    eq_map_name_inv := id ;
    eq_map_name_inv_inverse := fun n => eq_refl ;
    eq_map_name_inverse_inv := fun n => eq_refl
  }.

Lemma mgv_hyp_eq_mapped_init_handlers_eq : forall n,
  eq_mapped_init_handlers n = init_handlers (eq_map_name n).
Proof. by []. Qed.

Lemma mgv_hyp_eq_net_handlers_eq : 
  forall me src m st,
    eq_mapped_net_handlers me src m st = 
    net_handlers (eq_map_name me) (eq_map_name src) (eq_map_msg m) (eq_map_data st).
Proof.
move => me src m st.
rewrite /eq_mapped_net_handlers /= /mgv_refined_net_handlers /= /eq_map_name_msgs /= /id /=.
repeat break_let.
rewrite -/id map_id.
inversion Heqp; subst.
move {Heqp0 Heqp}.
rewrite /add_ghost_msg /=.
elim: l0 => //.
case => n m' l IH.
rewrite /=.
injection IH; subst.
move => IH'.
by rewrite IH'.
Qed.

Lemma mgv_hyp_eq_input_handlers_eq : forall me inp st,
  eq_mapped_input_handlers me inp st = input_handlers (eq_map_name me) (eq_map_input inp) (eq_map_data st).
Proof.
move => me inp st.
rewrite /eq_mapped_input_handlers /=.
repeat break_let.
rewrite map_id /id /=.
rewrite /mgv_refined_input_handlers in Heqp.
repeat break_let.
inversion Heqp; subst.
rewrite /= /eq_map_name_msgs /= /id /=.
move {Heqp1 Heqp}.
elim: l1 => //.
case => n m l.
rewrite /=.
move => IH.
injection IH; subst.
move => IH'.
by rewrite IH'.
Qed.

Lemma mgv_hyp_eq_mapped_reboot_eq : forall d,
  eq_map_data (reboot d) = reboot (eq_map_data d).
Proof. by []. Qed.

Lemma mgv_map_id_tr :
forall out,
map (fun e : name * (input + list output) =>
                 let (n, s) := e in
                 match s with
                 | inl io => (n, inl io)
                 | inr lo => (n, inr (map id lo))
                 end) out = out.
elim => //.
move => tr l IH.
rewrite /= IH.
break_let.
case: s Heqp => //=.
move => out H_eq.
by rewrite map_id.
Qed.

Theorem mgv_ghost_simulation_1 :
  forall net net' failed failed' out,
    @step_f _ _ mgv_refined_failure_params (failed, net) (failed', net') out ->
    @step_f _ _ failure_params (failed, mgv_deghost net) (failed', mgv_deghost net') out.
Proof.
have H_sim := step_f_eq_mapped_simulation_1 mgv_hyp_eq_net_handlers_eq mgv_hyp_eq_input_handlers_eq mgv_hyp_eq_mapped_reboot_eq.
move => net net' failed failed' out H_step.
apply H_sim in H_step.
rewrite /eq_map_name /eq_map_net /= 2!map_id /id /= in H_step.
rewrite /eq_map_trace_occ /= /id /= in H_step.
rewrite /eq_map_packet /= /id /= in H_step.
rewrite /mgv_deghost /=.
rewrite -/id mgv_map_id_tr in H_step.
move: H_step.
set fp := fun p : packet => _.
set fp' := fun p : packet => _.
have H_eq: fp = fp' by rewrite /fp /fp'; apply functional_extensionality; case => /= src dst m.
rewrite H_eq {H_eq fp}.
set fs1 := fun n => _.
set fs2 := fun n => _.
set fs1' := fun n => _.
set fs2' := fun n => _.
have H_eq: fs1 = fs1' by rewrite /fs1 /fs1' {fs1 fs1'}; apply functional_extensionality => n; case: net.
rewrite H_eq {H_eq fs1}.
have H_eq: fs2 = fs2' by rewrite /fs2 /fs2' {fs2 fs2'}; apply functional_extensionality => n; case: net'.
by rewrite H_eq {H_eq fs2}.
Qed.

(*
Definition ghost_packet p :=
  @mkPacket _ refined_multi_params
            (@pSrc _ multi_params p)
            (pDst p)
            (pBody p).

Arguments ghost_packet /_.

Definition reghost (net : @network _ multi_params) : @network _ refined_multi_params.
  refine (@mkNetwork _ refined_multi_params
                     (map ghost_packet
                        (nwPackets net))
                     _
         ).
  intros.
  destruct net.
  concludes.
  exact (ghost_init, nwState).
Defined.

Lemma reghost_deghost_partial_inverses :
  forall net,
    deghost (reghost net) = net.
Proof.
  destruct net. unfold deghost, reghost. simpl in *. f_equal.
  rewrite map_map. map_id.
Qed.
*)
