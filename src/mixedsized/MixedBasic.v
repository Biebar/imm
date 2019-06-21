From hahn Require Import Hahn.
From Coq Require Import Arith.
From promising Require Import Basic Event.
Require Import Events.

Section MixedBasic.

Notation "a ²" := (a × a) (at level 1, format "a ²").

Definition val_t := value.
Definition loc_t := nat.

Record MixedEvent := {
  rvals : loc_t -> option val_t;
  wvals : loc_t -> option val_t;
  scevent : bool;
  index : nat;
}.

Definition vals_dom (vals: loc_t -> option val_t) n := match vals n with
  | None => False
  | Some _ => True
  end.

Definition rvals_dom e := vals_dom (rvals e).
Definition wvals_dom e := vals_dom (wvals e).

Definition ev_dom e :=
  rvals_dom e ∪₁ wvals_dom e.

Definition in_dom n e := ev_dom e n.

Definition range a b c :=
  a <= c /\ c < a + b.

Definition overlap e e' :=
  exists n, ev_dom e n /\ ev_dom e' n.

Definition nooverlap e e' :=
  ev_dom e ∩₁ ev_dom e' ⊆₁ ∅.

Definition size_n n e :=
  exists a, ev_dom e ≡₁ range a n.

Definition aligned_n n e :=
  exists a, ev_dom e ≡₁ range a n /\ a mod n = 0.

Definition aligned e :=
  aligned_n 1 e \/ aligned_n 2 e \/ aligned_n 4 e.

Definition starts_at n ev :=
  exists size, ev_dom ev ≡₁ range n size.

Definition wf_event e :=
  forall n n',
  rvals_dom e n ->
  wvals_dom e n' ->
  rvals_dom e ≡₁ wvals_dom e.

Record MExec := {
  EV : MixedEvent -> Prop;
  IW : option MixedEvent;
  sb : MixedEvent -> MixedEvent -> Prop;
  rfb : nat -> MixedEvent -> MixedEvent -> Prop;
  tot : MixedEvent -> MixedEvent -> Prop;
}.

Definition is_rmw e := rvals_dom e ≡₁ wvals_dom e.
Definition is_read e := wvals_dom e ⊆₁ ∅ \/ is_rmw e.
Definition is_write e := rvals_dom e ⊆₁ ∅ \/ is_rmw e.
Definition is_sc e := scevent e = true.

Definition writes exec :=
  EV exec ∩₁ is_write.

Definition reads exec :=
  EV exec ∩₁ is_read.

Definition sc exec :=
  EV exec ∩₁ is_sc.

Definition same_loc e e' :=
  ev_dom e ≡₁ ev_dom e'.

Definition same_val_wr n e e' :=
  wvals e n = rvals e' n.

Definition init exec e := match IW exec with
  | None => False
  | Some e' => e = e'
end.

Definition sthd exec :=
  (sb exec)＊ ∪ (sb exec)＊⁻¹.

Definition rf exec :=
  ⋃ n , rfb exec n.

Definition sw e :=
  rf e ∩ ( (⦗sc e⦘ ∩ same_loc) ∪ ((sc e × init e)∩(fun x y => forall z, sc e x /\ rf e x y -> y = z))).

Definition hb e :=
  (sb e ∪ sw e ∪ init e × EV e)⁺.

Definition tearfree e :=
  aligned ∩₁ (EV e) ∪₁ init e.

Lemma sw_hb e :
  sw e ⊆ hb e.
Proof.
  do 2 eapply inclusion_trans.
  apply inclusion_union_r2. 
  apply inclusion_union_r1.
  apply ct_step.
  apply inclusion_refl.
Qed.

Lemma same_loc_sym :
  forall X Y, same_loc X Y -> same_loc Y X.
Proof.
  intros X Y [H1 H2].
  split; assumption.
Qed.


Record well_formed exec := {
  wf_ev : forall e, EV exec e -> wf_event e;
  wf_index : forall e e', EV exec e -> EV exec e' -> index e = index e' -> e = e';
  wf_iww : init exec ⊆₁ writes exec \₁ reads exec;
  wf_iwn : forall e n, init exec e -> ev_dom e n;
  wf_iwsc : init exec ∩₁ sc exec ⊆₁ ∅;
  wf_rfb_func : forall n, functional (rfb exec n)⁻¹;
  wf_rfb_val : forall n, rfb exec n ⊆ same_val_wr n;
  wf_rfb_dom : forall n, rfb exec n ⊆ in_dom n × in_dom n;
  wf_rfb_wr : forall n, rfb exec n ≡ ⦗writes exec⦘ ⨾ (rfb exec n) ⨾ ⦗reads exec⦘;
  wf_loc_size : (EV exec\₁init exec) ⊆₁ size_n 1 ∪₁ size_n 2 ∪₁ size_n 4;
  wf_sb : strict_partial_order (sb exec);
  wf_rmw_sc : writes exec ∩₁ reads exec ⊆₁ sc exec;
  wf_sc_align : sc exec ⊆₁ aligned;
  wf_tot : strict_total_order (EV exec) (tot exec);
}.

Record consistent_sc_unfixed exec := {
  cst_hb_tot : (hb exec) ⊆ (tot exec);
  cst_rf_tf : functional ((rf exec) ∩ ((tearfree exec)×(tearfree exec)) ∩ same_loc)⁻¹;
  cst_rf_hb : irreflexive ((hb exec) ⨾ (rf exec)⁻¹);
  cst_rf_hb_hb : forall n, irreflexive (⦗writes exec⦘ ⨾ (hb exec) ⨾
                           (rfb exec n)⁻¹ ⨾ (hb exec) ⨾ ⦗in_dom n⦘);
  cst_sw_tot : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
               (tot exec ∩ same_loc) ⨾ (sw exec)⁻¹ ⨾ (tot exec));
}.

Record consistent exec := {
  cst_ufxd : consistent_sc_unfixed exec;
  cst_dagger : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
               (hb exec) ⨾ (rf exec ∩ (hb exec))⁻¹ ⨾
               ⦗sc exec⦘ ⨾ (tot exec ∩ same_loc));
  cst_ddagger : irreflexive (⦗writes exec ∩₁ (sc exec)⦘ ⨾
                (tot exec ∩ same_loc) ⨾ ⦗sc exec⦘ ⨾ 
                (rf exec ∩ (hb exec))⁻¹ ⨾ (hb exec));
}.

Definition data_race_free e :=
  forall X Y,
    hb e X Y \/ hb e Y X \/
    (~(writes e X) /\ ~(writes e Y)) \/
    nooverlap X Y \/
    (same_loc Y X /\ sc e X /\ sc e Y).

Definition seqcst e :=
  forall n, irreflexive (⦗writes e ∩₁ in_dom n⦘ ⨾ (tot e) ⨾ (rfb e n)⁻¹ ⨾ (tot e)).


Lemma rf__overlap exec :
  well_formed exec ->
  rf exec ⊆ overlap.
Proof.
  intros wf X Y [b [_ rfbXY]].
  eexists.
  eapply wf_rfb_dom; eauto.
Qed.

Lemma rf__ev exec :
  well_formed exec ->
  rf exec ⊆ (EV exec)².
Proof.
  intros wf X Y [b [_ H]].
  destruct (wf_rfb_wr exec wf b) as [H1 _].
  apply H1 in H.
  unfolder in H.
  destruct H as [[EVX _] [_ [EVY _]]].
  split; assumption.
Qed.

End MixedBasic.