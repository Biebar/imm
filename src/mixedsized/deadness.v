From hahn Require Import Hahn.
Require Import MixedBasic.

Section deadness.
Set Implicit Arguments.

Record dead e := {
  dead_hb_tot : (hb e) ⊆ (tot e);
  dead_WRsc : ⦗writes e⦘ ⨾ (tot e) ⨾ ⦗reads e ∩₁ (sc e)⦘ ⊆ (hb e);
  dead_WscW : ⦗writes e ∩₁ (sc e)⦘ ⨾ (tot e) ⨾ ⦗writes e⦘ ⊆ (hb e);
}.

Definition differ_by_tot e e' :=
  EV e = EV e' /\
  IW e = IW e' /\
  sb e = sb e' /\
  rfb e = rfb e'.

Lemma dvt_w :
  forall e e', differ_by_tot e e' -> writes e = writes e'.
Proof.
  intros e e'[eqE _].
  unfold writes.
  rewrite eqE.
  reflexivity.
Qed.

Lemma dbt_rf :
  forall e e', differ_by_tot e e' -> rf e = rf e'.
Proof.
  intros e e' [eqE [eqIW [eqsb eqrfb]]].
  unfold rf.
  rewrite eqrfb.
  reflexivity.
Qed.

Lemma dbt_init :
  forall e e', differ_by_tot e e' -> init e = init e'.
Proof.
  intros e e' [eqE [eqIW [eqsb eqrfb]]].
  unfold init.
  rewrite eqIW.
  reflexivity.
Qed.

Lemma dbt_sw :
  forall e e', differ_by_tot e e' -> sw e = sw e'.
Proof.
  intros e e' dbt.
  unfold sw.
  rewrite (dbt_rf dbt).
  rewrite dbt_init with e e'; try assumption.
  destruct dbt as [eqE [eqIW [eqsb eqrfb]]].
  replace (sc e) with (sc e').
  reflexivity.
  unfold sc.
  rewrite eqE.
  reflexivity.
Qed.


Lemma dbt_hb :
  forall e e', differ_by_tot e e' -> hb e = hb e'.
Proof.
  intros e e' dbt.
  unfold hb.
  rewrite dbt_init with e e'; auto.
  rewrite dbt_sw with e e'; auto.
  destruct dbt as [eqE [eqIW [eqsb eqrfb]]].
  rewrite eqE.
  rewrite eqsb.
  reflexivity.
Qed.

Lemma rfb_w_dom :
  forall e X Y n, well_formed e -> rfb e n Y X -> ev_dom Y n.
Proof.
  intros e X Y n H rfbnYX.
  apply wf_rfb_dom in rfbnYX; try assumption.
  destruct rfbnYX.
  assumption.
Qed.

Lemma drf_totWovrlp :
  forall e e' X Y n,
  well_formed e -> well_formed e' ->
  differ_by_tot e e' ->
  data_race_free e -> dead e ->
  in_dom n X -> in_dom n Y ->
  writes e X \/ writes e Y ->
  tot e X Y ->
  hb e' X Y \/ (same_loc X Y /\ sc e X /\ sc e Y).
Proof.
  intros e e' X Y n wfe wfe' dbt drfe deade domnX domnY WXoY totXY.
  destruct (drfe X Y) as [hbXY|[hbZY|[[nWX nWZ]|[novrlpXY|[slXY[scX scY]]]]]].
  - left.
    rewrite <- dbt_hb with e e';
    assumption.
  - exfalso.
    destruct (wf_tot e wfe) as [[irrefl trans] _].
    apply irrefl with Y.
    apply trans with X; try assumption.
    apply dead_hb_tot; assumption.
  - exfalso. destruct WXoY; auto.
  - exfalso.
    apply novrlpXY with n.
    split; assumption.
  - right.
    split; auto.
    apply same_loc_sym; auto.
Qed.

Theorem dead_is_interesting :
  forall e e',
  well_formed e -> well_formed e' ->
  differ_by_tot e e' ->
  data_race_free e ->
  dead e ->
  hb e' ⊆ tot e' ->
  seqcst e' -> seqcst e.
Proof.
  intros e e' WFe WFe' ee'tot drfe deade hbtot' sce' n Z H.
  unfolder in H.
  destruct H as [[WZ Zwn] [X [totZX [Y [rfbnYX totYZ]]]]].
  assert (tot e' Y Z). {
    destruct drf_totWovrlp with e e' Y Z n as [hbYZ | [slYZ [scY scZ]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply hbtot'.
      rewrite <- dbt_hb with e e'; try assumption.
      apply dead_WscW; try assumption.
      unfolder.
      split; split; auto.
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX.
      assumption.
  }
  assert (tot e' Z X). {
    destruct drf_totWovrlp with e e' Z X n as [hbZX | [slZX [scZ scX]]];
    auto.
    - apply wf_rfb_dom in rfbnYX; try assumption.
      destruct rfbnYX.
      assumption.
    - apply hbtot'.
      rewrite <- dbt_hb with e e'; try assumption.
      apply dead_WRsc; try assumption.
      unfolder.
      do 3 (split; try assumption).
      apply wf_rfb_wr in rfbnYX; try assumption.
      unfolder in rfbnYX.
      destruct rfbnYX as [_[_ RX]].
      assumption.
  }
  unfold seqcst, irreflexive in sce'.
  apply sce' with n Z.
  unfolder.
  split.
  - split; try assumption.
    rewrite <- dvt_w with e e';
    assumption.
  - repeat (eexists; split; eauto).
    destruct ee'tot as [eqE [eqIW [eqsb eqrfb]]].
    rewrite <- eqrfb.
    assumption.
Qed.

End deadness.
