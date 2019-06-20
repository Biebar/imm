From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import WWMM.

Section WWMM_seqcst.

Variable G : execution.
Hypothesis WF : Wf G.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'fr'" := G.(fr).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Definition sw := ⦗ Sc ⦘ ⨾ rf ⨾ ⦗ Sc ⦘.
Definition hb := (sb ∪ sw)⁺.

Definition seqcst (mo : relation actid) :=
  irreflexive (⦗W⦘ ⨾ mo ⨾ (rf ∩ mo)⁻¹ ⨾ (mo ∩ same_loc)).

Definition data_race_free (mo : relation actid) :=
  forall X Y,
    hb X Y \/ hb Y X \/
    (~(W X) /\ ~(W Y)) \/
    (same_loc Y X ->  Sc X /\ Sc Y).

(*Definition data_race_free (mo : relation actid) :=
  ~(exists X Y,
    ~(hb X Y \/ hb Y X) /\
    (W X \/ W Y) /\
    same_loc X Y /\
    (~(Sc X) \/ ~(Sc Y))).*)

(*Definition data_race_free (mo : relation actid) :=
  E×E \ hb \ hb⁻¹ \ W×W \ Sc×Sc ∩ same_loc ≡ ∅₂.*)
(*
  
*)

Lemma drf_mo :
  forall mo, data_race_free mo -> wwmm_consistent G mo -> strict_partial_order mo ->
    forall X Y,
    mo X Y -> W X \/ W Y -> same_loc X Y ->
    hb X Y \/ (Sc X /\ Sc Y).
Proof.
  intros.
  destruct (H X Y) as [hbXY | [hbYX | [[nWX nWY] | Hsc]]]; auto.
  - exfalso.
    destruct H0 as [_ [H0 _]].
    destruct H1 as [irrefl trans].
    unfolder in irrefl.
    apply irrefl with X.
    apply trans with Y; try assumption.
    apply H0.
    assumption.
  - exfalso. destruct H3; auto.
  - right.
    apply Hsc.
    apply same_loc_sym.
    assumption.
Qed.

Lemma rf_r :
  forall X Y, rf Y X -> R X.
Proof.
  intros.
  apply wf_rfD in H; auto.
  unfolder in H.
  destruct H as [_ [_ RX]].
  assumption.
Qed.

Lemma rf_w :
  forall X Y, rf Y X -> W Y.
Proof.
  intros.
  apply wf_rfD in H; auto.
  unfolder in H.
  destruct H.
  assumption.
Qed.

Theorem sc_drf :
  forall mo, strict_partial_order mo ->
             wwmm_consistent G mo ->
             data_race_free mo ->
             seqcst mo.
Proof with
repeat (eexists; split; eauto);
try eapply rf_r; try eapply rf_w; eassumption.

  intros mo strict cst drf Z H.
  unfolder in H.
  destruct H as [WZ [X [moZX [Y [[rfYX moYX] [moYZ slYZ]]]]]].
  assert (hb Y Z \/ (Sc Y /\ Sc Z)) as drfYZ. {
    apply drf_mo with mo; auto.
  }
  assert (hb Z X \/ (Sc Z /\ Sc X)) as drfZX. {
    apply drf_mo with mo; auto.
    apply same_loc_trans with Y.
    apply same_loc_sym. assumption.
    apply wf_rfl; auto.
  }
  assert (hb Y X \/ (Sc Y /\ Sc X)) as drfYX. {
    apply drf_mo with mo; auto.
    - left. eapply rf_w. eauto.
    - apply wf_rfl; auto.
  }
  destruct drfYZ as [hbYZ | [ScY ScZ]];
  destruct drfZX as [hbZX | [ScZ' ScX]];
  destruct cst as [_[_[_[Chbrfhb [Cirr1 [Cirr2 Cirr3]]]]]];
  unfold NW, irreflexive in Chbrfhb, Cirr1, Cirr2, Cirr3;
  unfolder in Chbrfhb;
  unfolder in Cirr1;
  unfolder in Cirr2;
  unfolder in Cirr3.
  - eapply Chbrfhb...
  - destruct drfYX as [hbYX | [ScY _]].
    + eapply Cirr3...
    + eapply Cirr1...
  - destruct drfYX as [hbYX | [_ ScX]].
    + eapply Cirr2...
    + eapply Cirr1...
  - eapply Cirr1...
Qed.

  

End WWMM_seqcst.