Require Import Coq.Setoids.Setoid.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import WWMM.
Require Import MixedBasic.
Require Import MixedRfb.

Section MixedToSingle.

Definition set_from_list {A} l (x:A) :=
  In x l.

Definition is_finite_set {A} (S:A->Prop) :=
  exists l, S ≡₁ (set_from_list l).

Definition finite_events exec :=
  is_finite_set (EV exec).

Lemma select {A} (l:list A) S :
  exists l', (set_from_list l) ∩₁ S ≡₁ (set_from_list l').
Proof.
  induction l.
  - exists nil.
    split; intros x H.
    + destruct H.
      contradiction.
    + contradiction.
  - destruct IHl as [t' [H1 H2]].
    destruct (excluded_middle (S a)) as [Pa | nPa].
    + exists (a::t').
      split; intros x H.
      * destruct H.
        destruct H; simpl.
        -- left. assumption.
        -- right.
           apply H1.
           split; assumption.
      * destruct H.
        -- split.
           ++ left. assumption.
           ++ rewrite <- H. assumption.
        -- split; apply H2 in H; destruct H.
           ++ right.
              assumption.
           ++ assumption.
    + exists t'.
      split; intros x H.
      * destruct H as [[eq | xinl] Px]; simpl.
        -- subst. contradiction.
        -- intuition.
      * apply H2 in H.
        destruct H.
        split.
        -- right. assumption.
        -- assumption.
Qed.

Lemma map {A B} l (R : A -> B -> Prop) :
  (forall x, is_finite_set (R x)) -> 
  exists l', forall y, In y l' <-> exists x, In x l /\ R x y.
Proof.
  intro finite.
  induction l.
  - exists nil.
    intro.
    split;
    intro H;
    repeat destruct H.
  - destruct (finite a) as [h' [it'1 it'2]].
    clear finite.
    destruct IHl as [t' eql'].
    exists (h'++t').
    intro y.
    rewrite in_app_iff.
    simpl.
    split; intro H.
    + destruct H.
      * apply it'2 in H.
        exists a.
        split; auto.
      * rewrite eql' in H.
        destruct H as [x [H H1]].
        exists x.
        split; auto.
    + destruct H as [x [[eq | inxl] Rxy]].
      * subst.
        left. apply it'1. assumption.
      * right. rewrite eql'.
        exists x.
        split; assumption.
Qed.

Fixpoint transform_ev_list l := match l with
  | h::t => 

Theorem unisized_equivalence :
  forall exec,
  well_formed exec ->
  finite_events exec ->
  unisized exec ->
  exists exec' mo,
    Wf exec' /\
    (consistent exec <-> wwmm_consistent exec' mo).
Proof.
  intros exec wf [l eql] uni.

(*
Definition nooverlap_exec exec :=
  EV exec ⊆₁ aligned /\ EV exec × EV exec ∩ overlap ⊆ ∅₂.

Definition event_starts_at l e :=
  exists size, ev_dom e ≡₁ range l size.

Definition threadid := MixedEvent -> nat.

Definition wf_threadid exec (thid : threadid) :=
  forall e e', EV exec e -> EV exec e' ->
    thid e = thid e' <-> sthd exec e e'.

Definition is_finite exec :=
  exists l, forall e, EV exec e <-> In e l.

Fixpoint list_range n size := match size with
  | 0 => nil
  | S size' => n::(list_range (S n) size')
  end.

Definition or_else {A} (x:A) o := match o with
  | Some y => y
  | None => x
  end.

Definition comp {A} {B} {C} (g:B->C) (f:A->B) x :=
  g (f x).

Record evtoev_trans exec := {
  tev : MixedEvent -> actid -> Prop;
  tlab : actid -> label;
  tval : list nat -> nat;
  wf_tev : forall e, EV exec e -> exists f, tev e f;
  wf_thid : forall e e' f f', EV exec e -> EV exec e' ->
              tev e f -> tev e' f' ->
              tid f' = tid f' -> sthd exec e e';
  wf_index : forall e e' f f', EV exec e -> EV exec e' ->
              tev e f -> tev e' f' ->
              index f = index f' -> MixedBasic.index e = MixedBasic.index e';
  wf_init : forall e f, EV exec e -> tev e f -> is_init f -> init exec e;
  wf_labr : forall e f, EV exec e -> tev e f -> 
              is_r tlab f = true -> is_read e;
  wf_labw : forall e f, EV exec e -> tev e f ->
              is_w tlab f = true -> is_write e;
  wf_labsc : forall e f, EV exec e -> tev e f ->
              is_sc tlab f = true -> MixedBasic.is_sc e;
  wf_rval : forall e f n size, EV exec e -> tev e f ->
            is_r tlab f = true ->
            ev_dom e ≡₁ range n size ->
            or_else 0 (val tlab f) = tval (map (comp (or_else 0) (rvals e)) (list_range n size));
  wf_wval : forall e f n size, EV exec e -> tev e f ->
            is_w tlab f = true ->
            ev_dom e ≡₁ range n size ->
            or_else 0 (val tlab f) = tval (map (comp (or_else 0) (wvals e)) (list_range n size));
  wf_sc : forall e f, EV exec e -> tev e f ->
            is_sc tlab f <-> MixedBasic.is_sc e;
}.

Record extoex_trans := {
  mexec : MExec;
  exec : execution;
  trans : evtoev_trans mexec;
}.



(*
  goal : forall exec, aligned_and_no_overlap exec ->
                      well_formed exec ->
                      exists exec_single_location,
                      well_formed exec_single_location /\
                      coherent exec exec_single_location.
*)
*)

End MixedToSingle.