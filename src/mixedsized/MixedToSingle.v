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

Lemma set_from_list_cons {A} l (x : A) :
  set_from_list (x::l) ≡₁ (fun y => x=y) ∪₁ (set_from_list l).
Proof.
  unfold set_from_list.
  simpl.
  split; intros y H.
  - destruct H.
    + left. assumption.
    + right. assumption.
  - destruct H.
    + left. assumption.
    + right. assumption.
Qed.

Lemma set_from_list_app {A} (l l' : list A) :
  set_from_list (l++l') ≡₁ (set_from_list l) ∪₁ (set_from_list l').
Proof.
  induction l as [|x t].
  - split; intros x H.
    + right.
      assumption.
    + destruct H; auto. contradiction.
  - simpl.
    repeat rewrite set_from_list_cons.
    rewrite IHt. rewrite set_unionA.
    reflexivity.
Qed.

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

Definition set_image {A B} (R:A->B->Prop) S y :=
  exists x, S x /\ R x y.


Lemma map {A B} l (R : A -> B -> Prop) :
  (forall x, In x l -> is_finite_set (R x)) -> 
  exists l', forall y, In y l' <-> exists x, In x l /\ R x y.
Proof.
  intro finite.
  induction l.
  - exists nil.
    intro.
    split;
    intro H;
    repeat destruct H.
  - destruct (finite a) as [h' [it'1 it'2]]; try left; auto.
    destruct IHl as [t' eql'].
    { intros. apply finite. right. assumption. }
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

Lemma finite_map {A B} S (R : A -> B -> Prop) :
  is_finite_set S ->
  (forall x, S x -> is_finite_set (R x)) ->
  is_finite_set (set_image R S).
Proof.
  intros [l finitel] finiteImage.
  assert (forall x, In x l -> is_finite_set (R x)). {
    intros.
    apply finiteImage.
    apply (proj2 finitel).
    apply H.
  }
  apply map in H.
  destruct H as [l' eq].
  exists l'.
  split; intros y H.
  - apply (proj2 (eq y)).
    destruct H as [x [H1 H2]].
    exists x. 
    split;
    try apply (proj1 finitel);
    assumption.
  - apply (proj1 (eq y)) in H.
    destruct H as [x [H1 H2]].
    exists x.
    split;
    try apply (proj2 finitel);
    assumption.
Qed.

Definition mixed2single_event exec threadid mev sev :=
  IF init exec mev
  then
    exists loc ev, 
      in_dom loc mev /\ sev = InitEvent (BinPos.Pos.of_nat loc) /\
      EV exec ev /\ ~(init exec ev) /\ starts_at loc ev
  else IF is_rmw mev
  then
    sev = ThreadEvent (threadid mev) (2 * (index mev)) \/ (* rmw events get *)
    sev = ThreadEvent (threadid mev) (2 * (index mev) + 1) (* to two event *)
  else
    sev = ThreadEvent (threadid mev) (2 * (index mev)).

Record event_description := {
  init : bool;
  read : bool;
  write : bool;
  sc : bool;
  loc : location;
  value_r : value;
  value_w : value;
  id : nat;
}.

Record inj_nat_list__nat := {
  nln_func : list nat -> nat;
  nln_inj : forall x y, nln_func x = nln_func y -> x = y;
}.
Lemma nat_nat_star_bij : inj_nat_list__nat.
(*
  f(x1...xn) = Product_{i=1...n} pi^{xi+1}
  with pi the i-th prime number.
*)
Admitted.

Definition vallist2val := nln_func nat_nat_star_bij.

Definition mixed2descr exec mev descr :=
  let n := BinPos.Pos.to_nat (loc descr) in
  (MixedBasic.init exec mev <-> init descr = true) /\
  (is_read mev <-> read descr = true) /\ 
  (is_write mev <-> write descr = true) /\
  (is_sc mev <-> sc descr = true) /\
  (IF MixedBasic.init exec mev then
    in_dom n mev /\
    exists mev', EV exec mev' /\ ~(MixedBasic.init exec mev') /\ starts_at n mev'
   else
    starts_at n mev) /\
  True (*todo*).


Definition descr_to_mode descr :=
  match sc descr with
  | true => Osc
  | false => Orlx
  end.

Fixpoint mklabel levdescr sev :=
  let rec := mklabel in
  match levdescr with
  | nil => Afence Opln
  | descr::tail =>
    if is_init sev then
      if init descr then
        Astore Xpln Orlx (loc descr) (value_w descr)
      else
        mklabel tail sev
    else if Nat.eqb (Nat.div (Events.index sev) 2) (id descr) then
        if read descr && write descr then
          if Nat.even (Events.index sev) then
            Aload true (descr_to_mode descr) (loc descr) (value_r descr)
          else
            Astore Xpln (descr_to_mode descr) (loc descr) (value_w descr)
        else if read descr then
          Aload true (descr_to_mode descr) (loc descr) (value_r descr)
        else
          Astore Xpln (descr_to_mode descr) (loc descr) (value_w descr)
    else
        mklabel tail sev
      
  end.

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
  (*todo*)
Admitted.

End MixedToSingle.