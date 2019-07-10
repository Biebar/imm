Require Import Coq.Setoids.Setoid.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import WWMM.
Require Import MixedBasic.
Require Import MixedRfb.

Section MixedToSingle.

Definition is_readb mev :=
  match rvals mev with
  | nil => false
  | _ => true
  end.

Definition is_writeb mev :=
  match wvals mev with
  | nil => false
  | _ => true
  end.

Definition is_rmwb mev :=
  is_readb mev && is_writeb mev.

Definition is_initb mexec mev :=
  match IW mexec with
  | None => false
  | Some mev' => mev_eqb mev mev'
  end.

Definition get_size mev :=
  Nat.max (List.length (rvals mev)) (List.length (wvals mev)).

Fixpoint get_loc_list start (vallist:list val_t) :=
  match vallist with
  | nil => nil
  | h::t => (BinPos.Pos.of_nat start)::(get_loc_list (S start) t)
  end.

Definition get_all_loc:=
  List.map (Basics.compose BinPos.Pos.of_nat location).

Fixpoint find_loc_size mevlist' loc :=
  match mevlist' with
  | nil => 0
  | mev::tail =>
    if PeanoNat.Nat.eq_dec (location mev) loc then
      get_size mev
    else
      find_loc_size tail loc
  end.


Definition remove_opt list opt :=
  match opt with
  | None => list
  | Some x => List.remove mev_eq_dec x list
  end.

Definition remove_init exec mevlist :=
  remove_opt mevlist (IW exec).

Definition m2s_event mexec mevlist thid mev :=
  match is_initb mexec mev with
  | true => List.map (fun l => InitEvent l) (get_all_loc (remove_init mexec mevlist))
  | false =>
    match is_rmwb mev with
    | true => (ThreadEvent (thid mev) (2*(index mev)))::
              (ThreadEvent (thid mev) (2*(index mev)+1))::nil
    | false => (ThreadEvent (thid mev) (2*(index mev)))::nil
    end
  end.

Definition garbage_label := Afence Opln.

FixPoint m2s_lab mexec mevlist thid sev :=
  match sev with
  | InitEvent l =>
    match IW mexec with
    | Some mev =>
      match get_val (location mev) (wvals mev) l with
      | Some val => Astore Xpln Orlx l val
      | None => garbage_label
      end
    | None => garbage_label
    end
  | ThreadEvent thread id =>
    match mevlist with
    | nil => garbage_label
    | mev::tail =>
      if PeanoNat.Nat.eq_dec id (2*(index mev)) then
        if is_rmwb mev then
          Aload true Orlx (location mev) (

Theorem m2s :
  forall mexec mevlist thid,
  well_formed mexec ->
  EV mexec ≡₁ set_from_list mevlist ->
  consistent_thid mexec thid ->
  (consistent mexec
  <-> wwmm_consistent (m2s_exec mexec mevlist thid) (m2s_mo mexec mevlist thid)).

(*
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


Lemma map_rel {A B} l (R : A -> B -> Prop) :
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

Lemma finite_map_rel {A B} S (R : A -> B -> Prop) :
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
  apply map_rel in H.
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

Fixpoint extract_vallist {T} (vals:nat->T) n size :=
  match size with
  | 0 => nil
  | S size' => (vals n) :: (extract_vallist vals (S n) size')
  end.

Definition is_val_list list vals :=
  exists n size, vals_dom vals ≡₁ range n size /\ map Some list = extract_vallist vals n size.

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
  (is_read mev -> exists list, 
    value_r descr = vallist2val list /\ is_val_list list (rvals mev)) /\
  (is_write mev -> exists list,
    value_w descr = vallist2val list /\ is_val_list list (wvals mev)) /\
  (index mev = id descr).

Definition mixed2loc exec mev n :=
  ~MixedBasic.init exec mev /\ starts_at n mev.

Lemma finite_mixed2loc exec mev :
  well_formed exec -> EV exec mev ->
  is_finite_set (mixed2loc exec mev).
Proof.
  intros wf ev.
  destruct (excluded_middle (MixedBasic.init exec mev)).
  - exists nil.
    split;
    intros x H1;
    destruct H1;
    contradiction.
  - split; try assumption. 

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

Lemma finite_mixed2descr exec mev :
  is_finite_set (mixed2descr exec mev).
Proof.
  destruct (excluded_middle (MixedBasic.init exec mev)).
  - 

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
*)
End MixedToSingle.