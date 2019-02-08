(******************************************************************************)
(** * Weakening redundant SC accesses in IMM *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Dom.
Require Import Events Execution Execution_eco.
Require Import imm_common imm_hb imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Sc_opt.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'coi'" := G.(coi).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'detour'" := G.(detour).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).
Notation "'rs'" := G.(rs).
Notation "'hb'" := G.(hb).
Notation "'ppo'" := G.(ppo).
Notation "'psc'" := G.(psc).
Notation "'psc_base'" := G.(psc_base).
Notation "'bob'" := G.(bob).
Notation "'scb'" := G.(scb).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'sb_neq_loc'" := (sb \ same_loc).

Hypothesis WF : Wf G.
Hypothesis COMP : complete G.
Hypothesis COH : coherence G.
Hypothesis SC_PER_LOC : sc_per_loc G.

Notation "'sb''" := (sb \ rmw).
Notation "'ar'" := (ar G).
Notation "'br'" := (br G).

Lemma global_sc_helper
  (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb) :
  ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^? ⨾
    (⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW∩₁Sc⦘)^* ⨾
      eco^? ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ br⁺.
Proof.
  assert (transitive eco) as TECO by (by apply eco_trans).
  assert (transitive hb ) as THB  by (by apply hb_trans).

  assert (⦗F ∩₁ Sc⦘ ⨾ hb ⨾ eco^? ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ br⁺) as HH.
  { rewrite crE. relsf.
    unionL.
    { by apply f_sc_hb_f_sc_in_br. }
    rewrite <- ct_step. unfold imm.br, imm.psc.
      by unionR left. }

  eapply rt_ind_left with
      (P:= fun __ => ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ __ ⨾ eco ^? ⨾ hb ⨾ ⦗F∩₁Sc⦘).
  { eauto with hahn. }
  { relsf. }
  intros k IH.
  arewrite (⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW∩₁Sc⦘ ⊆
            ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ∪ eco)
    by basic_solver 42.
  rewrite HSC.
  arewrite (⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ (hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb ∪ eco) ⊆ 
            ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ^? ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^? ∪
              ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^?)
    by basic_solver 42.
  relsf.
  rewrite !seqA.
  rewrite <- seq_eqvK at 2; rewrite !seqA.
  sin_rewrite IH.
  apply inclusion_union_l; try done.
  rewrite <- !seqA with (r3 := br⁺).
  sin_rewrite HH.
  apply transitiveI. apply transitive_ct.
Qed.

Lemma RW_scb_RW :
  ⦗RW∩₁Sc⦘ ⨾ scb ⨾ ⦗RW∩₁Sc⦘ ⊆
  ⦗RW∩₁Sc⦘ ⨾
    (sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ (hb∩same_loc) ⨾ ⦗RW⦘ ∪ co ∪ fr)
      ⨾ ⦗RW∩₁Sc⦘.
Proof. unfold imm.scb; basic_solver 42. Qed.

Lemma psc_base_rw_rw :
  ⦗RW∩₁Sc⦘ ⨾ psc_base ⨾ ⦗RW∩₁Sc⦘ ⊆ ⦗RW∩₁Sc⦘ ⨾ scb ⨾ ⦗RW∩₁Sc⦘.
Proof.
  unfold imm.psc, imm.psc_base. rewrite !seqA.
  rewrite !crE.
  rewrite !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  arewrite_false !(⦗RW ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⨾ ⦗F⦘).
  { type_solver. }
  arewrite_false !(⦗F⦘ ⨾ ⦗Sc⦘ ⨾ ⦗RW ∩₁ Sc⦘).
  { type_solver. }
  basic_solver.
Qed.

Lemma scb_in_hb_eco : scb ⊆ hb ∪ eco.
Proof.
  unfold imm.scb. rewrite sb_in_hb, co_in_eco, fr_in_eco.
  generalize (@hb_trans G). basic_solver.
Qed.

Lemma psc_base_f :
  ⦗F∩₁Sc⦘ ⨾ psc_base ⨾ ⦗F∩₁Sc⦘ ⊆ br⁺.
Proof.
  unfold imm.psc, imm.psc_base, imm.scb.
  rewrite sb_in_hb, co_in_eco, fr_in_eco.
  arewrite (hb ∪ (hb \ same_loc) ⨾ hb ⨾ (hb \ same_loc) ∪ hb ∩ same_loc ⊆ hb).
  { generalize (@hb_trans G). basic_solver. }
  arewrite (hb ∪ eco ∪ eco ⊆ hb ∪ eco).
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  arewrite_false !(⦗F ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⨾ eco).
  { rewrite WF.(wf_ecoD). type_solver. }
  arewrite_false !(eco ⨾ ⦗Sc⦘ ⨾ ⦗F ∩₁ Sc⦘).
  { rewrite WF.(wf_ecoD). type_solver. }
  rewrite !seq_false_l, !seq_false_r, !union_false_l, !union_false_r.
  repeat arewrite (hb ⨾ hb ⊆ hb).
  repeat arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⊆ ⦗F ∩₁ Sc⦘).
  repeat arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗F ∩₁ Sc⦘).
  repeat arewrite (⦗Sc⦘ ⨾ ⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘).
  repeat arewrite (⦗F⦘ ⨾ ⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘).
  rewrite f_sc_hb_f_sc_in_br; auto.
  unionL; eauto with hahn.
Qed.

Lemma psc_base_rw_f :
  ⦗RW∩₁Sc⦘ ⨾ psc_base ⨾ ⦗F∩₁Sc⦘ ⊆ ⦗RW∩₁Sc⦘ ⨾ eco^? ⨾ hb ⨾ (⦗F∩₁Sc⦘).
Proof.
  unfold imm.psc, imm.psc_base.
  rewrite scb_in_hb_eco; auto. rewrite !seqA.
  arewrite (⦗RW ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⨾ (⦗F⦘ ⨾ hb)^? ⊆ ⦗RW ∩₁ Sc⦘).
  { rewrite crE, !seq_union_r. type_solver. }
  rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  arewrite_false !(eco ⨾ ⦗Sc⦘ ⨾ ⦗F ∩₁ Sc⦘).
  { rewrite WF.(wf_ecoD). type_solver. }
  generalize (@hb_trans G). 
  basic_solver 42.
Qed.

Lemma psc_base_f_rw :
  ⦗F∩₁Sc⦘ ⨾ psc_base ⨾ ⦗RW∩₁Sc⦘ ⊆ ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco^? ⨾ (⦗RW∩₁Sc⦘).
Proof.
  unfold imm.psc, imm.psc_base.
  rewrite scb_in_hb_eco; auto. rewrite !seqA.
  arewrite ((hb ⨾ ⦗F⦘)^? ⨾ ⦗Sc⦘ ⨾ ⦗RW ∩₁ Sc⦘ ⊆ ⦗RW ∩₁ Sc⦘).
  { rewrite crE, !seq_union_l. type_solver. }
  rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  arewrite_false !(⦗F ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⨾ eco).
  { rewrite WF.(wf_ecoD). type_solver. }
  generalize (@hb_trans G). 
  basic_solver 42.
Qed.

Lemma global_scb_rw_acyc
      (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
      (ACYC: acyclic br) :
  acyclic (⦗RW ∩₁ Sc⦘ ⨾ scb ⨾ ⦗RW ∩₁ Sc⦘).
Proof.
  rewrite RW_scb_RW.
  rewrite hb_loc_in_eco; auto.
  arewrite (sb_neq_loc ⊆ sb').
  { generalize WF.(wf_rmwl). basic_solver. }
  arewrite (sb ⊆ sb' ∪ rmw) at 1.
  { unfold inclusion, minus_rel, union; ins; tauto. }
  rewrite rmw_in_fr at 2; auto.
  rewrite co_in_eco; auto.
  rewrite fr_in_eco; auto.
  rewrite <- !unionA.
  arewrite (sb' ∪ eco ∪ sb' ⨾ hb ⨾ sb' ∪ eco ∪ sb' ∪ sb' ⨾ hb ⨾ sb'
                ∪ eco ∪ eco ⊆
            sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) by basic_solver 42.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  arewrite (⦗RW∩₁Sc⦘ ⨾ sb' ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb).
  { rewrite <- HSC. basic_solver 10. }
  arewrite (⦗RW∩₁Sc⦘ ⨾ sb' ⨾ hb ⨾ sb' ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb).
  { rewrite <- HSC. basic_solver 10. }
  rewrite unionK.
  apply acyclic_utt; splits.
  { apply transitiveI. arewrite_id ⦗F∩₁Sc⦘ at 1.
    rewrite seq_id_l.
    generalize (@hb_trans G). basic_solver 10. }
  { apply transitiveI.
    do 2 (arewrite_id ⦗RW∩₁Sc⦘ at 2; rewrite seq_id_l).
    generalize (@eco_trans G). basic_solver 10. }
  { arewrite_id ⦗F∩₁Sc⦘ at 1. rewrite seq_id_l.
    arewrite (hb ;; hb ⊆ hb). by apply hb_irr. }
  { generalize (eco_irr WF). basic_solver 10. }
  arewrite (⦗F∩₁Sc⦘ ⊆ ⦗F∩₁Sc⦘ ⨾ ⦗F∩₁Sc⦘) by basic_solver.
  do 2 (apply acyclic_seqC; try rewrite !seqA).
  eapply acyclic_mon with (r := psc).
  { by arewrite (psc ⊆ br). }
  unfold imm.psc. basic_solver 12.
Qed.

Lemma global_sc_base
      (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
      (ACYC: acyclic br) :
  acyclic psc_base.
Proof.
  assert (transitive eco) as TECO by (by apply eco_trans).
  assert (transitive hb ) as THB  by (by apply hb_trans).

  eapply acyc_dom with (d:= RW∩₁Sc) (e:= F∩₁Sc); try edone.
  { unfold imm.ar,imm.psc, imm.psc_base.
    arewrite (⦗Sc⦘ ≡ ⦗RW∩₁Sc⦘ ∪ ⦗F∩₁Sc⦘) by type_solver 42.
    basic_solver 42. }
  { type_solver. }
  { rewrite psc_base_rw_rw; auto.
    apply global_scb_rw_acyc; auto. }
  { rewrite psc_base_f; auto.
    red. by rewrite ct_of_ct. }
  rewrite psc_base_rw_rw; auto.
  rewrite RW_scb_RW.
  arewrite (
      sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ (hb ∩ same_loc) ⨾ ⦗RW⦘ ∪ co ∪ fr ⊆
      sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco
    ).
  { arewrite (sb ⊆ sb' ∪ rmw) by (by apply inclusion_union_minus).
    rewrite rmw_in_fr at 2; auto.
    rewrite fr_in_eco, co_in_eco, hb_loc_in_eco; auto.
    arewrite (sb_neq_loc ⊆ sb').
    { generalize WF.(wf_rmwl). basic_solver. }
    basic_solver 10. }
  sin_rewrite psc_base_rw_f; auto.
  sin_rewrite psc_base_f_rw; auto.
  rewrite !seqA.
  arewrite_id ⦗RW∩₁Sc⦘ at 1. arewrite_id ⦗RW∩₁Sc⦘ at 3. rewrite !seq_id_l.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ psc_base ⨾ ⦗F ∩₁ Sc⦘ ⊆ br⁺) by (by apply psc_base_f).
  rewrite rt_of_ct.
  rewrite <- !seqA with (r3 := br ^* ), global_sc_helper; auto.
  rels. red. by rewrite ct_of_ct.
Qed.

Lemma global_sc
      (HSC: ⦗RW∩₁Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW∩₁Sc⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
      (ACYC: acyclic br) :
  acyclic ar.
Proof.
  assert (transitive eco) as TECO by (by apply eco_trans).
  assert (transitive hb ) as THB  by (by apply hb_trans).
  arewrite (ar ⊆ psc_base ∪ br).
  { unfold imm.ar, imm.br. by rewrite !unionA. }
  apply acyclic_union1; auto.
  { apply global_sc_base; auto. }
  
  (* The below part of the proof is just a playground. *)
  
  assert (acyclic (psc_base ⨾ br⁺)).
  { arewrite (psc_base ⊆ (<|RW∩₁Sc|> ∪ <|F∩₁Sc|>) ;; psc_base ;; (<|RW∩₁Sc|> ∪ <|F∩₁Sc|>)).
    { admit. }
    rewrite !seq_union_l, !seq_union_r.
    sin_rewrite psc_base_f.
    sin_rewrite psc_base_rw_rw.
    sin_rewrite psc_base_f_rw.
    sin_rewrite psc_base_rw_f.
    admit. }

    (* unfold imm.psc_base, imm.scb. *)
    (* rewrite !crE. *)
    (* rewrite !seq_union_l, !seq_union_r. *)
    (* rewrite !seq_id_l, !seqA. *)

  (* assert (exists rr, psc_base ⊆ rr). *)
  (* { eexists. unfold imm.psc_base, imm.scb. *)
  (*   rewrite !crE. *)
  (*   rewrite !seq_union_l, !seq_union_r. *)
  (*   rewrite !seq_id_l, !seqA. *)
  (*   arewrite_false !(⦗F ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⨾ eco). *)
  (*   { rewrite WF.(wf_ecoD). type_solver. } *)
  (*   arewrite_false !(eco ⨾ ⦗Sc⦘ ⨾ ⦗F ∩₁ Sc⦘). *)
  (*   { rewrite WF.(wf_ecoD). type_solver. } *)
  (*   rewrite !seq_false_l, !seq_false_r, !union_false_l, !union_false_r. *)
  (*   repeat arewrite (hb ⨾ hb ⊆ hb). *)
  (*   repeat arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗Sc⦘ ⊆ ⦗F ∩₁ Sc⦘). *)
  (*   repeat arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗F ∩₁ Sc⦘). *)
  (*   repeat arewrite (⦗Sc⦘ ⨾ ⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘). *)
  (*   repeat arewrite (⦗F⦘ ⨾ ⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘). *)
Admitted.
  

(* Definition change_mode (l: label) (m: mode) : label := 
  match l with
  | Aload l v _ => Aload l v m
  | Astore l v _ => Astore l v m
  | Afence _ => Afence m
  end. *)
  
(* Definition change_modes (G: execution) (A: event -> Prop) (m: mode): execution :=
  Build_execution 
    acts
    (fun a => if (A a) then change_mode (lab a) m else lab a)
    sb rmw rf mo. *)

(* Lemma transf_g
  (NO_SC: ⦗Sc⦘ ≡ ∅₂)
  A (A_SUB: A ⊆₁ R_acq ∪₁ W_rel)
  (A1: ⦗A⦘ ⨾ (sb' ∪ sb'⨾hb⨾sb') ⨾ ⦗A⦘ ⊆ hb ⨾ ⦗F∩₁Sc⦘ ⨾ hb)
  (A2: ⦗A⦘ ⨾ rmw ≡ rmw ⨾ ⦗A⦘)
  (G' : execution) (CHANGE: G' = G)
  : consistent G'.
Proof.
Admitted. *)

End Sc_opt.