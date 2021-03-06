(******************************************************************************)
(** * Definition of the common part of IMM and s_IMM  *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition fwbob := sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
                         sb ⨾ ⦗F∩₁Acq/Rel⦘ ∪ ⦗F∩₁Acq/Rel⦘ ⨾ sb.

Definition bob := fwbob ∪ ⦗R∩₁Acq⦘ ⨾ sb.

Definition ppo := ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺ ⨾ ⦗W⦘.

Definition ar_int := bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_to_w_rel_in_fwbob : sb ⨾ ⦗W∩₁Rel⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_from_w_rel_in_fwbob : ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_to_f_in_fwbob : sb ⨾ ⦗F∩₁Acq/Rel⦘ ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma sb_from_f_in_fwbob : ⦗F∩₁Acq/Rel⦘ ⨾ sb  ⊆ fwbob.
Proof. unfold fwbob. basic_solver 10. Qed.

Lemma fwbob_in_bob : fwbob ⊆ bob.
Proof. unfold bob. basic_solver 12. Qed.

Lemma sb_to_w_rel_in_bob : sb ⨾ ⦗W∩₁Rel⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_to_w_rel_in_fwbob.
Qed.

Lemma sb_from_w_rel_in_bob : ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_from_w_rel_in_fwbob.
Qed.

Lemma sb_to_f_in_bob : sb ⨾ ⦗F∩₁Acq/Rel⦘ ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_to_f_in_fwbob.
Qed.

Lemma sb_from_f_in_bob : ⦗F∩₁Acq/Rel⦘ ⨾ sb  ⊆ bob.
Proof.
  etransitivity; [|by apply fwbob_in_bob].
  apply sb_from_f_in_fwbob.
Qed.

Lemma sb_from_r_acq_in_bob : ⦗R∩₁Acq⦘ ⨾ sb  ⊆ bob.
Proof. unfold bob. basic_solver 10. Qed.

Lemma fwbob_in_sb : fwbob ⊆ sb.
Proof.
  unfold fwbob.
  basic_solver 12.
Qed.

Lemma sb_fwbob_in_fwbob : sb ⨾ fwbob ⊆ fwbob⁺.
Proof.
unfold fwbob.
generalize (@sb_trans G); ins.
relsf; unionL.
1,3: rewrite <- ct_step; basic_solver 42.
1,2: rewrite ct_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 16.
Qed.

Lemma bob_in_sb : bob ⊆ sb.
Proof.
unfold bob; rewrite fwbob_in_sb; basic_solver.
Qed.

Lemma ppo_in_sb WF: ppo ⊆ sb.
Proof.
unfold ppo.
rewrite (addr_in_sb WF), (data_in_sb WF), (ctrl_in_sb WF).
rewrite (rmw_dep_in_sb WF).
arewrite (rfi ⊆ sb).
arewrite_id ⦗R_ex⦘.
generalize (@sb_trans G); ins; relsf.
basic_solver.
Qed.

Lemma rmw_in_ppo WF : rmw ⊆ ppo.
Proof.
unfold ppo; rewrite (wf_rmwD WF).
rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1.
rewrite (rmw_in_sb WF) at 1.
hahn_frame; unfolder; econs; basic_solver 12.
Qed.

Lemma rmw_sb_W_in_ppo WF : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof.
unfold ppo; rewrite (wf_rmwD WF).
rewrite (dom_l (wf_rmwD WF)), R_ex_in_R at 1.
rewrite (rmw_in_sb WF) at 1.
rewrite <- ct_step.
generalize (@sb_trans G).
basic_solver 12.
Qed.

Lemma data_in_ppo WF : data ⊆ ppo.
Proof.
unfold ppo; rewrite (wf_dataD WF) at 1.
hahn_frame; econs; basic_solver 12.
Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_fwbobE WF : fwbob ≡ ⦗E⦘ ⨾ fwbob ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold fwbob.
rewrite wf_sbE.
basic_solver 42.
Qed.

Lemma wf_bobE WF : bob ≡ ⦗E⦘ ⨾ bob ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold bob.
rewrite (wf_fwbobE WF), wf_sbE.
basic_solver 42.
Qed.

Lemma wf_ppoE WF : ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ppo.
arewrite ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺
  ⊆ ⦗E⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺ ⨾ ⦗E⦘) at 1.
{ rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
  apply inclusion_t_t.
  unfold Execution.rfi.
  rewrite (wf_rfE WF), (wf_dataE WF), (wf_rmw_depE WF) at 1.
  rewrite (wf_addrE WF), (wf_ctrlE WF).
  rewrite wf_sbE at 1 2 3 4.
  basic_solver 21.
}
basic_solver 42.
Qed.

Lemma wf_ar_intE WF : ar_int ≡ ⦗E⦘ ⨾ ar_int ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ar_int.
rewrite (wf_bobE WF), (wf_ppoE WF) at 1.
rewrite (wf_detourE WF), (@wf_sbE G).
basic_solver 42.
Qed.


(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma wf_ppoD: ppo ≡ ⦗R⦘ ⨾ ppo ⨾ ⦗W⦘.
Proof.
split; [|basic_solver].
unfold ppo; basic_solver.
Qed.

Lemma fwbob_r_sb: fwbob ⨾ ⦗ R ⦘ ⨾ sb ⊆ fwbob.
Proof.
unfold fwbob; relsf; unionL.
all: try by type_solver.
all: generalize (@sb_trans G); basic_solver 21.
Qed.

Lemma bob_r_sb: bob ⨾ ⦗ R ⦘ ⨾ sb ⊆ bob.
Proof.
unfold bob; relsf; rewrite fwbob_r_sb.
generalize (@sb_trans G); basic_solver 21.
Qed.

Lemma fwbob_ppo WF: fwbob ⨾ ppo ⊆ fwbob.
Proof.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite fwbob_r_sb.
basic_solver.
Qed.

Lemma bob_ppo WF: bob ⨾ ppo ⊆ bob.
Proof.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite bob_r_sb.
basic_solver.
Qed.

Lemma ar_int_in_sb WF: ar_int ⊆ sb.
Proof.
unfold ar_int.
rewrite bob_in_sb.
rewrite (ppo_in_sb WF).
arewrite (detour ⊆ sb).
basic_solver 21.
Qed.

Lemma ppo_rfi_ppo : ppo ⨾ rfi ⨾ ppo ⊆ ppo.
Proof.
unfold ppo.
rewrite !seqA.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R⦘ at 2.
arewrite (rfi ⊆ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)＊) at 2.
rewrite inclusion_t_rt at 1.
relsf.
Qed.

Lemma deps_rfi_in_ppo : ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unfold ppo, Execution.deps.
  hahn_frame.
  apply inclusion_t_t; basic_solver 21.
Qed.

Lemma ppo_alt WF 
  (RMW_DEPS : rmw ⊆ deps)
  (RMW_CTRL_FAIL : ⦗R_ex⦘ ⨾ sb ⊆ rmw ∪ ctrl)
  (DEPS_RMW_FAIL : rmw_dep ⨾ (rmw ∪ ctrl) ⊆ ctrl) : 
  ppo ≡ ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘.
Proof.
generalize (@sb_trans G); ins.
unfold ppo.
split.
2: by hahn_frame; apply inclusion_t_t; basic_solver 12.
sin_rewrite RMW_CTRL_FAIL; rewrite <- !unionA.
rewrite RMW_DEPS; unfold Execution.deps.
rewrite path_ut_first; relsf; unionL.
by hahn_frame; apply inclusion_t_t; basic_solver 12.
arewrite ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ (data ∪ addr ∪ ctrl) ∪ ctrl ∪ rmw_dep) ⊆ sb).
{ rewrite (data_in_sb WF), (addr_in_sb WF), (ctrl_in_sb WF).
  arewrite (rfi ⊆ sb).
  rewrite (rmw_dep_in_sb WF).
  relsf. }
relsf.
rewrite (dom_r (wf_rmw_depD WF)), !seqA.
rewrite (crE sb) at 2; relsf; unionL.
by rewrite R_ex_in_R; type_solver.
hahn_frame.
sin_rewrite RMW_CTRL_FAIL.
rewrite DEPS_RMW_FAIL.
rewrite ct_end.
apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42.
Qed.

Lemma bob_in_ar_int : bob ⊆ ar_int.
Proof. unfold ar_int. basic_solver. Qed.

Lemma ppo_in_ar_int : ppo ⊆ ar_int.
Proof. unfold ar_int. basic_solver. Qed.

Lemma detour_in_ar_int : detour ⊆ ar_int.
Proof. unfold ar_int. basic_solver. Qed.

Lemma w_ex_acq_sb_w_in_ar_int : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar_int.
Proof. unfold ar_int. basic_solver 5. Qed.


End IMM.