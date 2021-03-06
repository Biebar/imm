(******************************************************************************)
(** * Definition of the WWMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section WWMM.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
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

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition wwmm_consistent mo :=
  ⟪ Cmo   : strict_total_order E mo ⟫ /\
  ⟪ Chbmo : hb ⊆ mo ⟫ /\
  ⟪ Chbrf : irreflexive (hb ⨾ rf) ⟫ /\
  ⟪ Chbrfhb :
      irreflexive (hb ⨾ rf⁻¹ ⨾ (hb ∩ same_loc) ⨾ ⦗ W ⦘) ⟫ /\
  ⟪ Cirr1 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ mo ⨾ ⦗R∩₁Sc⦘ ⨾
                   rf⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (mo ∩ same_loc)) ⟫ /\
  ⟪ Cirr2 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ hb ⨾
                   (hb ∩ rf)⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (mo ∩ same_loc)) ⟫ /\
  ⟪ Cirr3 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ mo ⨾ ⦗R∩₁Sc⦘ ⨾
                   (hb ∩ rf)⁻¹ ⨾ (hb ∩ same_loc)) ⟫.

End WWMM.
