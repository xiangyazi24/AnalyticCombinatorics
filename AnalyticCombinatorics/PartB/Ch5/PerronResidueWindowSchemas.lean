import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perron residue window schemas.

This module records finite bookkeeping for Perron residue windows.
-/

namespace AnalyticCombinatorics.PartB.Ch5.PerronResidueWindowSchemas

structure PerronResidueWindowData where
  perronHeight : ℕ
  residueWindow : ℕ
  perronSlack : ℕ
deriving DecidableEq, Repr

def hasPerronHeight (d : PerronResidueWindowData) : Prop :=
  0 < d.perronHeight

def residueWindowControlled (d : PerronResidueWindowData) : Prop :=
  d.residueWindow ≤ d.perronHeight + d.perronSlack

def perronResidueWindowReady (d : PerronResidueWindowData) : Prop :=
  hasPerronHeight d ∧ residueWindowControlled d

def perronResidueWindowBudget (d : PerronResidueWindowData) : ℕ :=
  d.perronHeight + d.residueWindow + d.perronSlack

theorem perronResidueWindowReady.hasPerronHeight
    {d : PerronResidueWindowData}
    (h : perronResidueWindowReady d) :
    hasPerronHeight d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem residueWindow_le_budget (d : PerronResidueWindowData) :
    d.residueWindow ≤ perronResidueWindowBudget d := by
  unfold perronResidueWindowBudget
  omega

def samplePerronResidueWindowData : PerronResidueWindowData :=
  { perronHeight := 6, residueWindow := 8, perronSlack := 3 }

example : perronResidueWindowReady samplePerronResidueWindowData := by
  norm_num [perronResidueWindowReady, hasPerronHeight]
  norm_num [residueWindowControlled, samplePerronResidueWindowData]

example : perronResidueWindowBudget samplePerronResidueWindowData = 17 := by
  native_decide

structure PerronResidueWindowBudgetCertificate where
  perronHeightWindow : ℕ
  residueWindow : ℕ
  perronSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerronResidueWindowBudgetCertificate.controlled
    (c : PerronResidueWindowBudgetCertificate) : Prop :=
  0 < c.perronHeightWindow ∧
    c.residueWindow ≤ c.perronHeightWindow + c.perronSlackWindow + c.slack

def PerronResidueWindowBudgetCertificate.budgetControlled
    (c : PerronResidueWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.perronHeightWindow + c.residueWindow + c.perronSlackWindow + c.slack

def PerronResidueWindowBudgetCertificate.Ready
    (c : PerronResidueWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerronResidueWindowBudgetCertificate.size
    (c : PerronResidueWindowBudgetCertificate) : ℕ :=
  c.perronHeightWindow + c.residueWindow + c.perronSlackWindow + c.slack

theorem perronResidueWindow_budgetCertificate_le_size
    (c : PerronResidueWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePerronResidueWindowBudgetCertificate :
    PerronResidueWindowBudgetCertificate :=
  { perronHeightWindow := 6
    residueWindow := 8
    perronSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePerronResidueWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronResidueWindowBudgetCertificate.controlled,
      samplePerronResidueWindowBudgetCertificate]
  · norm_num [PerronResidueWindowBudgetCertificate.budgetControlled,
      samplePerronResidueWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerronResidueWindowBudgetCertificate.certificateBudgetWindow ≤
      samplePerronResidueWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePerronResidueWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [PerronResidueWindowBudgetCertificate.controlled,
      samplePerronResidueWindowBudgetCertificate]
  · norm_num [PerronResidueWindowBudgetCertificate.budgetControlled,
      samplePerronResidueWindowBudgetCertificate]

example :
    samplePerronResidueWindowBudgetCertificate.certificateBudgetWindow ≤
      samplePerronResidueWindowBudgetCertificate.size := by
  apply perronResidueWindow_budgetCertificate_le_size
  constructor
  · norm_num [PerronResidueWindowBudgetCertificate.controlled,
      samplePerronResidueWindowBudgetCertificate]
  · norm_num [PerronResidueWindowBudgetCertificate.budgetControlled,
      samplePerronResidueWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PerronResidueWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [samplePerronResidueWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePerronResidueWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.PerronResidueWindowSchemas
