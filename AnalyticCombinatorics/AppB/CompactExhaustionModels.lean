import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compact exhaustion models.

This file records a finite compact-index schema with cover and margin
budgets.
-/

namespace AnalyticCombinatorics.AppB.CompactExhaustionModels

structure CompactExhaustionData where
  compactIndex : ℕ
  coverCount : ℕ
  margin : ℕ
deriving DecidableEq, Repr

def positiveCompactIndex (d : CompactExhaustionData) : Prop :=
  0 < d.compactIndex

def coverControlled (d : CompactExhaustionData) : Prop :=
  d.coverCount ≤ d.compactIndex + d.margin

def compactExhaustionReady (d : CompactExhaustionData) : Prop :=
  positiveCompactIndex d ∧ coverControlled d

def compactExhaustionBudget (d : CompactExhaustionData) : ℕ :=
  d.compactIndex + d.coverCount + d.margin

theorem compactExhaustionReady.index {d : CompactExhaustionData}
    (h : compactExhaustionReady d) :
    positiveCompactIndex d ∧ coverControlled d ∧
      d.compactIndex ≤ compactExhaustionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold compactExhaustionBudget
  omega

theorem compactIndex_le_exhaustionBudget (d : CompactExhaustionData) :
    d.compactIndex ≤ compactExhaustionBudget d := by
  unfold compactExhaustionBudget
  omega

def sampleCompactExhaustionData : CompactExhaustionData :=
  { compactIndex := 4, coverCount := 6, margin := 3 }

example : compactExhaustionReady sampleCompactExhaustionData := by
  norm_num [compactExhaustionReady, positiveCompactIndex]
  norm_num [coverControlled, sampleCompactExhaustionData]

example : compactExhaustionBudget sampleCompactExhaustionData = 13 := by
  native_decide

/-- Finite executable readiness audit for compact-exhaustion windows. -/
def compactExhaustionListReady (windows : List CompactExhaustionData) : Bool :=
  windows.all fun d =>
    0 < d.compactIndex && d.coverCount ≤ d.compactIndex + d.margin

theorem compactExhaustionList_readyWindow :
    compactExhaustionListReady
      [{ compactIndex := 3, coverCount := 4, margin := 1 },
       { compactIndex := 4, coverCount := 6, margin := 3 }] = true := by
  unfold compactExhaustionListReady
  native_decide


structure CompactExhaustionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompactExhaustionModelsBudgetCertificate.controlled
    (c : CompactExhaustionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompactExhaustionModelsBudgetCertificate.budgetControlled
    (c : CompactExhaustionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompactExhaustionModelsBudgetCertificate.Ready
    (c : CompactExhaustionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompactExhaustionModelsBudgetCertificate.size
    (c : CompactExhaustionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compactExhaustionModels_budgetCertificate_le_size
    (c : CompactExhaustionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompactExhaustionModelsBudgetCertificate :
    CompactExhaustionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompactExhaustionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompactExhaustionModelsBudgetCertificate.controlled,
      sampleCompactExhaustionModelsBudgetCertificate]
  · norm_num [CompactExhaustionModelsBudgetCertificate.budgetControlled,
      sampleCompactExhaustionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompactExhaustionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompactExhaustionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCompactExhaustionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompactExhaustionModelsBudgetCertificate.controlled,
      sampleCompactExhaustionModelsBudgetCertificate]
  · norm_num [CompactExhaustionModelsBudgetCertificate.budgetControlled,
      sampleCompactExhaustionModelsBudgetCertificate]

example :
    sampleCompactExhaustionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompactExhaustionModelsBudgetCertificate.size := by
  apply compactExhaustionModels_budgetCertificate_le_size
  constructor
  · norm_num [CompactExhaustionModelsBudgetCertificate.controlled,
      sampleCompactExhaustionModelsBudgetCertificate]
  · norm_num [CompactExhaustionModelsBudgetCertificate.budgetControlled,
      sampleCompactExhaustionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CompactExhaustionModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompactExhaustionModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCompactExhaustionModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.CompactExhaustionModels
