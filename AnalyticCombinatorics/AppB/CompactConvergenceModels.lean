import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compact-convergence bookkeeping.

The finite data tracks how many compact sets are controlled and the common
uniform error budget.
-/

namespace AnalyticCombinatorics.AppB.CompactConvergenceModels

structure CompactConvergenceDatum where
  compactCount : ℕ
  uniformError : ℕ
  targetBudget : ℕ
deriving DecidableEq, Repr

def nonemptyCompactFamily (d : CompactConvergenceDatum) : Prop :=
  0 < d.compactCount

def compactErrorControlled (d : CompactConvergenceDatum) : Prop :=
  d.uniformError ≤ d.targetBudget

def compactConvergenceReady (d : CompactConvergenceDatum) : Prop :=
  nonemptyCompactFamily d ∧ compactErrorControlled d

def convergenceSlack (d : CompactConvergenceDatum) : ℕ :=
  d.targetBudget - d.uniformError

theorem compactConvergenceReady.error {d : CompactConvergenceDatum}
    (h : compactConvergenceReady d) :
    nonemptyCompactFamily d ∧ compactErrorControlled d := by
  refine ⟨h.1, h.2⟩

theorem convergenceSlack_add {d : CompactConvergenceDatum}
    (h : compactErrorControlled d) :
    convergenceSlack d + d.uniformError = d.targetBudget := by
  unfold convergenceSlack compactErrorControlled at *
  omega

def sampleCompactConvergence : CompactConvergenceDatum :=
  { compactCount := 4, uniformError := 3, targetBudget := 9 }

example : compactConvergenceReady sampleCompactConvergence := by
  norm_num
    [compactConvergenceReady, nonemptyCompactFamily, compactErrorControlled,
      sampleCompactConvergence]

example : convergenceSlack sampleCompactConvergence = 6 := by
  native_decide

structure CompactConvergenceWindow where
  compactWindow : ℕ
  uniformErrorWindow : ℕ
  targetWindow : ℕ
  extractionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompactConvergenceWindow.errorControlled (w : CompactConvergenceWindow) : Prop :=
  w.uniformErrorWindow ≤ w.targetWindow + w.slack

def compactConvergenceWindowReady (w : CompactConvergenceWindow) : Prop :=
  0 < w.compactWindow ∧ w.errorControlled ∧
    w.extractionBudget ≤ w.compactWindow + w.targetWindow + w.slack

def CompactConvergenceWindow.certificate (w : CompactConvergenceWindow) : ℕ :=
  w.compactWindow + w.uniformErrorWindow + w.targetWindow + w.extractionBudget + w.slack

theorem compactConvergence_extractionBudget_le_certificate (w : CompactConvergenceWindow) :
    w.extractionBudget ≤ w.certificate := by
  unfold CompactConvergenceWindow.certificate
  omega

def sampleCompactConvergenceWindow : CompactConvergenceWindow :=
  { compactWindow := 4, uniformErrorWindow := 3, targetWindow := 9,
    extractionBudget := 14, slack := 1 }

example : compactConvergenceWindowReady sampleCompactConvergenceWindow := by
  norm_num [compactConvergenceWindowReady, CompactConvergenceWindow.errorControlled,
    sampleCompactConvergenceWindow]


structure CompactConvergenceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompactConvergenceModelsBudgetCertificate.controlled
    (c : CompactConvergenceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompactConvergenceModelsBudgetCertificate.budgetControlled
    (c : CompactConvergenceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompactConvergenceModelsBudgetCertificate.Ready
    (c : CompactConvergenceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompactConvergenceModelsBudgetCertificate.size
    (c : CompactConvergenceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compactConvergenceModels_budgetCertificate_le_size
    (c : CompactConvergenceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompactConvergenceModelsBudgetCertificate :
    CompactConvergenceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompactConvergenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompactConvergenceModelsBudgetCertificate.controlled,
      sampleCompactConvergenceModelsBudgetCertificate]
  · norm_num [CompactConvergenceModelsBudgetCertificate.budgetControlled,
      sampleCompactConvergenceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompactConvergenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompactConvergenceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCompactConvergenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompactConvergenceModelsBudgetCertificate.controlled,
      sampleCompactConvergenceModelsBudgetCertificate]
  · norm_num [CompactConvergenceModelsBudgetCertificate.budgetControlled,
      sampleCompactConvergenceModelsBudgetCertificate]

example :
    sampleCompactConvergenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompactConvergenceModelsBudgetCertificate.size := by
  apply compactConvergenceModels_budgetCertificate_le_size
  constructor
  · norm_num [CompactConvergenceModelsBudgetCertificate.controlled,
      sampleCompactConvergenceModelsBudgetCertificate]
  · norm_num [CompactConvergenceModelsBudgetCertificate.budgetControlled,
      sampleCompactConvergenceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CompactConvergenceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompactConvergenceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompactConvergenceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.CompactConvergenceModels
