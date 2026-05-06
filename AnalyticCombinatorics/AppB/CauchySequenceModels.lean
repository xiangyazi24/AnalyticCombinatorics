import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cauchy sequence bookkeeping models.

The file records finite tail thresholds and error budgets for normal-family
and compact-convergence arguments.
-/

namespace AnalyticCombinatorics.AppB.CauchySequenceModels

structure CauchyDatum where
  tailStart : ℕ
  errorBudget : ℕ
  comparisonBudget : ℕ
deriving DecidableEq, Repr

def positiveTailStart (d : CauchyDatum) : Prop :=
  0 < d.tailStart

def cauchyErrorControlled (d : CauchyDatum) : Prop :=
  d.errorBudget ≤ d.comparisonBudget

def cauchyReady (d : CauchyDatum) : Prop :=
  positiveTailStart d ∧ cauchyErrorControlled d

def cauchySlack (d : CauchyDatum) : ℕ :=
  d.comparisonBudget - d.errorBudget

theorem cauchyReady.controlled {d : CauchyDatum}
    (h : cauchyReady d) :
    positiveTailStart d ∧ cauchyErrorControlled d := by
  refine ⟨h.1, h.2⟩

theorem cauchySlack_add {d : CauchyDatum}
    (h : cauchyErrorControlled d) :
    cauchySlack d + d.errorBudget = d.comparisonBudget := by
  unfold cauchySlack cauchyErrorControlled at *
  omega

def sampleCauchySequence : CauchyDatum :=
  { tailStart := 5, errorBudget := 2, comparisonBudget := 9 }

example : cauchyReady sampleCauchySequence := by
  norm_num [cauchyReady, positiveTailStart, cauchyErrorControlled, sampleCauchySequence]

example : cauchySlack sampleCauchySequence = 7 := by
  native_decide

structure CauchyWindow where
  tailStart : ℕ
  errorBudget : ℕ
  comparisonBudget : ℕ
  subsequenceBudget : ℕ
deriving DecidableEq, Repr

def CauchyWindow.tailReady (w : CauchyWindow) : Prop :=
  0 < w.tailStart

def CauchyWindow.errorControlled (w : CauchyWindow) : Prop :=
  w.errorBudget ≤ w.comparisonBudget

def CauchyWindow.subsequenceControlled (w : CauchyWindow) : Prop :=
  w.subsequenceBudget ≤ w.tailStart + w.comparisonBudget

def CauchyWindow.ready (w : CauchyWindow) : Prop :=
  w.tailReady ∧ w.errorControlled ∧ w.subsequenceControlled

def CauchyWindow.certificate (w : CauchyWindow) : ℕ :=
  w.tailStart + w.errorBudget + w.comparisonBudget + w.subsequenceBudget

theorem subsequenceBudget_le_certificate (w : CauchyWindow) :
    w.subsequenceBudget ≤ w.certificate := by
  unfold CauchyWindow.certificate
  omega

def sampleCauchyWindow : CauchyWindow :=
  { tailStart := 5, errorBudget := 2, comparisonBudget := 9, subsequenceBudget := 8 }

example : sampleCauchyWindow.ready := by
  norm_num [sampleCauchyWindow, CauchyWindow.ready, CauchyWindow.tailReady,
    CauchyWindow.errorControlled, CauchyWindow.subsequenceControlled]


structure CauchySequenceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CauchySequenceModelsBudgetCertificate.controlled
    (c : CauchySequenceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CauchySequenceModelsBudgetCertificate.budgetControlled
    (c : CauchySequenceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CauchySequenceModelsBudgetCertificate.Ready
    (c : CauchySequenceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CauchySequenceModelsBudgetCertificate.size
    (c : CauchySequenceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cauchySequenceModels_budgetCertificate_le_size
    (c : CauchySequenceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCauchySequenceModelsBudgetCertificate :
    CauchySequenceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCauchySequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchySequenceModelsBudgetCertificate.controlled,
      sampleCauchySequenceModelsBudgetCertificate]
  · norm_num [CauchySequenceModelsBudgetCertificate.budgetControlled,
      sampleCauchySequenceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCauchySequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchySequenceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCauchySequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchySequenceModelsBudgetCertificate.controlled,
      sampleCauchySequenceModelsBudgetCertificate]
  · norm_num [CauchySequenceModelsBudgetCertificate.budgetControlled,
      sampleCauchySequenceModelsBudgetCertificate]

example :
    sampleCauchySequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchySequenceModelsBudgetCertificate.size := by
  apply cauchySequenceModels_budgetCertificate_le_size
  constructor
  · norm_num [CauchySequenceModelsBudgetCertificate.controlled,
      sampleCauchySequenceModelsBudgetCertificate]
  · norm_num [CauchySequenceModelsBudgetCertificate.budgetControlled,
      sampleCauchySequenceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CauchySequenceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCauchySequenceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCauchySequenceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.CauchySequenceModels
