import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Percolation limit schema bookkeeping.

The finite data records threshold numerator/denominator and cluster budget
for random structure limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PercolationLimitSchemas

structure PercolationData where
  thresholdNumerator : ℕ
  thresholdDenominator : ℕ
  clusterBudget : ℕ
deriving DecidableEq, Repr

def positiveThresholdDenominator (d : PercolationData) : Prop :=
  0 < d.thresholdDenominator

def thresholdWithinUnit (d : PercolationData) : Prop :=
  d.thresholdNumerator ≤ d.thresholdDenominator

def percolationReady (d : PercolationData) : Prop :=
  positiveThresholdDenominator d ∧ thresholdWithinUnit d

def percolationBudget (d : PercolationData) : ℕ :=
  d.thresholdNumerator + d.thresholdDenominator + d.clusterBudget

theorem percolationReady.threshold {d : PercolationData}
    (h : percolationReady d) :
    thresholdWithinUnit d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem thresholdNumerator_le_budget (d : PercolationData) :
    d.thresholdNumerator ≤ percolationBudget d := by
  unfold percolationBudget
  omega

def samplePercolation : PercolationData :=
  { thresholdNumerator := 2, thresholdDenominator := 5, clusterBudget := 7 }

example : percolationReady samplePercolation := by
  norm_num [percolationReady, positiveThresholdDenominator, thresholdWithinUnit, samplePercolation]

example : percolationBudget samplePercolation = 14 := by
  native_decide

/-- Finite executable readiness audit for percolation limit data. -/
def percolationDataListReady
    (data : List PercolationData) : Bool :=
  data.all fun d =>
    0 < d.thresholdDenominator &&
      d.thresholdNumerator ≤ d.thresholdDenominator

theorem percolationDataList_readyWindow :
    percolationDataListReady
      [{ thresholdNumerator := 1, thresholdDenominator := 3, clusterBudget := 5 },
       { thresholdNumerator := 2, thresholdDenominator := 5, clusterBudget := 7 }] =
      true := by
  unfold percolationDataListReady
  native_decide

structure PercolationWindow where
  thresholdNumerator : ℕ
  thresholdDenominator : ℕ
  clusterBudget : ℕ
  crossingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PercolationWindow.thresholdControlled (w : PercolationWindow) : Prop :=
  w.thresholdNumerator ≤ w.thresholdDenominator

def PercolationWindow.crossingControlled (w : PercolationWindow) : Prop :=
  w.crossingBudget ≤ w.thresholdDenominator + w.clusterBudget + w.slack

def percolationWindowReady (w : PercolationWindow) : Prop :=
  0 < w.thresholdDenominator ∧
    w.thresholdControlled ∧
    w.crossingControlled

def PercolationWindow.certificate (w : PercolationWindow) : ℕ :=
  w.thresholdDenominator + w.clusterBudget + w.slack

theorem percolation_crossingBudget_le_certificate {w : PercolationWindow}
    (h : percolationWindowReady w) :
    w.crossingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcross⟩
  exact hcross

def samplePercolationWindow : PercolationWindow :=
  { thresholdNumerator := 2, thresholdDenominator := 5, clusterBudget := 7, crossingBudget := 10,
    slack := 0 }

example : percolationWindowReady samplePercolationWindow := by
  norm_num [percolationWindowReady, PercolationWindow.thresholdControlled,
    PercolationWindow.crossingControlled, samplePercolationWindow]

example : samplePercolationWindow.certificate = 12 := by
  native_decide


structure PercolationLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PercolationLimitSchemasBudgetCertificate.controlled
    (c : PercolationLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PercolationLimitSchemasBudgetCertificate.budgetControlled
    (c : PercolationLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PercolationLimitSchemasBudgetCertificate.Ready
    (c : PercolationLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PercolationLimitSchemasBudgetCertificate.size
    (c : PercolationLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem percolationLimitSchemas_budgetCertificate_le_size
    (c : PercolationLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePercolationLimitSchemasBudgetCertificate :
    PercolationLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePercolationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PercolationLimitSchemasBudgetCertificate.controlled,
      samplePercolationLimitSchemasBudgetCertificate]
  · norm_num [PercolationLimitSchemasBudgetCertificate.budgetControlled,
      samplePercolationLimitSchemasBudgetCertificate]

example :
    samplePercolationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePercolationLimitSchemasBudgetCertificate.size := by
  apply percolationLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PercolationLimitSchemasBudgetCertificate.controlled,
      samplePercolationLimitSchemasBudgetCertificate]
  · norm_num [PercolationLimitSchemasBudgetCertificate.budgetControlled,
      samplePercolationLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePercolationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PercolationLimitSchemasBudgetCertificate.controlled,
      samplePercolationLimitSchemasBudgetCertificate]
  · norm_num [PercolationLimitSchemasBudgetCertificate.budgetControlled,
      samplePercolationLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePercolationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePercolationLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PercolationLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePercolationLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePercolationLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.PercolationLimitSchemas
