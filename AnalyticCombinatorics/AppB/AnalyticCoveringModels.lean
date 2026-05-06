import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic covering models.

The schema tracks chart count, overlap count, and radius budget for
finite analytic coverings.
-/

namespace AnalyticCombinatorics.AppB.AnalyticCoveringModels

structure AnalyticCoveringData where
  chartCount : ℕ
  overlapCount : ℕ
  radiusBudget : ℕ
deriving DecidableEq, Repr

def chartsNonempty (d : AnalyticCoveringData) : Prop :=
  0 < d.chartCount

def overlapsControlled (d : AnalyticCoveringData) : Prop :=
  d.overlapCount ≤ d.chartCount + d.radiusBudget

def analyticCoveringReady (d : AnalyticCoveringData) : Prop :=
  chartsNonempty d ∧ overlapsControlled d

def analyticCoveringBudget (d : AnalyticCoveringData) : ℕ :=
  d.chartCount + d.overlapCount + d.radiusBudget

theorem analyticCoveringReady.charts {d : AnalyticCoveringData}
    (h : analyticCoveringReady d) :
    chartsNonempty d ∧ overlapsControlled d ∧ d.overlapCount ≤ analyticCoveringBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticCoveringBudget
  omega

theorem overlapCount_le_coveringBudget (d : AnalyticCoveringData) :
    d.overlapCount ≤ analyticCoveringBudget d := by
  unfold analyticCoveringBudget
  omega

def sampleAnalyticCoveringData : AnalyticCoveringData :=
  { chartCount := 5, overlapCount := 7, radiusBudget := 4 }

example : analyticCoveringReady sampleAnalyticCoveringData := by
  norm_num [analyticCoveringReady, chartsNonempty]
  norm_num [overlapsControlled, sampleAnalyticCoveringData]

example : analyticCoveringBudget sampleAnalyticCoveringData = 16 := by
  native_decide

structure AnalyticCoveringWindow where
  chartWindow : ℕ
  overlapWindow : ℕ
  radiusSlack : ℕ
  coverBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCoveringWindow.overlapControlled (w : AnalyticCoveringWindow) : Prop :=
  w.overlapWindow ≤ w.chartWindow + w.radiusSlack + w.slack

def analyticCoveringWindowReady (w : AnalyticCoveringWindow) : Prop :=
  0 < w.chartWindow ∧ w.overlapControlled ∧
    w.coverBudget ≤ w.chartWindow + w.overlapWindow + w.slack

def AnalyticCoveringWindow.certificate (w : AnalyticCoveringWindow) : ℕ :=
  w.chartWindow + w.overlapWindow + w.radiusSlack + w.coverBudget + w.slack

theorem analyticCovering_coverBudget_le_certificate (w : AnalyticCoveringWindow) :
    w.coverBudget ≤ w.certificate := by
  unfold AnalyticCoveringWindow.certificate
  omega

def sampleAnalyticCoveringWindow : AnalyticCoveringWindow :=
  { chartWindow := 4, overlapWindow := 6, radiusSlack := 2, coverBudget := 11, slack := 2 }

example : analyticCoveringWindowReady sampleAnalyticCoveringWindow := by
  norm_num [analyticCoveringWindowReady, AnalyticCoveringWindow.overlapControlled,
    sampleAnalyticCoveringWindow]


structure AnalyticCoveringModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCoveringModelsBudgetCertificate.controlled
    (c : AnalyticCoveringModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticCoveringModelsBudgetCertificate.budgetControlled
    (c : AnalyticCoveringModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticCoveringModelsBudgetCertificate.Ready
    (c : AnalyticCoveringModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticCoveringModelsBudgetCertificate.size
    (c : AnalyticCoveringModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticCoveringModels_budgetCertificate_le_size
    (c : AnalyticCoveringModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticCoveringModelsBudgetCertificate :
    AnalyticCoveringModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticCoveringModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCoveringModelsBudgetCertificate.controlled,
      sampleAnalyticCoveringModelsBudgetCertificate]
  · norm_num [AnalyticCoveringModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoveringModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticCoveringModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCoveringModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticCoveringModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCoveringModelsBudgetCertificate.controlled,
      sampleAnalyticCoveringModelsBudgetCertificate]
  · norm_num [AnalyticCoveringModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoveringModelsBudgetCertificate]

example :
    sampleAnalyticCoveringModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCoveringModelsBudgetCertificate.size := by
  apply analyticCoveringModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticCoveringModelsBudgetCertificate.controlled,
      sampleAnalyticCoveringModelsBudgetCertificate]
  · norm_num [AnalyticCoveringModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoveringModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticCoveringModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticCoveringModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticCoveringModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticCoveringModels
