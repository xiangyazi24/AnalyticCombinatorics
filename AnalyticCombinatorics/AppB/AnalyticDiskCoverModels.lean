import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic disk-cover bookkeeping.

Finite disk covers track the number of charts, a common radius, and overlap
budget.
-/

namespace AnalyticCombinatorics.AppB.AnalyticDiskCoverModels

structure DiskCoverDatum where
  diskCount : ℕ
  radiusBudget : ℕ
  overlapBudget : ℕ
deriving DecidableEq, Repr

def nonemptyDiskCover (d : DiskCoverDatum) : Prop :=
  0 < d.diskCount

def positiveRadiusBudget (d : DiskCoverDatum) : Prop :=
  0 < d.radiusBudget

def diskCoverReady (d : DiskCoverDatum) : Prop :=
  nonemptyDiskCover d ∧ positiveRadiusBudget d

def diskCoverComplexity (d : DiskCoverDatum) : ℕ :=
  d.diskCount * d.radiusBudget + d.overlapBudget

theorem diskCoverReady.radius {d : DiskCoverDatum}
    (h : diskCoverReady d) :
    nonemptyDiskCover d ∧ positiveRadiusBudget d ∧
      d.overlapBudget ≤ diskCoverComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold diskCoverComplexity
  omega

theorem overlapBudget_le_complexity (d : DiskCoverDatum) :
    d.overlapBudget ≤ diskCoverComplexity d := by
  unfold diskCoverComplexity
  omega

def sampleDiskCover : DiskCoverDatum :=
  { diskCount := 4, radiusBudget := 3, overlapBudget := 2 }

example : diskCoverReady sampleDiskCover := by
  norm_num [diskCoverReady, nonemptyDiskCover, positiveRadiusBudget, sampleDiskCover]

example : diskCoverComplexity sampleDiskCover = 14 := by
  native_decide

structure DiskCoverWindow where
  diskWindow : ℕ
  radiusWindow : ℕ
  overlapWindow : ℕ
  coverBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiskCoverWindow.overlapControlled (w : DiskCoverWindow) : Prop :=
  w.overlapWindow ≤ w.diskWindow * w.radiusWindow + w.slack

def diskCoverWindowReady (w : DiskCoverWindow) : Prop :=
  0 < w.diskWindow ∧ 0 < w.radiusWindow ∧ w.overlapControlled ∧
    w.coverBudget ≤ w.diskWindow * w.radiusWindow + w.overlapWindow + w.slack

def DiskCoverWindow.certificate (w : DiskCoverWindow) : ℕ :=
  w.diskWindow * w.radiusWindow + w.overlapWindow + w.coverBudget + w.slack

theorem diskCover_coverBudget_le_certificate (w : DiskCoverWindow) :
    w.coverBudget ≤ w.certificate := by
  unfold DiskCoverWindow.certificate
  omega

def sampleDiskCoverWindow : DiskCoverWindow :=
  { diskWindow := 3, radiusWindow := 4, overlapWindow := 5, coverBudget := 18, slack := 2 }

example : diskCoverWindowReady sampleDiskCoverWindow := by
  norm_num [diskCoverWindowReady, DiskCoverWindow.overlapControlled, sampleDiskCoverWindow]


structure AnalyticDiskCoverModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDiskCoverModelsBudgetCertificate.controlled
    (c : AnalyticDiskCoverModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticDiskCoverModelsBudgetCertificate.budgetControlled
    (c : AnalyticDiskCoverModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticDiskCoverModelsBudgetCertificate.Ready
    (c : AnalyticDiskCoverModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticDiskCoverModelsBudgetCertificate.size
    (c : AnalyticDiskCoverModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticDiskCoverModels_budgetCertificate_le_size
    (c : AnalyticDiskCoverModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticDiskCoverModelsBudgetCertificate :
    AnalyticDiskCoverModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticDiskCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.controlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticDiskCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDiskCoverModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticDiskCoverModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.controlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]

example :
    sampleAnalyticDiskCoverModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDiskCoverModelsBudgetCertificate.size := by
  apply analyticDiskCoverModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.controlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]
  · norm_num [AnalyticDiskCoverModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskCoverModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticDiskCoverModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticDiskCoverModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticDiskCoverModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticDiskCoverModels
