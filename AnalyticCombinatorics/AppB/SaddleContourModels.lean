import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle contour models.

The finite abstraction records contour arcs, descent margin, and error
budget for saddle-contour bookkeeping.
-/

namespace AnalyticCombinatorics.AppB.SaddleContourModels

structure SaddleContourData where
  contourArcs : ℕ
  descentMargin : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def descentMarginPositive (d : SaddleContourData) : Prop :=
  0 < d.descentMargin

def arcsControlled (d : SaddleContourData) : Prop :=
  d.contourArcs ≤ d.descentMargin + d.errorBudget

def saddleContourReady (d : SaddleContourData) : Prop :=
  descentMarginPositive d ∧ arcsControlled d

def saddleContourBudget (d : SaddleContourData) : ℕ :=
  d.contourArcs + d.descentMargin + d.errorBudget

theorem saddleContourReady.margin {d : SaddleContourData}
    (h : saddleContourReady d) :
    descentMarginPositive d ∧ arcsControlled d ∧
      d.contourArcs ≤ saddleContourBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleContourBudget
  omega

theorem contourArcs_le_saddleContourBudget (d : SaddleContourData) :
    d.contourArcs ≤ saddleContourBudget d := by
  unfold saddleContourBudget
  omega

def sampleSaddleContourData : SaddleContourData :=
  { contourArcs := 6, descentMargin := 4, errorBudget := 3 }

example : saddleContourReady sampleSaddleContourData := by
  norm_num [saddleContourReady, descentMarginPositive]
  norm_num [arcsControlled, sampleSaddleContourData]

example : saddleContourBudget sampleSaddleContourData = 13 := by
  native_decide

/-- Finite executable readiness audit for saddle-contour windows. -/
def saddleContourListReady (windows : List SaddleContourData) : Bool :=
  windows.all fun d =>
    0 < d.descentMargin && d.contourArcs ≤ d.descentMargin + d.errorBudget

theorem saddleContourList_readyWindow :
    saddleContourListReady
      [{ contourArcs := 4, descentMargin := 3, errorBudget := 1 },
       { contourArcs := 6, descentMargin := 4, errorBudget := 3 }] = true := by
  unfold saddleContourListReady
  native_decide


structure SaddleContourModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleContourModelsBudgetCertificate.controlled
    (c : SaddleContourModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SaddleContourModelsBudgetCertificate.budgetControlled
    (c : SaddleContourModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SaddleContourModelsBudgetCertificate.Ready
    (c : SaddleContourModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleContourModelsBudgetCertificate.size
    (c : SaddleContourModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem saddleContourModels_budgetCertificate_le_size
    (c : SaddleContourModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleContourModelsBudgetCertificate :
    SaddleContourModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSaddleContourModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleContourModelsBudgetCertificate.controlled,
      sampleSaddleContourModelsBudgetCertificate]
  · norm_num [SaddleContourModelsBudgetCertificate.budgetControlled,
      sampleSaddleContourModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleContourModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleContourModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSaddleContourModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleContourModelsBudgetCertificate.controlled,
      sampleSaddleContourModelsBudgetCertificate]
  · norm_num [SaddleContourModelsBudgetCertificate.budgetControlled,
      sampleSaddleContourModelsBudgetCertificate]

example :
    sampleSaddleContourModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleContourModelsBudgetCertificate.size := by
  apply saddleContourModels_budgetCertificate_le_size
  constructor
  · norm_num [SaddleContourModelsBudgetCertificate.controlled,
      sampleSaddleContourModelsBudgetCertificate]
  · norm_num [SaddleContourModelsBudgetCertificate.budgetControlled,
      sampleSaddleContourModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SaddleContourModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleContourModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddleContourModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.SaddleContourModels
