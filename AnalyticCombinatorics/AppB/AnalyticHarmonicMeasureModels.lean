import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic harmonic measure models.

This module records finite bookkeeping for harmonic measure windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticHarmonicMeasureModels

structure HarmonicMeasureData where
  boundaryArcs : ℕ
  measureWindow : ℕ
  harmonicSlack : ℕ
deriving DecidableEq, Repr

def hasBoundaryArcs (d : HarmonicMeasureData) : Prop :=
  0 < d.boundaryArcs

def measureWindowControlled (d : HarmonicMeasureData) : Prop :=
  d.measureWindow ≤ d.boundaryArcs + d.harmonicSlack

def harmonicMeasureReady (d : HarmonicMeasureData) : Prop :=
  hasBoundaryArcs d ∧ measureWindowControlled d

def harmonicMeasureBudget (d : HarmonicMeasureData) : ℕ :=
  d.boundaryArcs + d.measureWindow + d.harmonicSlack

theorem harmonicMeasureReady.hasBoundaryArcs {d : HarmonicMeasureData}
    (h : harmonicMeasureReady d) :
    hasBoundaryArcs d ∧ measureWindowControlled d ∧
      d.measureWindow ≤ harmonicMeasureBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold harmonicMeasureBudget
  omega

theorem measureWindow_le_budget (d : HarmonicMeasureData) :
    d.measureWindow ≤ harmonicMeasureBudget d := by
  unfold harmonicMeasureBudget
  omega

def sampleHarmonicMeasureData : HarmonicMeasureData :=
  { boundaryArcs := 6, measureWindow := 8, harmonicSlack := 3 }

example : harmonicMeasureReady sampleHarmonicMeasureData := by
  norm_num [harmonicMeasureReady, hasBoundaryArcs]
  norm_num [measureWindowControlled, sampleHarmonicMeasureData]

example : harmonicMeasureBudget sampleHarmonicMeasureData = 17 := by
  native_decide

structure HarmonicMeasureWindow where
  arcWindow : ℕ
  measureWindow : ℕ
  harmonicSlack : ℕ
  measureBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HarmonicMeasureWindow.measureControlled (w : HarmonicMeasureWindow) : Prop :=
  w.measureWindow ≤ w.arcWindow + w.harmonicSlack + w.slack

def harmonicMeasureWindowReady (w : HarmonicMeasureWindow) : Prop :=
  0 < w.arcWindow ∧ w.measureControlled ∧
    w.measureBudget ≤ w.arcWindow + w.measureWindow + w.slack

def HarmonicMeasureWindow.certificate (w : HarmonicMeasureWindow) : ℕ :=
  w.arcWindow + w.measureWindow + w.harmonicSlack + w.measureBudget + w.slack

theorem harmonicMeasure_measureBudget_le_certificate (w : HarmonicMeasureWindow) :
    w.measureBudget ≤ w.certificate := by
  unfold HarmonicMeasureWindow.certificate
  omega

def sampleHarmonicMeasureWindow : HarmonicMeasureWindow :=
  { arcWindow := 5, measureWindow := 7, harmonicSlack := 2, measureBudget := 14, slack := 2 }

example : harmonicMeasureWindowReady sampleHarmonicMeasureWindow := by
  norm_num [harmonicMeasureWindowReady, HarmonicMeasureWindow.measureControlled,
    sampleHarmonicMeasureWindow]


structure AnalyticHarmonicMeasureModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticHarmonicMeasureModelsBudgetCertificate.controlled
    (c : AnalyticHarmonicMeasureModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticHarmonicMeasureModelsBudgetCertificate.budgetControlled
    (c : AnalyticHarmonicMeasureModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticHarmonicMeasureModelsBudgetCertificate.Ready
    (c : AnalyticHarmonicMeasureModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticHarmonicMeasureModelsBudgetCertificate.size
    (c : AnalyticHarmonicMeasureModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticHarmonicMeasureModels_budgetCertificate_le_size
    (c : AnalyticHarmonicMeasureModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticHarmonicMeasureModelsBudgetCertificate :
    AnalyticHarmonicMeasureModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticHarmonicMeasureModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.controlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.budgetControlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticHarmonicMeasureModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticHarmonicMeasureModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.controlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.budgetControlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]

example :
    sampleAnalyticHarmonicMeasureModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate.size := by
  apply analyticHarmonicMeasureModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.controlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]
  · norm_num [AnalyticHarmonicMeasureModelsBudgetCertificate.budgetControlled,
      sampleAnalyticHarmonicMeasureModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticHarmonicMeasureModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticHarmonicMeasureModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticHarmonicMeasureModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticHarmonicMeasureModels
