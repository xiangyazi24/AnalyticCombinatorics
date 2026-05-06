import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform harmonic measure window models.

This module records finite bookkeeping for harmonic measure windows.
-/

namespace AnalyticCombinatorics.AppB.UniformHarmonicMeasureWindowModels

structure HarmonicMeasureWindowData where
  boundaryArcs : ℕ
  measureWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasBoundaryArcs (d : HarmonicMeasureWindowData) : Prop :=
  0 < d.boundaryArcs

def measureWindowControlled
    (d : HarmonicMeasureWindowData) : Prop :=
  d.measureWindow ≤ d.boundaryArcs + d.boundarySlack

def harmonicMeasureWindowReady
    (d : HarmonicMeasureWindowData) : Prop :=
  hasBoundaryArcs d ∧ measureWindowControlled d

def harmonicMeasureWindowBudget
    (d : HarmonicMeasureWindowData) : ℕ :=
  d.boundaryArcs + d.measureWindow + d.boundarySlack

theorem harmonicMeasureWindowReady.hasBoundaryArcs
    {d : HarmonicMeasureWindowData}
    (h : harmonicMeasureWindowReady d) :
    hasBoundaryArcs d ∧ measureWindowControlled d ∧
      d.measureWindow ≤ harmonicMeasureWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold harmonicMeasureWindowBudget
  omega

theorem measureWindow_le_budget (d : HarmonicMeasureWindowData) :
    d.measureWindow ≤ harmonicMeasureWindowBudget d := by
  unfold harmonicMeasureWindowBudget
  omega

def sampleHarmonicMeasureWindowData : HarmonicMeasureWindowData :=
  { boundaryArcs := 6, measureWindow := 8, boundarySlack := 3 }

example : harmonicMeasureWindowReady sampleHarmonicMeasureWindowData := by
  norm_num [harmonicMeasureWindowReady, hasBoundaryArcs]
  norm_num [measureWindowControlled, sampleHarmonicMeasureWindowData]

example : harmonicMeasureWindowBudget sampleHarmonicMeasureWindowData = 17 := by
  native_decide


structure UniformHarmonicMeasureWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformHarmonicMeasureWindowModelsBudgetCertificate.controlled
    (c : UniformHarmonicMeasureWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformHarmonicMeasureWindowModelsBudgetCertificate.budgetControlled
    (c : UniformHarmonicMeasureWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformHarmonicMeasureWindowModelsBudgetCertificate.Ready
    (c : UniformHarmonicMeasureWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformHarmonicMeasureWindowModelsBudgetCertificate.size
    (c : UniformHarmonicMeasureWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformHarmonicMeasureWindowModels_budgetCertificate_le_size
    (c : UniformHarmonicMeasureWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformHarmonicMeasureWindowModelsBudgetCertificate :
    UniformHarmonicMeasureWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.controlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.controlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]

example :
    sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate.size := by
  apply uniformHarmonicMeasureWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.controlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]
  · norm_num [UniformHarmonicMeasureWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformHarmonicMeasureWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformHarmonicMeasureWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformHarmonicMeasureWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformHarmonicMeasureWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformHarmonicMeasureWindowModels
