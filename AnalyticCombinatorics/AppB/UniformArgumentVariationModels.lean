import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform argument variation models.

This module records finite bookkeeping for argument variation windows.
-/

namespace AnalyticCombinatorics.AppB.UniformArgumentVariationModels

structure ArgumentVariationData where
  contourSegments : ℕ
  variationWindow : ℕ
  argumentSlack : ℕ
deriving DecidableEq, Repr

def hasContourSegments (d : ArgumentVariationData) : Prop :=
  0 < d.contourSegments

def variationWindowControlled (d : ArgumentVariationData) : Prop :=
  d.variationWindow ≤ d.contourSegments + d.argumentSlack

def argumentVariationReady (d : ArgumentVariationData) : Prop :=
  hasContourSegments d ∧ variationWindowControlled d

def argumentVariationBudget (d : ArgumentVariationData) : ℕ :=
  d.contourSegments + d.variationWindow + d.argumentSlack

theorem argumentVariationReady.hasContourSegments
    {d : ArgumentVariationData}
    (h : argumentVariationReady d) :
    hasContourSegments d ∧ variationWindowControlled d ∧
      d.variationWindow ≤ argumentVariationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold argumentVariationBudget
  omega

theorem variationWindow_le_budget (d : ArgumentVariationData) :
    d.variationWindow ≤ argumentVariationBudget d := by
  unfold argumentVariationBudget
  omega

def sampleArgumentVariationData : ArgumentVariationData :=
  { contourSegments := 5, variationWindow := 7, argumentSlack := 2 }

example : argumentVariationReady sampleArgumentVariationData := by
  norm_num [argumentVariationReady, hasContourSegments]
  norm_num [variationWindowControlled, sampleArgumentVariationData]

example : argumentVariationBudget sampleArgumentVariationData = 14 := by
  native_decide

/-- Finite executable readiness audit for argument-variation windows. -/
def argumentVariationListReady (windows : List ArgumentVariationData) : Bool :=
  windows.all fun d =>
    0 < d.contourSegments &&
      d.variationWindow ≤ d.contourSegments + d.argumentSlack

theorem argumentVariationList_readyWindow :
    argumentVariationListReady
      [{ contourSegments := 3, variationWindow := 4, argumentSlack := 1 },
       { contourSegments := 5, variationWindow := 7, argumentSlack := 2 }] = true := by
  unfold argumentVariationListReady
  native_decide


structure UniformArgumentVariationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformArgumentVariationModelsBudgetCertificate.controlled
    (c : UniformArgumentVariationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformArgumentVariationModelsBudgetCertificate.budgetControlled
    (c : UniformArgumentVariationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformArgumentVariationModelsBudgetCertificate.Ready
    (c : UniformArgumentVariationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformArgumentVariationModelsBudgetCertificate.size
    (c : UniformArgumentVariationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformArgumentVariationModels_budgetCertificate_le_size
    (c : UniformArgumentVariationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformArgumentVariationModelsBudgetCertificate :
    UniformArgumentVariationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformArgumentVariationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.controlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformArgumentVariationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformArgumentVariationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformArgumentVariationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.controlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]

example :
    sampleUniformArgumentVariationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformArgumentVariationModelsBudgetCertificate.size := by
  apply uniformArgumentVariationModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.controlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]
  · norm_num [UniformArgumentVariationModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentVariationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformArgumentVariationModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformArgumentVariationModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformArgumentVariationModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformArgumentVariationModels
