import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Cauchy coefficient schemas.

This module records finite bookkeeping for Cauchy coefficient bounds.
-/

namespace AnalyticCombinatorics.PartB.Ch4.UniformCauchyCoefficientSchemas

structure CauchyCoefficientData where
  contourRadius : ℕ
  coefficientDepth : ℕ
  cauchySlack : ℕ
deriving DecidableEq, Repr

def hasContourRadius (d : CauchyCoefficientData) : Prop :=
  0 < d.contourRadius

def coefficientDepthControlled (d : CauchyCoefficientData) : Prop :=
  d.coefficientDepth ≤ d.contourRadius + d.cauchySlack

def cauchyCoefficientReady (d : CauchyCoefficientData) : Prop :=
  hasContourRadius d ∧ coefficientDepthControlled d

def cauchyCoefficientBudget (d : CauchyCoefficientData) : ℕ :=
  d.contourRadius + d.coefficientDepth + d.cauchySlack

theorem cauchyCoefficientReady.hasContourRadius
    {d : CauchyCoefficientData}
    (h : cauchyCoefficientReady d) :
    hasContourRadius d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem coefficientDepth_le_budget (d : CauchyCoefficientData) :
    d.coefficientDepth ≤ cauchyCoefficientBudget d := by
  unfold cauchyCoefficientBudget
  omega

def sampleCauchyCoefficientData : CauchyCoefficientData :=
  { contourRadius := 6, coefficientDepth := 8, cauchySlack := 3 }

example : cauchyCoefficientReady sampleCauchyCoefficientData := by
  norm_num [cauchyCoefficientReady, hasContourRadius]
  norm_num [coefficientDepthControlled, sampleCauchyCoefficientData]

example : cauchyCoefficientBudget sampleCauchyCoefficientData = 17 := by
  native_decide

structure UniformCauchyCoefficientBudgetCertificate where
  contourWindow : ℕ
  coefficientWindow : ℕ
  cauchySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCauchyCoefficientBudgetCertificate.controlled
    (c : UniformCauchyCoefficientBudgetCertificate) : Prop :=
  0 < c.contourWindow ∧
    c.coefficientWindow ≤ c.contourWindow + c.cauchySlackWindow + c.slack

def UniformCauchyCoefficientBudgetCertificate.budgetControlled
    (c : UniformCauchyCoefficientBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.contourWindow + c.coefficientWindow + c.cauchySlackWindow + c.slack

def UniformCauchyCoefficientBudgetCertificate.Ready
    (c : UniformCauchyCoefficientBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformCauchyCoefficientBudgetCertificate.size
    (c : UniformCauchyCoefficientBudgetCertificate) : ℕ :=
  c.contourWindow + c.coefficientWindow + c.cauchySlackWindow + c.slack

theorem uniformCauchyCoefficient_budgetCertificate_le_size
    (c : UniformCauchyCoefficientBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCauchyCoefficientBudgetCertificate :
    UniformCauchyCoefficientBudgetCertificate :=
  { contourWindow := 6
    coefficientWindow := 8
    cauchySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformCauchyCoefficientBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyCoefficientBudgetCertificate.controlled,
      sampleUniformCauchyCoefficientBudgetCertificate]
  · norm_num [UniformCauchyCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCauchyCoefficientBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformCauchyCoefficientBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyCoefficientBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformCauchyCoefficientBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyCoefficientBudgetCertificate.controlled,
      sampleUniformCauchyCoefficientBudgetCertificate]
  · norm_num [UniformCauchyCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCauchyCoefficientBudgetCertificate]

example :
    sampleUniformCauchyCoefficientBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyCoefficientBudgetCertificate.size := by
  apply uniformCauchyCoefficient_budgetCertificate_le_size
  constructor
  · norm_num [UniformCauchyCoefficientBudgetCertificate.controlled,
      sampleUniformCauchyCoefficientBudgetCertificate]
  · norm_num [UniformCauchyCoefficientBudgetCertificate.budgetControlled,
      sampleUniformCauchyCoefficientBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformCauchyCoefficientBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleUniformCauchyCoefficientBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleUniformCauchyCoefficientBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.UniformCauchyCoefficientSchemas
