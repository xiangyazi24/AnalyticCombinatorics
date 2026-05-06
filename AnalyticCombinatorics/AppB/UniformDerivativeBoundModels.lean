import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform derivative bound models.

The finite abstraction records derivative order, norm scale, and radius
slack.
-/

namespace AnalyticCombinatorics.AppB.UniformDerivativeBoundModels

structure UniformDerivativeBoundData where
  derivativeOrder : ℕ
  normScale : ℕ
  radiusSlack : ℕ
deriving DecidableEq, Repr

def normScalePositive (d : UniformDerivativeBoundData) : Prop :=
  0 < d.normScale

def derivativeOrderControlled (d : UniformDerivativeBoundData) : Prop :=
  d.derivativeOrder ≤ d.normScale + d.radiusSlack

def uniformDerivativeBoundReady (d : UniformDerivativeBoundData) : Prop :=
  normScalePositive d ∧ derivativeOrderControlled d

def uniformDerivativeBoundBudget (d : UniformDerivativeBoundData) : ℕ :=
  d.derivativeOrder + d.normScale + d.radiusSlack

theorem uniformDerivativeBoundReady.norm {d : UniformDerivativeBoundData}
    (h : uniformDerivativeBoundReady d) :
    normScalePositive d ∧ derivativeOrderControlled d ∧
      d.derivativeOrder ≤ uniformDerivativeBoundBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformDerivativeBoundBudget
  omega

theorem derivativeOrder_le_derivativeBoundBudget
    (d : UniformDerivativeBoundData) :
    d.derivativeOrder ≤ uniformDerivativeBoundBudget d := by
  unfold uniformDerivativeBoundBudget
  omega

def sampleUniformDerivativeBoundData : UniformDerivativeBoundData :=
  { derivativeOrder := 7, normScale := 5, radiusSlack := 3 }

example : uniformDerivativeBoundReady sampleUniformDerivativeBoundData := by
  norm_num [uniformDerivativeBoundReady, normScalePositive]
  norm_num [derivativeOrderControlled, sampleUniformDerivativeBoundData]

example : uniformDerivativeBoundBudget sampleUniformDerivativeBoundData = 15 := by
  native_decide


structure UniformDerivativeBoundModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDerivativeBoundModelsBudgetCertificate.controlled
    (c : UniformDerivativeBoundModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformDerivativeBoundModelsBudgetCertificate.budgetControlled
    (c : UniformDerivativeBoundModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformDerivativeBoundModelsBudgetCertificate.Ready
    (c : UniformDerivativeBoundModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformDerivativeBoundModelsBudgetCertificate.size
    (c : UniformDerivativeBoundModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformDerivativeBoundModels_budgetCertificate_le_size
    (c : UniformDerivativeBoundModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformDerivativeBoundModelsBudgetCertificate :
    UniformDerivativeBoundModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformDerivativeBoundModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.controlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.budgetControlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformDerivativeBoundModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDerivativeBoundModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformDerivativeBoundModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.controlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.budgetControlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]

example :
    sampleUniformDerivativeBoundModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDerivativeBoundModelsBudgetCertificate.size := by
  apply uniformDerivativeBoundModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.controlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]
  · norm_num [UniformDerivativeBoundModelsBudgetCertificate.budgetControlled,
      sampleUniformDerivativeBoundModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformDerivativeBoundModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformDerivativeBoundModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformDerivativeBoundModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformDerivativeBoundModels
