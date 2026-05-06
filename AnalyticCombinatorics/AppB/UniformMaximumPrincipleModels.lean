import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform maximum principle models.

The finite schema records boundary samples, interior samples, and
comparison slack.
-/

namespace AnalyticCombinatorics.AppB.UniformMaximumPrincipleModels

structure UniformMaximumPrincipleData where
  boundarySamples : ℕ
  interiorSamples : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def boundarySamplesPositive (d : UniformMaximumPrincipleData) : Prop :=
  0 < d.boundarySamples

def interiorSamplesControlled (d : UniformMaximumPrincipleData) : Prop :=
  d.interiorSamples ≤ d.boundarySamples + d.comparisonSlack

def uniformMaximumPrincipleReady
    (d : UniformMaximumPrincipleData) : Prop :=
  boundarySamplesPositive d ∧ interiorSamplesControlled d

def uniformMaximumPrincipleBudget
    (d : UniformMaximumPrincipleData) : ℕ :=
  d.boundarySamples + d.interiorSamples + d.comparisonSlack

theorem uniformMaximumPrincipleReady.boundary
    {d : UniformMaximumPrincipleData}
    (h : uniformMaximumPrincipleReady d) :
    boundarySamplesPositive d ∧ interiorSamplesControlled d ∧
      d.interiorSamples ≤ uniformMaximumPrincipleBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformMaximumPrincipleBudget
  omega

theorem interiorSamples_le_maximumPrincipleBudget
    (d : UniformMaximumPrincipleData) :
    d.interiorSamples ≤ uniformMaximumPrincipleBudget d := by
  unfold uniformMaximumPrincipleBudget
  omega

def sampleUniformMaximumPrincipleData : UniformMaximumPrincipleData :=
  { boundarySamples := 7, interiorSamples := 9, comparisonSlack := 3 }

example : uniformMaximumPrincipleReady sampleUniformMaximumPrincipleData := by
  norm_num [uniformMaximumPrincipleReady, boundarySamplesPositive]
  norm_num [interiorSamplesControlled, sampleUniformMaximumPrincipleData]

example :
    uniformMaximumPrincipleBudget sampleUniformMaximumPrincipleData = 19 := by
  native_decide


structure UniformMaximumPrincipleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformMaximumPrincipleModelsBudgetCertificate.controlled
    (c : UniformMaximumPrincipleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformMaximumPrincipleModelsBudgetCertificate.budgetControlled
    (c : UniformMaximumPrincipleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformMaximumPrincipleModelsBudgetCertificate.Ready
    (c : UniformMaximumPrincipleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformMaximumPrincipleModelsBudgetCertificate.size
    (c : UniformMaximumPrincipleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformMaximumPrincipleModels_budgetCertificate_le_size
    (c : UniformMaximumPrincipleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformMaximumPrincipleModelsBudgetCertificate :
    UniformMaximumPrincipleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformMaximumPrincipleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.controlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.budgetControlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformMaximumPrincipleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMaximumPrincipleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformMaximumPrincipleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.controlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.budgetControlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]

example :
    sampleUniformMaximumPrincipleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformMaximumPrincipleModelsBudgetCertificate.size := by
  apply uniformMaximumPrincipleModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.controlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]
  · norm_num [UniformMaximumPrincipleModelsBudgetCertificate.budgetControlled,
      sampleUniformMaximumPrincipleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformMaximumPrincipleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformMaximumPrincipleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformMaximumPrincipleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformMaximumPrincipleModels
