import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Gaussian saddle remainder schemas.

This module records finite bookkeeping for Gaussian saddle remainders.
-/

namespace AnalyticCombinatorics.PartB.Ch8.UniformGaussianSaddleRemainderSchemas

structure GaussianSaddleRemainderData where
  gaussianScale : ℕ
  remainderWindow : ℕ
  saddleSlack : ℕ
deriving DecidableEq, Repr

def hasGaussianScale (d : GaussianSaddleRemainderData) : Prop :=
  0 < d.gaussianScale

def remainderWindowControlled (d : GaussianSaddleRemainderData) : Prop :=
  d.remainderWindow ≤ d.gaussianScale + d.saddleSlack

def gaussianSaddleRemainderReady
    (d : GaussianSaddleRemainderData) : Prop :=
  hasGaussianScale d ∧ remainderWindowControlled d

def gaussianSaddleRemainderBudget
    (d : GaussianSaddleRemainderData) : ℕ :=
  d.gaussianScale + d.remainderWindow + d.saddleSlack

theorem gaussianSaddleRemainderReady.hasGaussianScale
    {d : GaussianSaddleRemainderData}
    (h : gaussianSaddleRemainderReady d) :
    hasGaussianScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : GaussianSaddleRemainderData) :
    d.remainderWindow ≤ gaussianSaddleRemainderBudget d := by
  unfold gaussianSaddleRemainderBudget
  omega

def sampleGaussianSaddleRemainderData : GaussianSaddleRemainderData :=
  { gaussianScale := 6, remainderWindow := 8, saddleSlack := 3 }

example : gaussianSaddleRemainderReady
    sampleGaussianSaddleRemainderData := by
  norm_num [gaussianSaddleRemainderReady, hasGaussianScale]
  norm_num [remainderWindowControlled, sampleGaussianSaddleRemainderData]

example :
    gaussianSaddleRemainderBudget sampleGaussianSaddleRemainderData = 17 := by
  native_decide


structure UniformGaussianSaddleRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformGaussianSaddleRemainderSchemasBudgetCertificate.controlled
    (c : UniformGaussianSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformGaussianSaddleRemainderSchemasBudgetCertificate.budgetControlled
    (c : UniformGaussianSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformGaussianSaddleRemainderSchemasBudgetCertificate.Ready
    (c : UniformGaussianSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformGaussianSaddleRemainderSchemasBudgetCertificate.size
    (c : UniformGaussianSaddleRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformGaussianSaddleRemainderSchemas_budgetCertificate_le_size
    (c : UniformGaussianSaddleRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate :
    UniformGaussianSaddleRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]

example :
    sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate.size := by
  apply uniformGaussianSaddleRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformGaussianSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformGaussianSaddleRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformGaussianSaddleRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.UniformGaussianSaddleRemainderSchemas

