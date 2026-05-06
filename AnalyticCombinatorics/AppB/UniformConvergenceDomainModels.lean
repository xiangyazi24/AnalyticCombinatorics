import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform convergence domain models.

The schema records compact count, convergence rate, and boundary slack
for finite uniform-convergence checks.
-/

namespace AnalyticCombinatorics.AppB.UniformConvergenceDomainModels

structure UniformConvergenceDomainData where
  compactCount : ℕ
  convergenceRate : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def compactCountPositive (d : UniformConvergenceDomainData) : Prop :=
  0 < d.compactCount

def rateControlled (d : UniformConvergenceDomainData) : Prop :=
  d.convergenceRate ≤ d.compactCount + d.boundarySlack

def uniformConvergenceDomainReady
    (d : UniformConvergenceDomainData) : Prop :=
  compactCountPositive d ∧ rateControlled d

def uniformConvergenceDomainBudget
    (d : UniformConvergenceDomainData) : ℕ :=
  d.compactCount + d.convergenceRate + d.boundarySlack

theorem uniformConvergenceDomainReady.compact
    {d : UniformConvergenceDomainData}
    (h : uniformConvergenceDomainReady d) :
    compactCountPositive d ∧ rateControlled d ∧
      d.convergenceRate ≤ uniformConvergenceDomainBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformConvergenceDomainBudget
  omega

theorem convergenceRate_le_domainBudget
    (d : UniformConvergenceDomainData) :
    d.convergenceRate ≤ uniformConvergenceDomainBudget d := by
  unfold uniformConvergenceDomainBudget
  omega

def sampleUniformConvergenceDomainData :
    UniformConvergenceDomainData :=
  { compactCount := 6, convergenceRate := 8, boundarySlack := 3 }

example :
    uniformConvergenceDomainReady sampleUniformConvergenceDomainData := by
  norm_num [uniformConvergenceDomainReady, compactCountPositive]
  norm_num [rateControlled, sampleUniformConvergenceDomainData]

example :
    uniformConvergenceDomainBudget sampleUniformConvergenceDomainData = 17 := by
  native_decide


structure UniformConvergenceDomainModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformConvergenceDomainModelsBudgetCertificate.controlled
    (c : UniformConvergenceDomainModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformConvergenceDomainModelsBudgetCertificate.budgetControlled
    (c : UniformConvergenceDomainModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformConvergenceDomainModelsBudgetCertificate.Ready
    (c : UniformConvergenceDomainModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformConvergenceDomainModelsBudgetCertificate.size
    (c : UniformConvergenceDomainModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformConvergenceDomainModels_budgetCertificate_le_size
    (c : UniformConvergenceDomainModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformConvergenceDomainModelsBudgetCertificate :
    UniformConvergenceDomainModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformConvergenceDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.controlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.budgetControlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformConvergenceDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformConvergenceDomainModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformConvergenceDomainModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.controlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.budgetControlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]

example :
    sampleUniformConvergenceDomainModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformConvergenceDomainModelsBudgetCertificate.size := by
  apply uniformConvergenceDomainModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.controlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]
  · norm_num [UniformConvergenceDomainModelsBudgetCertificate.budgetControlled,
      sampleUniformConvergenceDomainModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformConvergenceDomainModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformConvergenceDomainModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformConvergenceDomainModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformConvergenceDomainModels
