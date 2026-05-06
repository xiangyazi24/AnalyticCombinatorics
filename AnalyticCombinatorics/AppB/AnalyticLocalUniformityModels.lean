import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic local uniformity models.

The finite abstraction records neighborhoods, uniformity checks, and
boundary slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticLocalUniformityModels

structure AnalyticLocalUniformityData where
  neighborhoods : ℕ
  uniformityChecks : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def neighborhoodsPositive (d : AnalyticLocalUniformityData) : Prop :=
  0 < d.neighborhoods

def checksControlled (d : AnalyticLocalUniformityData) : Prop :=
  d.uniformityChecks ≤ d.neighborhoods + d.boundarySlack

def analyticLocalUniformityReady
    (d : AnalyticLocalUniformityData) : Prop :=
  neighborhoodsPositive d ∧ checksControlled d

def analyticLocalUniformityBudget
    (d : AnalyticLocalUniformityData) : ℕ :=
  d.neighborhoods + d.uniformityChecks + d.boundarySlack

theorem analyticLocalUniformityReady.neighborhoods
    {d : AnalyticLocalUniformityData}
    (h : analyticLocalUniformityReady d) :
    neighborhoodsPositive d ∧ checksControlled d ∧
      d.uniformityChecks ≤ analyticLocalUniformityBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticLocalUniformityBudget
  omega

theorem checks_le_localUniformityBudget
    (d : AnalyticLocalUniformityData) :
    d.uniformityChecks ≤ analyticLocalUniformityBudget d := by
  unfold analyticLocalUniformityBudget
  omega

def sampleAnalyticLocalUniformityData :
    AnalyticLocalUniformityData :=
  { neighborhoods := 5, uniformityChecks := 7, boundarySlack := 3 }

example :
    analyticLocalUniformityReady sampleAnalyticLocalUniformityData := by
  norm_num [analyticLocalUniformityReady, neighborhoodsPositive]
  norm_num [checksControlled, sampleAnalyticLocalUniformityData]

example :
    analyticLocalUniformityBudget sampleAnalyticLocalUniformityData = 15 := by
  native_decide


structure AnalyticLocalUniformityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticLocalUniformityModelsBudgetCertificate.controlled
    (c : AnalyticLocalUniformityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticLocalUniformityModelsBudgetCertificate.budgetControlled
    (c : AnalyticLocalUniformityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticLocalUniformityModelsBudgetCertificate.Ready
    (c : AnalyticLocalUniformityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticLocalUniformityModelsBudgetCertificate.size
    (c : AnalyticLocalUniformityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticLocalUniformityModels_budgetCertificate_le_size
    (c : AnalyticLocalUniformityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticLocalUniformityModelsBudgetCertificate :
    AnalyticLocalUniformityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticLocalUniformityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.controlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticLocalUniformityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticLocalUniformityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticLocalUniformityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.controlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]

example :
    sampleAnalyticLocalUniformityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticLocalUniformityModelsBudgetCertificate.size := by
  apply analyticLocalUniformityModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.controlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]
  · norm_num [AnalyticLocalUniformityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLocalUniformityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticLocalUniformityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticLocalUniformityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticLocalUniformityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticLocalUniformityModels
