import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite exponential construction models.

The finite record stores label budget, component budget, and exponential
slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteExponentialConstructionModels

structure ExponentialConstructionData where
  labelBudget : ℕ
  componentBudget : ℕ
  exponentialSlack : ℕ
deriving DecidableEq, Repr

def labelBudgetPositive (d : ExponentialConstructionData) : Prop :=
  0 < d.labelBudget

def componentsControlled (d : ExponentialConstructionData) : Prop :=
  d.componentBudget ≤ d.labelBudget + d.exponentialSlack

def exponentialConstructionReady (d : ExponentialConstructionData) : Prop :=
  labelBudgetPositive d ∧ componentsControlled d

def exponentialConstructionBudget (d : ExponentialConstructionData) : ℕ :=
  d.labelBudget + d.componentBudget + d.exponentialSlack

theorem exponentialConstructionReady.labels
    {d : ExponentialConstructionData}
    (h : exponentialConstructionReady d) :
    labelBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem componentBudget_le_exponentialConstructionBudget
    (d : ExponentialConstructionData) :
    d.componentBudget ≤ exponentialConstructionBudget d := by
  unfold exponentialConstructionBudget
  omega

def sampleExponentialConstructionData : ExponentialConstructionData :=
  { labelBudget := 7, componentBudget := 9, exponentialSlack := 3 }

example : exponentialConstructionReady sampleExponentialConstructionData := by
  norm_num [exponentialConstructionReady, labelBudgetPositive]
  norm_num [componentsControlled, sampleExponentialConstructionData]

example :
    exponentialConstructionBudget sampleExponentialConstructionData = 19 := by
  native_decide


structure FiniteExponentialConstructionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteExponentialConstructionModelsBudgetCertificate.controlled
    (c : FiniteExponentialConstructionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteExponentialConstructionModelsBudgetCertificate.budgetControlled
    (c : FiniteExponentialConstructionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteExponentialConstructionModelsBudgetCertificate.Ready
    (c : FiniteExponentialConstructionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteExponentialConstructionModelsBudgetCertificate.size
    (c : FiniteExponentialConstructionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteExponentialConstructionModels_budgetCertificate_le_size
    (c : FiniteExponentialConstructionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteExponentialConstructionModelsBudgetCertificate :
    FiniteExponentialConstructionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteExponentialConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.controlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteExponentialConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteExponentialConstructionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteExponentialConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.controlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]

example :
    sampleFiniteExponentialConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteExponentialConstructionModelsBudgetCertificate.size := by
  apply finiteExponentialConstructionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.controlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]
  · norm_num [FiniteExponentialConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteExponentialConstructionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteExponentialConstructionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteExponentialConstructionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteExponentialConstructionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteExponentialConstructionModels
