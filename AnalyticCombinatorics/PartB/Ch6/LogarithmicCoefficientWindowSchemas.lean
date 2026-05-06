import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Logarithmic coefficient window schemas.

This module records finite bookkeeping for logarithmic coefficient windows.
-/

namespace AnalyticCombinatorics.PartB.Ch6.LogarithmicCoefficientWindowSchemas

structure LogarithmicCoefficientWindowData where
  logarithmicOrder : ℕ
  coefficientWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasLogarithmicOrder (d : LogarithmicCoefficientWindowData) : Prop :=
  0 < d.logarithmicOrder

def coefficientWindowControlled
    (d : LogarithmicCoefficientWindowData) : Prop :=
  d.coefficientWindow ≤ d.logarithmicOrder + d.transferSlack

def logarithmicCoefficientWindowReady
    (d : LogarithmicCoefficientWindowData) : Prop :=
  hasLogarithmicOrder d ∧ coefficientWindowControlled d

def logarithmicCoefficientWindowBudget
    (d : LogarithmicCoefficientWindowData) : ℕ :=
  d.logarithmicOrder + d.coefficientWindow + d.transferSlack

theorem logarithmicCoefficientWindowReady.hasLogarithmicOrder
    {d : LogarithmicCoefficientWindowData}
    (h : logarithmicCoefficientWindowReady d) :
    hasLogarithmicOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem coefficientWindow_le_budget
    (d : LogarithmicCoefficientWindowData) :
    d.coefficientWindow ≤ logarithmicCoefficientWindowBudget d := by
  unfold logarithmicCoefficientWindowBudget
  omega

def sampleLogarithmicCoefficientWindowData :
    LogarithmicCoefficientWindowData :=
  { logarithmicOrder := 6, coefficientWindow := 8, transferSlack := 3 }

example : logarithmicCoefficientWindowReady
    sampleLogarithmicCoefficientWindowData := by
  norm_num [logarithmicCoefficientWindowReady, hasLogarithmicOrder]
  norm_num
    [coefficientWindowControlled, sampleLogarithmicCoefficientWindowData]

example :
    logarithmicCoefficientWindowBudget
      sampleLogarithmicCoefficientWindowData = 17 := by
  native_decide


structure LogarithmicCoefficientWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicCoefficientWindowSchemasBudgetCertificate.controlled
    (c : LogarithmicCoefficientWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LogarithmicCoefficientWindowSchemasBudgetCertificate.budgetControlled
    (c : LogarithmicCoefficientWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogarithmicCoefficientWindowSchemasBudgetCertificate.Ready
    (c : LogarithmicCoefficientWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicCoefficientWindowSchemasBudgetCertificate.size
    (c : LogarithmicCoefficientWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logarithmicCoefficientWindowSchemas_budgetCertificate_le_size
    (c : LogarithmicCoefficientWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicCoefficientWindowSchemasBudgetCertificate :
    LogarithmicCoefficientWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.controlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.controlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]

example :
    sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate.size := by
  apply logarithmicCoefficientWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.controlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]
  · norm_num [LogarithmicCoefficientWindowSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicCoefficientWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LogarithmicCoefficientWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicCoefficientWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLogarithmicCoefficientWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.LogarithmicCoefficientWindowSchemas
