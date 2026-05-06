import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random constraint satisfaction schemas.

The finite schema records variables, constraints, and slack for random
constraint satisfaction models.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomConstraintSatisfactionSchemas

structure RandomConstraintSatisfactionData where
  variableCount : ℕ
  constraints : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def variablesPositive (d : RandomConstraintSatisfactionData) : Prop :=
  0 < d.variableCount

def constraintsControlled (d : RandomConstraintSatisfactionData) : Prop :=
  d.constraints ≤ d.variableCount + d.slack

def randomConstraintSatisfactionReady
    (d : RandomConstraintSatisfactionData) : Prop :=
  variablesPositive d ∧ constraintsControlled d

def randomConstraintSatisfactionBudget
    (d : RandomConstraintSatisfactionData) : ℕ :=
  d.variableCount + d.constraints + d.slack

theorem randomConstraintSatisfactionReady.variables
    {d : RandomConstraintSatisfactionData}
    (h : randomConstraintSatisfactionReady d) :
    variablesPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem constraints_le_randomConstraintBudget
    (d : RandomConstraintSatisfactionData) :
    d.constraints ≤ randomConstraintSatisfactionBudget d := by
  unfold randomConstraintSatisfactionBudget
  omega

def sampleRandomConstraintSatisfactionData :
    RandomConstraintSatisfactionData :=
  { variableCount := 9, constraints := 11, slack := 3 }

example :
    randomConstraintSatisfactionReady
      sampleRandomConstraintSatisfactionData := by
  norm_num [randomConstraintSatisfactionReady, variablesPositive]
  norm_num [constraintsControlled, sampleRandomConstraintSatisfactionData]

example :
    randomConstraintSatisfactionBudget
      sampleRandomConstraintSatisfactionData = 23 := by
  native_decide

/-- Finite executable readiness audit for random CSP windows. -/
def randomConstraintSatisfactionListReady
    (windows : List RandomConstraintSatisfactionData) : Bool :=
  windows.all fun d =>
    0 < d.variableCount && d.constraints ≤ d.variableCount + d.slack

theorem randomConstraintSatisfactionList_readyWindow :
    randomConstraintSatisfactionListReady
      [{ variableCount := 5, constraints := 6, slack := 1 },
       { variableCount := 9, constraints := 11, slack := 3 }] = true := by
  unfold randomConstraintSatisfactionListReady
  native_decide

structure RandomConstraintSatisfactionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomConstraintSatisfactionSchemasBudgetCertificate.controlled
    (c : RandomConstraintSatisfactionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomConstraintSatisfactionSchemasBudgetCertificate.budgetControlled
    (c : RandomConstraintSatisfactionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomConstraintSatisfactionSchemasBudgetCertificate.Ready
    (c : RandomConstraintSatisfactionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomConstraintSatisfactionSchemasBudgetCertificate.size
    (c : RandomConstraintSatisfactionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomConstraintSatisfactionSchemas_budgetCertificate_le_size
    (c : RandomConstraintSatisfactionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomConstraintSatisfactionSchemasBudgetCertificate :
    RandomConstraintSatisfactionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomConstraintSatisfactionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.controlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.budgetControlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomConstraintSatisfactionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomConstraintSatisfactionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.controlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.budgetControlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]

example :
    sampleRandomConstraintSatisfactionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate.size := by
  apply randomConstraintSatisfactionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.controlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]
  · norm_num [RandomConstraintSatisfactionSchemasBudgetCertificate.budgetControlled,
      sampleRandomConstraintSatisfactionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomConstraintSatisfactionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomConstraintSatisfactionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomConstraintSatisfactionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomConstraintSatisfactionSchemas
