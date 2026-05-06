import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic parameter limit schemas.

The finite schema records parameter dimension, analytic window, and
moment slack.
-/

namespace AnalyticCombinatorics.PartA.Ch3.AnalyticParameterLimitSchemas

structure AnalyticParameterLimitData where
  parameterDimension : ℕ
  analyticWindow : ℕ
  momentSlack : ℕ
deriving DecidableEq, Repr

def parameterDimensionPositive (d : AnalyticParameterLimitData) : Prop :=
  0 < d.parameterDimension

def analyticWindowControlled (d : AnalyticParameterLimitData) : Prop :=
  d.analyticWindow ≤ d.parameterDimension + d.momentSlack

def analyticParameterLimitReady
    (d : AnalyticParameterLimitData) : Prop :=
  parameterDimensionPositive d ∧ analyticWindowControlled d

def analyticParameterLimitBudget
    (d : AnalyticParameterLimitData) : ℕ :=
  d.parameterDimension + d.analyticWindow + d.momentSlack

theorem analyticParameterLimitReady.dimension
    {d : AnalyticParameterLimitData}
    (h : analyticParameterLimitReady d) :
    parameterDimensionPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem analyticWindow_le_parameterLimitBudget
    (d : AnalyticParameterLimitData) :
    d.analyticWindow ≤ analyticParameterLimitBudget d := by
  unfold analyticParameterLimitBudget
  omega

def sampleAnalyticParameterLimitData :
    AnalyticParameterLimitData :=
  { parameterDimension := 5, analyticWindow := 7, momentSlack := 3 }

example :
    analyticParameterLimitReady sampleAnalyticParameterLimitData := by
  norm_num [analyticParameterLimitReady, parameterDimensionPositive]
  norm_num [analyticWindowControlled, sampleAnalyticParameterLimitData]

example :
    analyticParameterLimitBudget sampleAnalyticParameterLimitData = 15 := by
  native_decide


structure AnalyticParameterLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticParameterLimitSchemasBudgetCertificate.controlled
    (c : AnalyticParameterLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticParameterLimitSchemasBudgetCertificate.budgetControlled
    (c : AnalyticParameterLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticParameterLimitSchemasBudgetCertificate.Ready
    (c : AnalyticParameterLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticParameterLimitSchemasBudgetCertificate.size
    (c : AnalyticParameterLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticParameterLimitSchemas_budgetCertificate_le_size
    (c : AnalyticParameterLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticParameterLimitSchemasBudgetCertificate :
    AnalyticParameterLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticParameterLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.controlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticParameterLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticParameterLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticParameterLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.controlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]

example :
    sampleAnalyticParameterLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticParameterLimitSchemasBudgetCertificate.size := by
  apply analyticParameterLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.controlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]
  · norm_num [AnalyticParameterLimitSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticParameterLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticParameterLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticParameterLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticParameterLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.AnalyticParameterLimitSchemas
