import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random intersection graph limit schemas.

The finite schema records vertex, feature, and overlap budgets.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomIntersectionGraphLimitSchemas

structure RandomIntersectionGraphData where
  vertices : ℕ
  features : ℕ
  overlapBudget : ℕ
deriving DecidableEq, Repr

def verticesNonempty (d : RandomIntersectionGraphData) : Prop :=
  0 < d.vertices

def featuresControlled (d : RandomIntersectionGraphData) : Prop :=
  d.features ≤ d.vertices + d.overlapBudget

def randomIntersectionGraphReady
    (d : RandomIntersectionGraphData) : Prop :=
  verticesNonempty d ∧ featuresControlled d

def randomIntersectionGraphBudget
    (d : RandomIntersectionGraphData) : ℕ :=
  d.vertices + d.features + d.overlapBudget

theorem randomIntersectionGraphReady.vertices
    {d : RandomIntersectionGraphData}
    (h : randomIntersectionGraphReady d) :
    verticesNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem features_le_randomIntersectionBudget
    (d : RandomIntersectionGraphData) :
    d.features ≤ randomIntersectionGraphBudget d := by
  unfold randomIntersectionGraphBudget
  omega

def sampleRandomIntersectionGraphData :
    RandomIntersectionGraphData :=
  { vertices := 10, features := 12, overlapBudget := 4 }

example :
    randomIntersectionGraphReady sampleRandomIntersectionGraphData := by
  norm_num [randomIntersectionGraphReady, verticesNonempty]
  norm_num [featuresControlled, sampleRandomIntersectionGraphData]

example :
    randomIntersectionGraphBudget
      sampleRandomIntersectionGraphData = 26 := by
  native_decide

/-- Finite executable readiness audit for random intersection graph windows. -/
def randomIntersectionGraphListReady
    (windows : List RandomIntersectionGraphData) : Bool :=
  windows.all fun d =>
    0 < d.vertices && d.features ≤ d.vertices + d.overlapBudget

theorem randomIntersectionGraphList_readyWindow :
    randomIntersectionGraphListReady
      [{ vertices := 6, features := 7, overlapBudget := 1 },
       { vertices := 10, features := 12, overlapBudget := 4 }] = true := by
  unfold randomIntersectionGraphListReady
  native_decide

structure RandomIntersectionGraphLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomIntersectionGraphLimitSchemasBudgetCertificate.controlled
    (c : RandomIntersectionGraphLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomIntersectionGraphLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomIntersectionGraphLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomIntersectionGraphLimitSchemasBudgetCertificate.Ready
    (c : RandomIntersectionGraphLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomIntersectionGraphLimitSchemasBudgetCertificate.size
    (c : RandomIntersectionGraphLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomIntersectionGraphLimitSchemas_budgetCertificate_le_size
    (c : RandomIntersectionGraphLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomIntersectionGraphLimitSchemasBudgetCertificate :
    RandomIntersectionGraphLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]

example :
    sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate.size := by
  apply randomIntersectionGraphLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomIntersectionGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomIntersectionGraphLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomIntersectionGraphLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomIntersectionGraphLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomIntersectionGraphLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomIntersectionGraphLimitSchemas
