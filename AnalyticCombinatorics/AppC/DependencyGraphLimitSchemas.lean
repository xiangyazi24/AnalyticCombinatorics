import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dependency graph limit schemas.

The finite record stores dependency degree, vertex budget, and error
slack.
-/

namespace AnalyticCombinatorics.AppC.DependencyGraphLimitSchemas

structure DependencyGraphLimitData where
  dependencyDegree : ℕ
  vertexBudget : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def vertexBudgetPositive (d : DependencyGraphLimitData) : Prop :=
  0 < d.vertexBudget

def dependencyDegreeControlled (d : DependencyGraphLimitData) : Prop :=
  d.dependencyDegree ≤ d.vertexBudget + d.errorSlack

def dependencyGraphLimitReady (d : DependencyGraphLimitData) : Prop :=
  vertexBudgetPositive d ∧ dependencyDegreeControlled d

def dependencyGraphLimitBudget (d : DependencyGraphLimitData) : ℕ :=
  d.dependencyDegree + d.vertexBudget + d.errorSlack

theorem dependencyGraphLimitReady.vertices
    {d : DependencyGraphLimitData}
    (h : dependencyGraphLimitReady d) :
    vertexBudgetPositive d ∧ dependencyDegreeControlled d ∧
      d.dependencyDegree ≤ dependencyGraphLimitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold dependencyGraphLimitBudget
  omega

theorem dependencyDegree_le_dependencyGraphBudget
    (d : DependencyGraphLimitData) :
    d.dependencyDegree ≤ dependencyGraphLimitBudget d := by
  unfold dependencyGraphLimitBudget
  omega

def sampleDependencyGraphLimitData : DependencyGraphLimitData :=
  { dependencyDegree := 7, vertexBudget := 5, errorSlack := 3 }

example : dependencyGraphLimitReady sampleDependencyGraphLimitData := by
  norm_num [dependencyGraphLimitReady, vertexBudgetPositive]
  norm_num [dependencyDegreeControlled, sampleDependencyGraphLimitData]

example : dependencyGraphLimitBudget sampleDependencyGraphLimitData = 15 := by
  native_decide

structure DependencyGraphLimitWindow where
  degreeWindow : ℕ
  vertexWindow : ℕ
  errorSlack : ℕ
  graphBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DependencyGraphLimitWindow.degreeControlled
    (w : DependencyGraphLimitWindow) : Prop :=
  w.degreeWindow ≤ w.vertexWindow + w.errorSlack + w.slack

def dependencyGraphLimitWindowReady (w : DependencyGraphLimitWindow) : Prop :=
  0 < w.vertexWindow ∧ w.degreeControlled ∧
    w.graphBudget ≤ w.degreeWindow + w.vertexWindow + w.slack

def DependencyGraphLimitWindow.certificate (w : DependencyGraphLimitWindow) : ℕ :=
  w.degreeWindow + w.vertexWindow + w.errorSlack + w.graphBudget + w.slack

theorem dependencyGraphLimit_graphBudget_le_certificate
    (w : DependencyGraphLimitWindow) :
    w.graphBudget ≤ w.certificate := by
  unfold DependencyGraphLimitWindow.certificate
  omega

def sampleDependencyGraphLimitWindow : DependencyGraphLimitWindow :=
  { degreeWindow := 6, vertexWindow := 5, errorSlack := 2, graphBudget := 12, slack := 1 }

example : dependencyGraphLimitWindowReady sampleDependencyGraphLimitWindow := by
  norm_num [dependencyGraphLimitWindowReady,
    DependencyGraphLimitWindow.degreeControlled, sampleDependencyGraphLimitWindow]


structure DependencyGraphLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DependencyGraphLimitSchemasBudgetCertificate.controlled
    (c : DependencyGraphLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DependencyGraphLimitSchemasBudgetCertificate.budgetControlled
    (c : DependencyGraphLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DependencyGraphLimitSchemasBudgetCertificate.Ready
    (c : DependencyGraphLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DependencyGraphLimitSchemasBudgetCertificate.size
    (c : DependencyGraphLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dependencyGraphLimitSchemas_budgetCertificate_le_size
    (c : DependencyGraphLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDependencyGraphLimitSchemasBudgetCertificate :
    DependencyGraphLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDependencyGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.controlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]

example : sampleDependencyGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.controlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]

example :
    sampleDependencyGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDependencyGraphLimitSchemasBudgetCertificate.size := by
  apply dependencyGraphLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.controlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]
  · norm_num [DependencyGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleDependencyGraphLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleDependencyGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDependencyGraphLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DependencyGraphLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDependencyGraphLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDependencyGraphLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DependencyGraphLimitSchemas
