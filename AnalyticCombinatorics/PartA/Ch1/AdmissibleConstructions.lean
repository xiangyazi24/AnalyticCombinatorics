import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Admissible constructions and specifications.

Finite arity and dependency-window bookkeeping for admissible symbolic
constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.AdmissibleConstructions

/-- Finite descriptor for a symbolic construction rule. -/
structure ConstructionRule where
  arity : ℕ
  recursiveCalls : ℕ
  preservesSize : Bool
deriving DecidableEq, Repr

def ConstructionRule.admissible (r : ConstructionRule) : Prop :=
  0 < r.arity ∧ r.recursiveCalls ≤ r.arity ∧ r.preservesSize = true

def constructionRuleAdmissibleBool (r : ConstructionRule) : Bool :=
  decide (0 < r.arity) && decide (r.recursiveCalls ≤ r.arity) && r.preservesSize

def productConstructionRule : ConstructionRule :=
  { arity := 2, recursiveCalls := 2, preservesSize := true }

theorem productConstructionRule_admissible :
    productConstructionRule.admissible ∧
      constructionRuleAdmissibleBool productConstructionRule = true := by
  constructor
  · norm_num [ConstructionRule.admissible, productConstructionRule]
  · unfold constructionRuleAdmissibleBool productConstructionRule
    native_decide

structure AdmissibleConstructionData where
  constructorArity : ℕ
  dependencyDepth : ℕ
  specificationSize : ℕ
  admissibilitySlack : ℕ
deriving DecidableEq, Repr

def hasConstructor (d : AdmissibleConstructionData) : Prop :=
  0 < d.constructorArity

def dependencyDepthControlled (d : AdmissibleConstructionData) : Prop :=
  d.dependencyDepth ≤ d.constructorArity + d.specificationSize + d.admissibilitySlack

def admissibleConstructionReady (d : AdmissibleConstructionData) : Prop :=
  hasConstructor d ∧ dependencyDepthControlled d

def admissibleConstructionBudget (d : AdmissibleConstructionData) : ℕ :=
  d.constructorArity + d.dependencyDepth + d.specificationSize + d.admissibilitySlack

theorem dependencyDepth_le_budget (d : AdmissibleConstructionData) :
    d.dependencyDepth ≤ admissibleConstructionBudget d := by
  unfold admissibleConstructionBudget
  omega

def sampleAdmissibleConstructionData : AdmissibleConstructionData :=
  { constructorArity := 3
    dependencyDepth := 8
    specificationSize := 4
    admissibilitySlack := 1 }

example : admissibleConstructionReady sampleAdmissibleConstructionData := by
  norm_num [admissibleConstructionReady, hasConstructor,
    dependencyDepthControlled, sampleAdmissibleConstructionData]

structure AdmissibleConstructionsBudgetCertificate where
  arityWindow : ℕ
  specificationWindow : ℕ
  dependencyWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdmissibleConstructionsBudgetCertificate.controlled
    (c : AdmissibleConstructionsBudgetCertificate) : Prop :=
  0 < c.arityWindow ∧
    c.dependencyWindow ≤ c.arityWindow + c.specificationWindow + c.slack

def AdmissibleConstructionsBudgetCertificate.budgetControlled
    (c : AdmissibleConstructionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.arityWindow + c.specificationWindow + c.dependencyWindow + c.slack

def AdmissibleConstructionsBudgetCertificate.Ready
    (c : AdmissibleConstructionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdmissibleConstructionsBudgetCertificate.size
    (c : AdmissibleConstructionsBudgetCertificate) : ℕ :=
  c.arityWindow + c.specificationWindow + c.dependencyWindow + c.slack

theorem admissibleConstructions_budgetCertificate_le_size
    (c : AdmissibleConstructionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAdmissibleConstructionsBudgetCertificate :
    AdmissibleConstructionsBudgetCertificate :=
  { arityWindow := 3
    specificationWindow := 4
    dependencyWindow := 8
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdmissibleConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibleConstructionsBudgetCertificate.controlled,
      sampleAdmissibleConstructionsBudgetCertificate]
  · norm_num [AdmissibleConstructionsBudgetCertificate.budgetControlled,
      sampleAdmissibleConstructionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdmissibleConstructionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAdmissibleConstructionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdmissibleConstructionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AdmissibleConstructionsBudgetCertificate.controlled,
      sampleAdmissibleConstructionsBudgetCertificate]
  · norm_num [AdmissibleConstructionsBudgetCertificate.budgetControlled,
      sampleAdmissibleConstructionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AdmissibleConstructionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAdmissibleConstructionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdmissibleConstructionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.AdmissibleConstructions
