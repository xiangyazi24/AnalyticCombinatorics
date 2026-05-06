import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Recursive specification schemas.

The file records finite dependency counts and guardedness budgets for
recursive combinatorial specifications.
-/

namespace AnalyticCombinatorics.PartA.Ch1.RecursiveSpecificationSchemas

structure RecursiveSpecData where
  equationCount : ℕ
  dependencyCount : ℕ
  guardBudget : ℕ
deriving DecidableEq, Repr

def nonemptySpecification (d : RecursiveSpecData) : Prop :=
  0 < d.equationCount

def guardedSpecification (d : RecursiveSpecData) : Prop :=
  d.dependencyCount ≤ d.guardBudget + d.equationCount

def recursiveSpecReady (d : RecursiveSpecData) : Prop :=
  nonemptySpecification d ∧ guardedSpecification d

def specificationBudget (d : RecursiveSpecData) : ℕ :=
  d.equationCount + d.dependencyCount + d.guardBudget

theorem recursiveSpecReady.nonempty {d : RecursiveSpecData}
    (h : recursiveSpecReady d) :
    nonemptySpecification d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem equationCount_le_budget (d : RecursiveSpecData) :
    d.equationCount ≤ specificationBudget d := by
  unfold specificationBudget
  omega

def sampleRecursiveSpec : RecursiveSpecData :=
  { equationCount := 2, dependencyCount := 5, guardBudget := 4 }

example : recursiveSpecReady sampleRecursiveSpec := by
  norm_num [recursiveSpecReady, nonemptySpecification, guardedSpecification, sampleRecursiveSpec]

example : specificationBudget sampleRecursiveSpec = 11 := by
  native_decide

structure RecursiveSpecificationWindow where
  equations : ℕ
  dependencies : ℕ
  guardBudget : ℕ
  solutionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveSpecificationWindow.nonempty (w : RecursiveSpecificationWindow) : Prop :=
  0 < w.equations

def RecursiveSpecificationWindow.guarded (w : RecursiveSpecificationWindow) : Prop :=
  w.dependencies ≤ w.guardBudget + w.equations + w.slack

def RecursiveSpecificationWindow.solutionControlled (w : RecursiveSpecificationWindow) : Prop :=
  w.solutionBudget ≤ w.equations + w.dependencies + w.guardBudget + w.slack

def RecursiveSpecificationWindow.ready (w : RecursiveSpecificationWindow) : Prop :=
  w.nonempty ∧ w.guarded ∧ w.solutionControlled

def RecursiveSpecificationWindow.certificate (w : RecursiveSpecificationWindow) : ℕ :=
  w.equations + w.dependencies + w.guardBudget + w.solutionBudget + w.slack

theorem solutionBudget_le_certificate (w : RecursiveSpecificationWindow) :
    w.solutionBudget ≤ w.certificate := by
  unfold RecursiveSpecificationWindow.certificate
  omega

def sampleRecursiveSpecificationWindow : RecursiveSpecificationWindow :=
  { equations := 2, dependencies := 5, guardBudget := 4, solutionBudget := 6, slack := 0 }

example : sampleRecursiveSpecificationWindow.ready := by
  norm_num [sampleRecursiveSpecificationWindow, RecursiveSpecificationWindow.ready,
    RecursiveSpecificationWindow.nonempty, RecursiveSpecificationWindow.guarded,
    RecursiveSpecificationWindow.solutionControlled]


structure RecursiveSpecificationSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveSpecificationSchemasBudgetCertificate.controlled
    (c : RecursiveSpecificationSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecursiveSpecificationSchemasBudgetCertificate.budgetControlled
    (c : RecursiveSpecificationSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecursiveSpecificationSchemasBudgetCertificate.Ready
    (c : RecursiveSpecificationSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecursiveSpecificationSchemasBudgetCertificate.size
    (c : RecursiveSpecificationSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recursiveSpecificationSchemas_budgetCertificate_le_size
    (c : RecursiveSpecificationSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecursiveSpecificationSchemasBudgetCertificate :
    RecursiveSpecificationSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRecursiveSpecificationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.controlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecursiveSpecificationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveSpecificationSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRecursiveSpecificationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.controlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]

example :
    sampleRecursiveSpecificationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveSpecificationSchemasBudgetCertificate.size := by
  apply recursiveSpecificationSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.controlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]
  · norm_num [RecursiveSpecificationSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveSpecificationSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RecursiveSpecificationSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecursiveSpecificationSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRecursiveSpecificationSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.RecursiveSpecificationSchemas
