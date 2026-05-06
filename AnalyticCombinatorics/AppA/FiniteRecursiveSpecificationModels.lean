import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite recursive specification models.

The finite record stores equation count, constructor budget, and guard
slack for recursive specifications.
-/

namespace AnalyticCombinatorics.AppA.FiniteRecursiveSpecificationModels

structure RecursiveSpecificationData where
  equationCount : ℕ
  constructorBudget : ℕ
  guardSlack : ℕ
deriving DecidableEq, Repr

def equationCountPositive (d : RecursiveSpecificationData) : Prop :=
  0 < d.equationCount

def constructorBudgetControlled (d : RecursiveSpecificationData) : Prop :=
  d.constructorBudget ≤ d.equationCount + d.guardSlack

def recursiveSpecificationReady (d : RecursiveSpecificationData) : Prop :=
  equationCountPositive d ∧ constructorBudgetControlled d

def recursiveSpecificationBudget (d : RecursiveSpecificationData) : ℕ :=
  d.equationCount + d.constructorBudget + d.guardSlack

theorem recursiveSpecificationReady.equations
    {d : RecursiveSpecificationData}
    (h : recursiveSpecificationReady d) :
    equationCountPositive d ∧ constructorBudgetControlled d ∧
      d.constructorBudget ≤ recursiveSpecificationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold recursiveSpecificationBudget
  omega

theorem constructorBudget_le_recursiveSpecificationBudget
    (d : RecursiveSpecificationData) :
    d.constructorBudget ≤ recursiveSpecificationBudget d := by
  unfold recursiveSpecificationBudget
  omega

def sampleRecursiveSpecificationData : RecursiveSpecificationData :=
  { equationCount := 5, constructorBudget := 7, guardSlack := 3 }

example : recursiveSpecificationReady sampleRecursiveSpecificationData := by
  norm_num [recursiveSpecificationReady, equationCountPositive]
  norm_num [constructorBudgetControlled, sampleRecursiveSpecificationData]

example :
    recursiveSpecificationBudget sampleRecursiveSpecificationData = 15 := by
  native_decide


structure FiniteRecursiveSpecificationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRecursiveSpecificationModelsBudgetCertificate.controlled
    (c : FiniteRecursiveSpecificationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRecursiveSpecificationModelsBudgetCertificate.budgetControlled
    (c : FiniteRecursiveSpecificationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRecursiveSpecificationModelsBudgetCertificate.Ready
    (c : FiniteRecursiveSpecificationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRecursiveSpecificationModelsBudgetCertificate.size
    (c : FiniteRecursiveSpecificationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRecursiveSpecificationModels_budgetCertificate_le_size
    (c : FiniteRecursiveSpecificationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRecursiveSpecificationModelsBudgetCertificate :
    FiniteRecursiveSpecificationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRecursiveSpecificationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.controlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.budgetControlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRecursiveSpecificationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRecursiveSpecificationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.controlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.budgetControlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]

example :
    sampleFiniteRecursiveSpecificationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate.size := by
  apply finiteRecursiveSpecificationModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.controlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]
  · norm_num [FiniteRecursiveSpecificationModelsBudgetCertificate.budgetControlled,
      sampleFiniteRecursiveSpecificationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteRecursiveSpecificationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRecursiveSpecificationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRecursiveSpecificationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRecursiveSpecificationModels
