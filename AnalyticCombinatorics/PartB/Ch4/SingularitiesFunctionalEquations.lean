import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singularities and functional equations.
-/

namespace AnalyticCombinatorics.PartB.Ch4.SingularitiesFunctionalEquations

/-- Integer residual for the tree equation `y = x * (1 + y)^2`. -/
def treeEquationResidual (x y : ℤ) : ℤ :=
  y - x * (1 + y) ^ 2

/-- Criticality condition: derivative in `y` vanishes. -/
def treeEquationDerivativeY (x y : ℤ) : ℤ :=
  1 - x * (2 * (1 + y))

/-- Finite noncriticality check over sampled integer boxes. -/
def noncriticalBoxCheck (radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun x =>
    (List.range (radius + 1)).all fun y =>
      treeEquationDerivativeY x y ≠ 0

/-- Local functional-equation window at the ordinary point. -/
def FunctionalEquationWindow : Prop :=
  treeEquationResidual 0 0 = 0 ∧ treeEquationDerivativeY 0 0 = 1

theorem treeEquation_originWindow :
    FunctionalEquationWindow := by
  unfold FunctionalEquationWindow treeEquationResidual treeEquationDerivativeY
  norm_num

theorem treeEquation_noncriticalOrigin :
    noncriticalBoxCheck 0 = true := by
  unfold noncriticalBoxCheck treeEquationDerivativeY
  native_decide

def TreeEquationResidualWindow (x y residual derivative : ℤ) : Prop :=
  treeEquationResidual x y = residual ∧
    treeEquationDerivativeY x y = derivative

theorem treeEquation_sampleResidualWindow :
    TreeEquationResidualWindow 1 1 (-3) (-3) := by
  unfold TreeEquationResidualWindow treeEquationResidual treeEquationDerivativeY
  norm_num

example : treeEquationResidual 2 1 = -7 := by
  unfold treeEquationResidual
  norm_num

example : treeEquationDerivativeY 2 1 = -7 := by
  unfold treeEquationDerivativeY
  norm_num

structure SingularitiesFunctionalEquationsBudgetCertificate where
  equationWindow : ℕ
  singularityWindow : ℕ
  solutionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularitiesFunctionalEquationsBudgetCertificate.controlled
    (c : SingularitiesFunctionalEquationsBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.solutionWindow ≤ c.equationWindow + c.singularityWindow + c.slack

def SingularitiesFunctionalEquationsBudgetCertificate.budgetControlled
    (c : SingularitiesFunctionalEquationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.singularityWindow + c.solutionWindow + c.slack

def SingularitiesFunctionalEquationsBudgetCertificate.Ready
    (c : SingularitiesFunctionalEquationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularitiesFunctionalEquationsBudgetCertificate.size
    (c : SingularitiesFunctionalEquationsBudgetCertificate) : ℕ :=
  c.equationWindow + c.singularityWindow + c.solutionWindow + c.slack

theorem singularitiesFunctionalEquations_budgetCertificate_le_size
    (c : SingularitiesFunctionalEquationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularitiesFunctionalEquationsBudgetCertificate :
    SingularitiesFunctionalEquationsBudgetCertificate :=
  { equationWindow := 5
    singularityWindow := 6
    solutionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSingularitiesFunctionalEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesFunctionalEquationsBudgetCertificate.controlled,
      sampleSingularitiesFunctionalEquationsBudgetCertificate]
  · norm_num [SingularitiesFunctionalEquationsBudgetCertificate.budgetControlled,
      sampleSingularitiesFunctionalEquationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularitiesFunctionalEquationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularitiesFunctionalEquationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSingularitiesFunctionalEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesFunctionalEquationsBudgetCertificate.controlled,
      sampleSingularitiesFunctionalEquationsBudgetCertificate]
  · norm_num [SingularitiesFunctionalEquationsBudgetCertificate.budgetControlled,
      sampleSingularitiesFunctionalEquationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SingularitiesFunctionalEquationsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularitiesFunctionalEquationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSingularitiesFunctionalEquationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.SingularitiesFunctionalEquations
