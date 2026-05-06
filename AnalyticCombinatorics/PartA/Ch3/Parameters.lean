import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Combinatorial parameter schemas.

This module records finite bookkeeping for size and parameter counts.
-/

namespace AnalyticCombinatorics.PartA.Ch3.Parameters

structure ParameterFiber where
  sizeIndex : ℕ
  parameterValue : ℕ
  fiberCount : ℕ
deriving DecidableEq, Repr

def fiberBudget (f : ParameterFiber) : ℕ :=
  f.sizeIndex + f.parameterValue + f.fiberCount

def fiberNonempty (f : ParameterFiber) : Prop :=
  0 < f.fiberCount

theorem fiberCount_le_budget (f : ParameterFiber) :
    f.fiberCount ≤ fiberBudget f := by
  unfold fiberBudget
  omega

def sampleFiber : ParameterFiber :=
  { sizeIndex := 5, parameterValue := 2, fiberCount := 7 }

example : fiberNonempty sampleFiber := by
  norm_num [fiberNonempty, sampleFiber]

example : fiberBudget sampleFiber = 14 := by
  native_decide

structure ParameterMomentWindow where
  sizeIndex : ℕ
  fiberCount : ℕ
  parameterSum : ℕ
  parameterSquareSum : ℕ
deriving DecidableEq, Repr

def ParameterMomentWindow.meanNumerator (w : ParameterMomentWindow) : ℕ :=
  w.parameterSum

def ParameterMomentWindow.secondMomentNumerator (w : ParameterMomentWindow) : ℕ :=
  w.parameterSquareSum

def ParameterMomentWindow.ready (w : ParameterMomentWindow) : Prop :=
  0 < w.fiberCount ∧ w.parameterSum ≤ w.parameterSquareSum + w.fiberCount

def ParameterMomentWindow.certificate (w : ParameterMomentWindow) : ℕ :=
  w.sizeIndex + w.fiberCount + w.parameterSum + w.parameterSquareSum

theorem parameterSum_le_certificate (w : ParameterMomentWindow) :
    w.parameterSum ≤ w.certificate := by
  unfold ParameterMomentWindow.certificate
  omega

def sampleParameterMomentWindow : ParameterMomentWindow :=
  { sizeIndex := 6, fiberCount := 8, parameterSum := 18, parameterSquareSum := 14 }

example : sampleParameterMomentWindow.ready := by
  norm_num [sampleParameterMomentWindow, ParameterMomentWindow.ready]

example : sampleParameterMomentWindow.certificate = 46 := by
  native_decide


structure ParametersBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ParametersBudgetCertificate.controlled
    (c : ParametersBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ParametersBudgetCertificate.budgetControlled
    (c : ParametersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ParametersBudgetCertificate.Ready
    (c : ParametersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ParametersBudgetCertificate.size
    (c : ParametersBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem parameters_budgetCertificate_le_size
    (c : ParametersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleParametersBudgetCertificate :
    ParametersBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [ParametersBudgetCertificate.controlled,
      sampleParametersBudgetCertificate]
  · norm_num [ParametersBudgetCertificate.budgetControlled,
      sampleParametersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleParametersBudgetCertificate.certificateBudgetWindow ≤
      sampleParametersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleParametersBudgetCertificate.Ready := by
  constructor
  · norm_num [ParametersBudgetCertificate.controlled,
      sampleParametersBudgetCertificate]
  · norm_num [ParametersBudgetCertificate.budgetControlled,
      sampleParametersBudgetCertificate]

example :
    sampleParametersBudgetCertificate.certificateBudgetWindow ≤
      sampleParametersBudgetCertificate.size := by
  apply parameters_budgetCertificate_le_size
  constructor
  · norm_num [ParametersBudgetCertificate.controlled,
      sampleParametersBudgetCertificate]
  · norm_num [ParametersBudgetCertificate.budgetControlled,
      sampleParametersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ParametersBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleParametersBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleParametersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.Parameters
