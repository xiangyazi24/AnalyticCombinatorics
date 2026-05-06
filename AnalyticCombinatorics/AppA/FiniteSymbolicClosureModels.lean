import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite symbolic closure models.

The finite record stores constructor count, closure budget, and guard
slack for symbolic methods.
-/

namespace AnalyticCombinatorics.AppA.FiniteSymbolicClosureModels

structure SymbolicClosureData where
  constructorCount : ℕ
  closureBudget : ℕ
  guardSlack : ℕ
deriving DecidableEq, Repr

def constructorsPositive (d : SymbolicClosureData) : Prop :=
  0 < d.constructorCount

def closureControlled (d : SymbolicClosureData) : Prop :=
  d.closureBudget ≤ d.constructorCount + d.guardSlack

def symbolicClosureReady (d : SymbolicClosureData) : Prop :=
  constructorsPositive d ∧ closureControlled d

def symbolicClosureBudget (d : SymbolicClosureData) : ℕ :=
  d.constructorCount + d.closureBudget + d.guardSlack

theorem symbolicClosureReady.constructors {d : SymbolicClosureData}
    (h : symbolicClosureReady d) :
    constructorsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem closureBudget_le_symbolicClosureBudget (d : SymbolicClosureData) :
    d.closureBudget ≤ symbolicClosureBudget d := by
  unfold symbolicClosureBudget
  omega

def sampleSymbolicClosureData : SymbolicClosureData :=
  { constructorCount := 7, closureBudget := 9, guardSlack := 3 }

example : symbolicClosureReady sampleSymbolicClosureData := by
  norm_num [symbolicClosureReady, constructorsPositive]
  norm_num [closureControlled, sampleSymbolicClosureData]

example : symbolicClosureBudget sampleSymbolicClosureData = 19 := by
  native_decide

structure SymbolicClosureWindow where
  constructorCount : ℕ
  closureBudget : ℕ
  guardSlack : ℕ
  fixedPointBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymbolicClosureWindow.closureControlled (w : SymbolicClosureWindow) : Prop :=
  w.closureBudget ≤ w.constructorCount + w.guardSlack + w.slack

def SymbolicClosureWindow.fixedPointControlled (w : SymbolicClosureWindow) : Prop :=
  w.fixedPointBudget ≤ w.constructorCount + w.closureBudget + w.guardSlack + w.slack

def symbolicClosureWindowReady (w : SymbolicClosureWindow) : Prop :=
  0 < w.constructorCount ∧
    w.closureControlled ∧
    w.fixedPointControlled

def SymbolicClosureWindow.certificate (w : SymbolicClosureWindow) : ℕ :=
  w.constructorCount + w.closureBudget + w.guardSlack + w.slack

theorem symbolicClosure_fixedPointBudget_le_certificate {w : SymbolicClosureWindow}
    (h : symbolicClosureWindowReady w) :
    w.fixedPointBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hfixed⟩
  exact hfixed

def sampleSymbolicClosureWindow : SymbolicClosureWindow :=
  { constructorCount := 7, closureBudget := 9, guardSlack := 3, fixedPointBudget := 18, slack := 0 }

example : symbolicClosureWindowReady sampleSymbolicClosureWindow := by
  norm_num [symbolicClosureWindowReady, SymbolicClosureWindow.closureControlled,
    SymbolicClosureWindow.fixedPointControlled, sampleSymbolicClosureWindow]

example : sampleSymbolicClosureWindow.certificate = 19 := by
  native_decide


structure FiniteSymbolicClosureModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSymbolicClosureModelsBudgetCertificate.controlled
    (c : FiniteSymbolicClosureModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSymbolicClosureModelsBudgetCertificate.budgetControlled
    (c : FiniteSymbolicClosureModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSymbolicClosureModelsBudgetCertificate.Ready
    (c : FiniteSymbolicClosureModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSymbolicClosureModelsBudgetCertificate.size
    (c : FiniteSymbolicClosureModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSymbolicClosureModels_budgetCertificate_le_size
    (c : FiniteSymbolicClosureModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSymbolicClosureModelsBudgetCertificate :
    FiniteSymbolicClosureModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSymbolicClosureModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSymbolicClosureModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSymbolicClosureModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSymbolicClosureModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]

example :
    sampleFiniteSymbolicClosureModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSymbolicClosureModelsBudgetCertificate.size := by
  apply finiteSymbolicClosureModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]
  · norm_num [FiniteSymbolicClosureModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicClosureModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSymbolicClosureModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSymbolicClosureModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSymbolicClosureModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSymbolicClosureModels
