import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite symbolic transfer window models.

This module records finite bookkeeping for symbolic transfer windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteSymbolicTransferWindowModels

structure SymbolicTransferWindowData where
  constructors : ℕ
  transferWindow : ℕ
  symbolicSlack : ℕ
deriving DecidableEq, Repr

def hasConstructors (d : SymbolicTransferWindowData) : Prop :=
  0 < d.constructors

def transferWindowControlled (d : SymbolicTransferWindowData) : Prop :=
  d.transferWindow ≤ d.constructors + d.symbolicSlack

def symbolicTransferWindowReady
    (d : SymbolicTransferWindowData) : Prop :=
  hasConstructors d ∧ transferWindowControlled d

def symbolicTransferWindowBudget
    (d : SymbolicTransferWindowData) : ℕ :=
  d.constructors + d.transferWindow + d.symbolicSlack

theorem symbolicTransferWindowReady.hasConstructors
    {d : SymbolicTransferWindowData}
    (h : symbolicTransferWindowReady d) :
    hasConstructors d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transferWindow_le_budget
    (d : SymbolicTransferWindowData) :
    d.transferWindow ≤ symbolicTransferWindowBudget d := by
  unfold symbolicTransferWindowBudget
  omega

def sampleSymbolicTransferWindowData : SymbolicTransferWindowData :=
  { constructors := 6, transferWindow := 8, symbolicSlack := 3 }

example : symbolicTransferWindowReady sampleSymbolicTransferWindowData := by
  norm_num [symbolicTransferWindowReady, hasConstructors]
  norm_num [transferWindowControlled, sampleSymbolicTransferWindowData]

example : symbolicTransferWindowBudget sampleSymbolicTransferWindowData = 17 := by
  native_decide


structure FiniteSymbolicTransferWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSymbolicTransferWindowModelsBudgetCertificate.controlled
    (c : FiniteSymbolicTransferWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSymbolicTransferWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteSymbolicTransferWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSymbolicTransferWindowModelsBudgetCertificate.Ready
    (c : FiniteSymbolicTransferWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSymbolicTransferWindowModelsBudgetCertificate.size
    (c : FiniteSymbolicTransferWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSymbolicTransferWindowModels_budgetCertificate_le_size
    (c : FiniteSymbolicTransferWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSymbolicTransferWindowModelsBudgetCertificate :
    FiniteSymbolicTransferWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]

example :
    sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate.size := by
  apply finiteSymbolicTransferWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.controlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]
  · norm_num [FiniteSymbolicTransferWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSymbolicTransferWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSymbolicTransferWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSymbolicTransferWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSymbolicTransferWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSymbolicTransferWindowModels
