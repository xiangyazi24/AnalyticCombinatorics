import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Symbolic transfer window schemas.

This module records finite bookkeeping for symbolic transfer windows.
-/

namespace AnalyticCombinatorics.PartA.Ch1.SymbolicTransferWindowSchemas

structure SymbolicTransferWindowData where
  classAtoms : ℕ
  transferWindow : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def hasClassAtoms (d : SymbolicTransferWindowData) : Prop :=
  0 < d.classAtoms

def transferWindowControlled (d : SymbolicTransferWindowData) : Prop :=
  d.transferWindow ≤ d.classAtoms + d.constructionSlack

def symbolicTransferWindowReady
    (d : SymbolicTransferWindowData) : Prop :=
  hasClassAtoms d ∧ transferWindowControlled d

def symbolicTransferWindowBudget
    (d : SymbolicTransferWindowData) : ℕ :=
  d.classAtoms + d.transferWindow + d.constructionSlack

theorem symbolicTransferWindowReady.hasClassAtoms
    {d : SymbolicTransferWindowData}
    (h : symbolicTransferWindowReady d) :
    hasClassAtoms d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem transferWindow_le_budget
    (d : SymbolicTransferWindowData) :
    d.transferWindow ≤ symbolicTransferWindowBudget d := by
  unfold symbolicTransferWindowBudget
  omega

def sampleSymbolicTransferWindowData : SymbolicTransferWindowData :=
  { classAtoms := 5, transferWindow := 7, constructionSlack := 2 }

example : symbolicTransferWindowReady sampleSymbolicTransferWindowData := by
  norm_num [symbolicTransferWindowReady, hasClassAtoms]
  norm_num [transferWindowControlled, sampleSymbolicTransferWindowData]

example : symbolicTransferWindowBudget sampleSymbolicTransferWindowData = 14 := by
  native_decide


structure SymbolicTransferWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SymbolicTransferWindowSchemasBudgetCertificate.controlled
    (c : SymbolicTransferWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SymbolicTransferWindowSchemasBudgetCertificate.budgetControlled
    (c : SymbolicTransferWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SymbolicTransferWindowSchemasBudgetCertificate.Ready
    (c : SymbolicTransferWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SymbolicTransferWindowSchemasBudgetCertificate.size
    (c : SymbolicTransferWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem symbolicTransferWindowSchemas_budgetCertificate_le_size
    (c : SymbolicTransferWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSymbolicTransferWindowSchemasBudgetCertificate :
    SymbolicTransferWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSymbolicTransferWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.controlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.budgetControlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSymbolicTransferWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicTransferWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSymbolicTransferWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.controlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.budgetControlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]

example :
    sampleSymbolicTransferWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSymbolicTransferWindowSchemasBudgetCertificate.size := by
  apply symbolicTransferWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.controlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]
  · norm_num [SymbolicTransferWindowSchemasBudgetCertificate.budgetControlled,
      sampleSymbolicTransferWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SymbolicTransferWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSymbolicTransferWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSymbolicTransferWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SymbolicTransferWindowSchemas

