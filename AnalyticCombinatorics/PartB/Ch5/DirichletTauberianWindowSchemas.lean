import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dirichlet Tauberian window schemas.

This module records finite bookkeeping for Dirichlet Tauberian windows.
-/

namespace AnalyticCombinatorics.PartB.Ch5.DirichletTauberianWindowSchemas

structure DirichletTauberianWindowData where
  stripWidth : ℕ
  summatoryWindow : ℕ
  tauberianSlack : ℕ
deriving DecidableEq, Repr

def hasStripWidth (d : DirichletTauberianWindowData) : Prop :=
  0 < d.stripWidth

def summatoryWindowControlled
    (d : DirichletTauberianWindowData) : Prop :=
  d.summatoryWindow ≤ d.stripWidth + d.tauberianSlack

def dirichletTauberianWindowReady
    (d : DirichletTauberianWindowData) : Prop :=
  hasStripWidth d ∧ summatoryWindowControlled d

def dirichletTauberianWindowBudget
    (d : DirichletTauberianWindowData) : ℕ :=
  d.stripWidth + d.summatoryWindow + d.tauberianSlack

theorem dirichletTauberianWindowReady.hasStripWidth
    {d : DirichletTauberianWindowData}
    (h : dirichletTauberianWindowReady d) :
    hasStripWidth d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem summatoryWindow_le_budget (d : DirichletTauberianWindowData) :
    d.summatoryWindow ≤ dirichletTauberianWindowBudget d := by
  unfold dirichletTauberianWindowBudget
  omega

def sampleDirichletTauberianWindowData : DirichletTauberianWindowData :=
  { stripWidth := 6, summatoryWindow := 8, tauberianSlack := 3 }

example : dirichletTauberianWindowReady
    sampleDirichletTauberianWindowData := by
  norm_num [dirichletTauberianWindowReady, hasStripWidth]
  norm_num [summatoryWindowControlled, sampleDirichletTauberianWindowData]

example :
    dirichletTauberianWindowBudget
      sampleDirichletTauberianWindowData = 17 := by
  native_decide


structure DirichletTauberianWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DirichletTauberianWindowSchemasBudgetCertificate.controlled
    (c : DirichletTauberianWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DirichletTauberianWindowSchemasBudgetCertificate.budgetControlled
    (c : DirichletTauberianWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DirichletTauberianWindowSchemasBudgetCertificate.Ready
    (c : DirichletTauberianWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DirichletTauberianWindowSchemasBudgetCertificate.size
    (c : DirichletTauberianWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dirichletTauberianWindowSchemas_budgetCertificate_le_size
    (c : DirichletTauberianWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDirichletTauberianWindowSchemasBudgetCertificate :
    DirichletTauberianWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDirichletTauberianWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.controlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.budgetControlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDirichletTauberianWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletTauberianWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDirichletTauberianWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.controlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.budgetControlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]

example :
    sampleDirichletTauberianWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletTauberianWindowSchemasBudgetCertificate.size := by
  apply dirichletTauberianWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.controlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]
  · norm_num [DirichletTauberianWindowSchemasBudgetCertificate.budgetControlled,
      sampleDirichletTauberianWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List DirichletTauberianWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDirichletTauberianWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDirichletTauberianWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.DirichletTauberianWindowSchemas

