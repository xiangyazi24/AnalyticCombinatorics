import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Depoissonization limit schemas.

This module records finite bookkeeping for depoissonization limits.
-/

namespace AnalyticCombinatorics.AppC.DepoissonizationLimitSchemas

structure DepoissonizationLimitData where
  poissonWindow : ℕ
  discreteWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasPoissonWindow (d : DepoissonizationLimitData) : Prop :=
  0 < d.poissonWindow

def discreteWindowControlled (d : DepoissonizationLimitData) : Prop :=
  d.discreteWindow ≤ d.poissonWindow + d.transferSlack

def depoissonizationLimitReady (d : DepoissonizationLimitData) : Prop :=
  hasPoissonWindow d ∧ discreteWindowControlled d

def depoissonizationLimitBudget (d : DepoissonizationLimitData) : ℕ :=
  d.poissonWindow + d.discreteWindow + d.transferSlack

theorem depoissonizationLimitReady.hasPoissonWindow
    {d : DepoissonizationLimitData}
    (h : depoissonizationLimitReady d) :
    hasPoissonWindow d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem discreteWindow_le_budget (d : DepoissonizationLimitData) :
    d.discreteWindow ≤ depoissonizationLimitBudget d := by
  unfold depoissonizationLimitBudget
  omega

def sampleDepoissonizationLimitData : DepoissonizationLimitData :=
  { poissonWindow := 6, discreteWindow := 8, transferSlack := 3 }

example : depoissonizationLimitReady sampleDepoissonizationLimitData := by
  norm_num [depoissonizationLimitReady, hasPoissonWindow]
  norm_num [discreteWindowControlled, sampleDepoissonizationLimitData]

example : depoissonizationLimitBudget sampleDepoissonizationLimitData = 17 := by
  native_decide

structure DepoissonizationLimitWindow where
  poissonWindow : ℕ
  discreteWindow : ℕ
  transferSlack : ℕ
  limitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationLimitWindow.discreteControlled
    (w : DepoissonizationLimitWindow) : Prop :=
  w.discreteWindow ≤ w.poissonWindow + w.transferSlack + w.slack

def depoissonizationLimitWindowReady (w : DepoissonizationLimitWindow) : Prop :=
  0 < w.poissonWindow ∧ w.discreteControlled ∧
    w.limitBudget ≤ w.poissonWindow + w.discreteWindow + w.slack

def DepoissonizationLimitWindow.certificate (w : DepoissonizationLimitWindow) : ℕ :=
  w.poissonWindow + w.discreteWindow + w.transferSlack + w.limitBudget + w.slack

theorem depoissonizationLimit_limitBudget_le_certificate
    (w : DepoissonizationLimitWindow) :
    w.limitBudget ≤ w.certificate := by
  unfold DepoissonizationLimitWindow.certificate
  omega

def sampleDepoissonizationLimitWindow : DepoissonizationLimitWindow :=
  { poissonWindow := 5, discreteWindow := 7, transferSlack := 2, limitBudget := 14, slack := 2 }

example : depoissonizationLimitWindowReady sampleDepoissonizationLimitWindow := by
  norm_num [depoissonizationLimitWindowReady,
    DepoissonizationLimitWindow.discreteControlled, sampleDepoissonizationLimitWindow]


structure DepoissonizationLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationLimitSchemasBudgetCertificate.controlled
    (c : DepoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DepoissonizationLimitSchemasBudgetCertificate.budgetControlled
    (c : DepoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DepoissonizationLimitSchemasBudgetCertificate.Ready
    (c : DepoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DepoissonizationLimitSchemasBudgetCertificate.size
    (c : DepoissonizationLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem depoissonizationLimitSchemas_budgetCertificate_le_size
    (c : DepoissonizationLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDepoissonizationLimitSchemasBudgetCertificate :
    DepoissonizationLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDepoissonizationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.controlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]

example : sampleDepoissonizationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.controlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]

example :
    sampleDepoissonizationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationLimitSchemasBudgetCertificate.size := by
  apply depoissonizationLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.controlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]
  · norm_num [DepoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      sampleDepoissonizationLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleDepoissonizationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DepoissonizationLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDepoissonizationLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDepoissonizationLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DepoissonizationLimitSchemas
