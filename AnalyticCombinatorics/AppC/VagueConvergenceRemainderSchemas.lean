import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Vague convergence remainder schemas.

This module records finite bookkeeping for vague convergence remainders.
-/

namespace AnalyticCombinatorics.AppC.VagueConvergenceRemainderSchemas

structure VagueConvergenceRemainderData where
  testWindow : ℕ
  remainderScale : ℕ
  vagueSlack : ℕ
deriving DecidableEq, Repr

def hasTestWindow (d : VagueConvergenceRemainderData) : Prop :=
  0 < d.testWindow

def remainderScaleControlled (d : VagueConvergenceRemainderData) : Prop :=
  d.remainderScale ≤ d.testWindow + d.vagueSlack

def vagueConvergenceRemainderReady
    (d : VagueConvergenceRemainderData) : Prop :=
  hasTestWindow d ∧ remainderScaleControlled d

def vagueConvergenceRemainderBudget
    (d : VagueConvergenceRemainderData) : ℕ :=
  d.testWindow + d.remainderScale + d.vagueSlack

theorem vagueConvergenceRemainderReady.hasTestWindow
    {d : VagueConvergenceRemainderData}
    (h : vagueConvergenceRemainderReady d) :
    hasTestWindow d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderScale_le_budget (d : VagueConvergenceRemainderData) :
    d.remainderScale ≤ vagueConvergenceRemainderBudget d := by
  unfold vagueConvergenceRemainderBudget
  omega

def sampleVagueConvergenceRemainderData :
    VagueConvergenceRemainderData :=
  { testWindow := 7, remainderScale := 9, vagueSlack := 3 }

example : vagueConvergenceRemainderReady
    sampleVagueConvergenceRemainderData := by
  norm_num [vagueConvergenceRemainderReady, hasTestWindow]
  norm_num [remainderScaleControlled, sampleVagueConvergenceRemainderData]

example :
    vagueConvergenceRemainderBudget sampleVagueConvergenceRemainderData = 19 := by
  native_decide

structure VagueConvergenceRemainderWindow where
  testWindow : ℕ
  remainderWindow : ℕ
  vagueSlack : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def VagueConvergenceRemainderWindow.remainderControlled
    (w : VagueConvergenceRemainderWindow) : Prop :=
  w.remainderWindow ≤ w.testWindow + w.vagueSlack + w.slack

def vagueConvergenceRemainderWindowReady
    (w : VagueConvergenceRemainderWindow) : Prop :=
  0 < w.testWindow ∧ w.remainderControlled ∧
    w.remainderBudget ≤ w.testWindow + w.remainderWindow + w.slack

def VagueConvergenceRemainderWindow.certificate
    (w : VagueConvergenceRemainderWindow) : ℕ :=
  w.testWindow + w.remainderWindow + w.vagueSlack + w.remainderBudget + w.slack

theorem vagueConvergenceRemainder_budget_le_certificate
    (w : VagueConvergenceRemainderWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold VagueConvergenceRemainderWindow.certificate
  omega

def sampleVagueConvergenceRemainderWindow : VagueConvergenceRemainderWindow :=
  { testWindow := 6, remainderWindow := 8, vagueSlack := 2,
    remainderBudget := 15, slack := 1 }

example : vagueConvergenceRemainderWindowReady
    sampleVagueConvergenceRemainderWindow := by
  norm_num [vagueConvergenceRemainderWindowReady,
    VagueConvergenceRemainderWindow.remainderControlled,
    sampleVagueConvergenceRemainderWindow]


structure VagueConvergenceRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def VagueConvergenceRemainderSchemasBudgetCertificate.controlled
    (c : VagueConvergenceRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def VagueConvergenceRemainderSchemasBudgetCertificate.budgetControlled
    (c : VagueConvergenceRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def VagueConvergenceRemainderSchemasBudgetCertificate.Ready
    (c : VagueConvergenceRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def VagueConvergenceRemainderSchemasBudgetCertificate.size
    (c : VagueConvergenceRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem vagueConvergenceRemainderSchemas_budgetCertificate_le_size
    (c : VagueConvergenceRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleVagueConvergenceRemainderSchemasBudgetCertificate :
    VagueConvergenceRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleVagueConvergenceRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]

example : sampleVagueConvergenceRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]

example :
    sampleVagueConvergenceRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleVagueConvergenceRemainderSchemasBudgetCertificate.size := by
  apply vagueConvergenceRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.controlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]
  · norm_num [VagueConvergenceRemainderSchemasBudgetCertificate.budgetControlled,
      sampleVagueConvergenceRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleVagueConvergenceRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleVagueConvergenceRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List VagueConvergenceRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleVagueConvergenceRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleVagueConvergenceRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.VagueConvergenceRemainderSchemas
