import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bootstrap limit schemas.

The finite schema records resample count, statistic budget, and
approximation slack.
-/

namespace AnalyticCombinatorics.AppC.BootstrapLimitSchemas

structure BootstrapLimitData where
  resampleCount : ℕ
  statisticBudget : ℕ
  approximationSlack : ℕ
deriving DecidableEq, Repr

def resampleCountPositive (d : BootstrapLimitData) : Prop :=
  0 < d.resampleCount

def statisticBudgetControlled (d : BootstrapLimitData) : Prop :=
  d.statisticBudget ≤ d.resampleCount + d.approximationSlack

def bootstrapLimitReady (d : BootstrapLimitData) : Prop :=
  resampleCountPositive d ∧ statisticBudgetControlled d

def bootstrapLimitBudget (d : BootstrapLimitData) : ℕ :=
  d.resampleCount + d.statisticBudget + d.approximationSlack

theorem bootstrapLimitReady.resamples {d : BootstrapLimitData}
    (h : bootstrapLimitReady d) :
    resampleCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem statisticBudget_le_bootstrapBudget (d : BootstrapLimitData) :
    d.statisticBudget ≤ bootstrapLimitBudget d := by
  unfold bootstrapLimitBudget
  omega

def sampleBootstrapLimitData : BootstrapLimitData :=
  { resampleCount := 6, statisticBudget := 8, approximationSlack := 3 }

example : bootstrapLimitReady sampleBootstrapLimitData := by
  norm_num [bootstrapLimitReady, resampleCountPositive]
  norm_num [statisticBudgetControlled, sampleBootstrapLimitData]

example : bootstrapLimitBudget sampleBootstrapLimitData = 17 := by
  native_decide

structure BootstrapLimitWindow where
  resampleCount : ℕ
  statisticBudget : ℕ
  approximationSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BootstrapLimitWindow.statisticControlled (w : BootstrapLimitWindow) : Prop :=
  w.statisticBudget ≤ w.resampleCount + w.approximationSlack + w.slack

def BootstrapLimitWindow.couplingControlled (w : BootstrapLimitWindow) : Prop :=
  w.couplingBudget ≤ w.resampleCount + w.statisticBudget + w.approximationSlack + w.slack

def bootstrapLimitWindowReady (w : BootstrapLimitWindow) : Prop :=
  0 < w.resampleCount ∧
    w.statisticControlled ∧
    w.couplingControlled

def BootstrapLimitWindow.certificate (w : BootstrapLimitWindow) : ℕ :=
  w.resampleCount + w.statisticBudget + w.approximationSlack + w.slack

theorem bootstrapLimit_couplingBudget_le_certificate {w : BootstrapLimitWindow}
    (h : bootstrapLimitWindowReady w) :
    w.couplingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoupling⟩
  exact hcoupling

def sampleBootstrapLimitWindow : BootstrapLimitWindow :=
  { resampleCount := 6, statisticBudget := 8, approximationSlack := 3, couplingBudget := 16,
    slack := 0 }

example : bootstrapLimitWindowReady sampleBootstrapLimitWindow := by
  norm_num [bootstrapLimitWindowReady, BootstrapLimitWindow.statisticControlled,
    BootstrapLimitWindow.couplingControlled, sampleBootstrapLimitWindow]

example : sampleBootstrapLimitWindow.certificate = 17 := by
  native_decide


structure BootstrapLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BootstrapLimitSchemasBudgetCertificate.controlled
    (c : BootstrapLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BootstrapLimitSchemasBudgetCertificate.budgetControlled
    (c : BootstrapLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BootstrapLimitSchemasBudgetCertificate.Ready
    (c : BootstrapLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BootstrapLimitSchemasBudgetCertificate.size
    (c : BootstrapLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem bootstrapLimitSchemas_budgetCertificate_le_size
    (c : BootstrapLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBootstrapLimitSchemasBudgetCertificate :
    BootstrapLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBootstrapLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BootstrapLimitSchemasBudgetCertificate.controlled,
      sampleBootstrapLimitSchemasBudgetCertificate]
  · norm_num [BootstrapLimitSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapLimitSchemasBudgetCertificate]

example : sampleBootstrapLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BootstrapLimitSchemasBudgetCertificate.controlled,
      sampleBootstrapLimitSchemasBudgetCertificate]
  · norm_num [BootstrapLimitSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapLimitSchemasBudgetCertificate]

example :
    sampleBootstrapLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBootstrapLimitSchemasBudgetCertificate.size := by
  apply bootstrapLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BootstrapLimitSchemasBudgetCertificate.controlled,
      sampleBootstrapLimitSchemasBudgetCertificate]
  · norm_num [BootstrapLimitSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBootstrapLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBootstrapLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BootstrapLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBootstrapLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBootstrapLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BootstrapLimitSchemas
