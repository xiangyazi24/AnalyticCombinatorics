import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Renewal limit window schemas.

This module records finite bookkeeping for renewal limit windows.
-/

namespace AnalyticCombinatorics.AppC.RenewalLimitWindowSchemas

structure RenewalLimitWindowData where
  renewalScale : ℕ
  limitWindow : ℕ
  renewalSlack : ℕ
deriving DecidableEq, Repr

def hasRenewalScale (d : RenewalLimitWindowData) : Prop :=
  0 < d.renewalScale

def limitWindowControlled (d : RenewalLimitWindowData) : Prop :=
  d.limitWindow ≤ d.renewalScale + d.renewalSlack

def renewalLimitWindowReady (d : RenewalLimitWindowData) : Prop :=
  hasRenewalScale d ∧ limitWindowControlled d

def renewalLimitWindowBudget (d : RenewalLimitWindowData) : ℕ :=
  d.renewalScale + d.limitWindow + d.renewalSlack

theorem renewalLimitWindowReady.hasRenewalScale
    {d : RenewalLimitWindowData}
    (h : renewalLimitWindowReady d) :
    hasRenewalScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem limitWindow_le_budget (d : RenewalLimitWindowData) :
    d.limitWindow ≤ renewalLimitWindowBudget d := by
  unfold renewalLimitWindowBudget
  omega

def sampleRenewalLimitWindowData : RenewalLimitWindowData :=
  { renewalScale := 6, limitWindow := 8, renewalSlack := 3 }

example : renewalLimitWindowReady sampleRenewalLimitWindowData := by
  norm_num [renewalLimitWindowReady, hasRenewalScale]
  norm_num [limitWindowControlled, sampleRenewalLimitWindowData]

example : renewalLimitWindowBudget sampleRenewalLimitWindowData = 17 := by
  native_decide

structure RenewalLimitCertificateWindow where
  renewalWindow : ℕ
  limitWindow : ℕ
  renewalSlack : ℕ
  renewalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RenewalLimitCertificateWindow.limitControlled
    (w : RenewalLimitCertificateWindow) : Prop :=
  w.limitWindow ≤ w.renewalWindow + w.renewalSlack + w.slack

def renewalLimitCertificateReady (w : RenewalLimitCertificateWindow) : Prop :=
  0 < w.renewalWindow ∧ w.limitControlled ∧
    w.renewalBudget ≤ w.renewalWindow + w.limitWindow + w.slack

def RenewalLimitCertificateWindow.certificate
    (w : RenewalLimitCertificateWindow) : ℕ :=
  w.renewalWindow + w.limitWindow + w.renewalSlack + w.renewalBudget + w.slack

theorem renewalLimit_renewalBudget_le_certificate
    (w : RenewalLimitCertificateWindow) :
    w.renewalBudget ≤ w.certificate := by
  unfold RenewalLimitCertificateWindow.certificate
  omega

def sampleRenewalLimitCertificateWindow : RenewalLimitCertificateWindow :=
  { renewalWindow := 5, limitWindow := 7, renewalSlack := 2, renewalBudget := 14, slack := 2 }

example : renewalLimitCertificateReady sampleRenewalLimitCertificateWindow := by
  norm_num [renewalLimitCertificateReady,
    RenewalLimitCertificateWindow.limitControlled, sampleRenewalLimitCertificateWindow]


structure RenewalLimitWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RenewalLimitWindowSchemasBudgetCertificate.controlled
    (c : RenewalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RenewalLimitWindowSchemasBudgetCertificate.budgetControlled
    (c : RenewalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RenewalLimitWindowSchemasBudgetCertificate.Ready
    (c : RenewalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RenewalLimitWindowSchemasBudgetCertificate.size
    (c : RenewalLimitWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem renewalLimitWindowSchemas_budgetCertificate_le_size
    (c : RenewalLimitWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRenewalLimitWindowSchemasBudgetCertificate :
    RenewalLimitWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRenewalLimitWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.controlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]

example : sampleRenewalLimitWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.controlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]

example :
    sampleRenewalLimitWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRenewalLimitWindowSchemasBudgetCertificate.size := by
  apply renewalLimitWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.controlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]
  · norm_num [RenewalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleRenewalLimitWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRenewalLimitWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRenewalLimitWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RenewalLimitWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRenewalLimitWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRenewalLimitWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RenewalLimitWindowSchemas
