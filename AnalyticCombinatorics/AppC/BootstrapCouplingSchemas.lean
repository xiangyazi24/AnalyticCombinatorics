import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bootstrap coupling schemas.

This module records finite bookkeeping for bootstrap coupling windows.
-/

namespace AnalyticCombinatorics.AppC.BootstrapCouplingSchemas

structure BootstrapCouplingData where
  bootstrapSamples : ℕ
  couplingWindow : ℕ
  approximationSlack : ℕ
deriving DecidableEq, Repr

def hasBootstrapSamples (d : BootstrapCouplingData) : Prop :=
  0 < d.bootstrapSamples

def couplingWindowControlled (d : BootstrapCouplingData) : Prop :=
  d.couplingWindow ≤ d.bootstrapSamples + d.approximationSlack

def bootstrapCouplingReady (d : BootstrapCouplingData) : Prop :=
  hasBootstrapSamples d ∧ couplingWindowControlled d

def bootstrapCouplingBudget (d : BootstrapCouplingData) : ℕ :=
  d.bootstrapSamples + d.couplingWindow + d.approximationSlack

theorem bootstrapCouplingReady.hasBootstrapSamples
    {d : BootstrapCouplingData}
    (h : bootstrapCouplingReady d) :
    hasBootstrapSamples d ∧ couplingWindowControlled d ∧
      d.couplingWindow ≤ bootstrapCouplingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold bootstrapCouplingBudget
  omega

theorem couplingWindow_le_budget (d : BootstrapCouplingData) :
    d.couplingWindow ≤ bootstrapCouplingBudget d := by
  unfold bootstrapCouplingBudget
  omega

def sampleBootstrapCouplingData : BootstrapCouplingData :=
  { bootstrapSamples := 7, couplingWindow := 9, approximationSlack := 3 }

example : bootstrapCouplingReady sampleBootstrapCouplingData := by
  norm_num [bootstrapCouplingReady, hasBootstrapSamples]
  norm_num [couplingWindowControlled, sampleBootstrapCouplingData]

example : bootstrapCouplingBudget sampleBootstrapCouplingData = 19 := by
  native_decide

structure BootstrapCouplingWindow where
  sampleWindow : ℕ
  couplingWindow : ℕ
  approximationSlack : ℕ
  bootstrapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BootstrapCouplingWindow.couplingControlled (w : BootstrapCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.sampleWindow + w.approximationSlack + w.slack

def bootstrapCouplingWindowReady (w : BootstrapCouplingWindow) : Prop :=
  0 < w.sampleWindow ∧ w.couplingControlled ∧
    w.bootstrapBudget ≤ w.sampleWindow + w.couplingWindow + w.slack

def BootstrapCouplingWindow.certificate (w : BootstrapCouplingWindow) : ℕ :=
  w.sampleWindow + w.couplingWindow + w.approximationSlack + w.bootstrapBudget + w.slack

theorem bootstrapCoupling_bootstrapBudget_le_certificate
    (w : BootstrapCouplingWindow) :
    w.bootstrapBudget ≤ w.certificate := by
  unfold BootstrapCouplingWindow.certificate
  omega

def sampleBootstrapCouplingWindow : BootstrapCouplingWindow :=
  { sampleWindow := 6, couplingWindow := 8, approximationSlack := 2,
    bootstrapBudget := 15, slack := 1 }

example : bootstrapCouplingWindowReady sampleBootstrapCouplingWindow := by
  norm_num [bootstrapCouplingWindowReady, BootstrapCouplingWindow.couplingControlled,
    sampleBootstrapCouplingWindow]


structure BootstrapCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BootstrapCouplingSchemasBudgetCertificate.controlled
    (c : BootstrapCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BootstrapCouplingSchemasBudgetCertificate.budgetControlled
    (c : BootstrapCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BootstrapCouplingSchemasBudgetCertificate.Ready
    (c : BootstrapCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BootstrapCouplingSchemasBudgetCertificate.size
    (c : BootstrapCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem bootstrapCouplingSchemas_budgetCertificate_le_size
    (c : BootstrapCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBootstrapCouplingSchemasBudgetCertificate :
    BootstrapCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBootstrapCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.controlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]

example : sampleBootstrapCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.controlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]

example :
    sampleBootstrapCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBootstrapCouplingSchemasBudgetCertificate.size := by
  apply bootstrapCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.controlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]
  · norm_num [BootstrapCouplingSchemasBudgetCertificate.budgetControlled,
      sampleBootstrapCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBootstrapCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBootstrapCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BootstrapCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBootstrapCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBootstrapCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BootstrapCouplingSchemas
