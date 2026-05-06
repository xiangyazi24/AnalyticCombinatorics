import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Wasserstein coupling window schemas.

This module records finite bookkeeping for Wasserstein coupling windows.
-/

namespace AnalyticCombinatorics.AppC.WassersteinCouplingWindowSchemas

structure WassersteinCouplingWindowData where
  transportScale : ℕ
  couplingWindow : ℕ
  wassersteinSlack : ℕ
deriving DecidableEq, Repr

def hasTransportScale (d : WassersteinCouplingWindowData) : Prop :=
  0 < d.transportScale

def couplingWindowControlled
    (d : WassersteinCouplingWindowData) : Prop :=
  d.couplingWindow ≤ d.transportScale + d.wassersteinSlack

def wassersteinCouplingReady
    (d : WassersteinCouplingWindowData) : Prop :=
  hasTransportScale d ∧ couplingWindowControlled d

def wassersteinCouplingBudget
    (d : WassersteinCouplingWindowData) : ℕ :=
  d.transportScale + d.couplingWindow + d.wassersteinSlack

theorem wassersteinCouplingReady.hasTransportScale
    {d : WassersteinCouplingWindowData}
    (h : wassersteinCouplingReady d) :
    hasTransportScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : WassersteinCouplingWindowData) :
    d.couplingWindow ≤ wassersteinCouplingBudget d := by
  unfold wassersteinCouplingBudget
  omega

def sampleWassersteinCouplingWindowData :
    WassersteinCouplingWindowData :=
  { transportScale := 7, couplingWindow := 9, wassersteinSlack := 3 }

example : wassersteinCouplingReady
    sampleWassersteinCouplingWindowData := by
  norm_num [wassersteinCouplingReady, hasTransportScale]
  norm_num [couplingWindowControlled, sampleWassersteinCouplingWindowData]

example :
    wassersteinCouplingBudget sampleWassersteinCouplingWindowData = 19 := by
  native_decide

structure WassersteinCouplingCertificateWindow where
  transportWindow : ℕ
  couplingWindow : ℕ
  wassersteinSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WassersteinCouplingCertificateWindow.couplingControlled
    (w : WassersteinCouplingCertificateWindow) : Prop :=
  w.couplingWindow ≤ w.transportWindow + w.wassersteinSlack + w.slack

def wassersteinCouplingCertificateReady
    (w : WassersteinCouplingCertificateWindow) : Prop :=
  0 < w.transportWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.transportWindow + w.couplingWindow + w.slack

def WassersteinCouplingCertificateWindow.certificate
    (w : WassersteinCouplingCertificateWindow) : ℕ :=
  w.transportWindow + w.couplingWindow + w.wassersteinSlack + w.couplingBudget + w.slack

theorem wassersteinCoupling_budget_le_certificate
    (w : WassersteinCouplingCertificateWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold WassersteinCouplingCertificateWindow.certificate
  omega

def sampleWassersteinCouplingCertificateWindow :
    WassersteinCouplingCertificateWindow :=
  { transportWindow := 6, couplingWindow := 8, wassersteinSlack := 2,
    couplingBudget := 15, slack := 1 }

example : wassersteinCouplingCertificateReady
    sampleWassersteinCouplingCertificateWindow := by
  norm_num [wassersteinCouplingCertificateReady,
    WassersteinCouplingCertificateWindow.couplingControlled,
    sampleWassersteinCouplingCertificateWindow]


structure WassersteinCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WassersteinCouplingWindowSchemasBudgetCertificate.controlled
    (c : WassersteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WassersteinCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : WassersteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WassersteinCouplingWindowSchemasBudgetCertificate.Ready
    (c : WassersteinCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WassersteinCouplingWindowSchemasBudgetCertificate.size
    (c : WassersteinCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem wassersteinCouplingWindowSchemas_budgetCertificate_le_size
    (c : WassersteinCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWassersteinCouplingWindowSchemasBudgetCertificate :
    WassersteinCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWassersteinCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]

example : sampleWassersteinCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]

example :
    sampleWassersteinCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWassersteinCouplingWindowSchemasBudgetCertificate.size := by
  apply wassersteinCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.controlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]
  · norm_num [WassersteinCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleWassersteinCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleWassersteinCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWassersteinCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List WassersteinCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWassersteinCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWassersteinCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.WassersteinCouplingWindowSchemas
