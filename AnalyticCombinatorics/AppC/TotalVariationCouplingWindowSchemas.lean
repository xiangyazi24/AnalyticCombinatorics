import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Total variation coupling window schemas.

This module records finite bookkeeping for total variation couplings.
-/

namespace AnalyticCombinatorics.AppC.TotalVariationCouplingWindowSchemas

structure TotalVariationCouplingWindowData where
  variationScale : ℕ
  couplingWindow : ℕ
  variationSlack : ℕ
deriving DecidableEq, Repr

def hasVariationScale (d : TotalVariationCouplingWindowData) : Prop :=
  0 < d.variationScale

def couplingWindowControlled
    (d : TotalVariationCouplingWindowData) : Prop :=
  d.couplingWindow ≤ d.variationScale + d.variationSlack

def totalVariationCouplingReady
    (d : TotalVariationCouplingWindowData) : Prop :=
  hasVariationScale d ∧ couplingWindowControlled d

def totalVariationCouplingBudget
    (d : TotalVariationCouplingWindowData) : ℕ :=
  d.variationScale + d.couplingWindow + d.variationSlack

theorem totalVariationCouplingReady.hasVariationScale
    {d : TotalVariationCouplingWindowData}
    (h : totalVariationCouplingReady d) :
    hasVariationScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : TotalVariationCouplingWindowData) :
    d.couplingWindow ≤ totalVariationCouplingBudget d := by
  unfold totalVariationCouplingBudget
  omega

def sampleTotalVariationCouplingWindowData :
    TotalVariationCouplingWindowData :=
  { variationScale := 6, couplingWindow := 8, variationSlack := 3 }

example : totalVariationCouplingReady
    sampleTotalVariationCouplingWindowData := by
  norm_num [totalVariationCouplingReady, hasVariationScale]
  norm_num [couplingWindowControlled, sampleTotalVariationCouplingWindowData]

example :
    totalVariationCouplingBudget sampleTotalVariationCouplingWindowData = 17 := by
  native_decide

structure TotalVariationCouplingCertificateWindow where
  variationWindow : ℕ
  couplingWindow : ℕ
  variationSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TotalVariationCouplingCertificateWindow.couplingControlled
    (w : TotalVariationCouplingCertificateWindow) : Prop :=
  w.couplingWindow ≤ w.variationWindow + w.variationSlack + w.slack

def totalVariationCouplingCertificateReady
    (w : TotalVariationCouplingCertificateWindow) : Prop :=
  0 < w.variationWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.variationWindow + w.couplingWindow + w.slack

def TotalVariationCouplingCertificateWindow.certificate
    (w : TotalVariationCouplingCertificateWindow) : ℕ :=
  w.variationWindow + w.couplingWindow + w.variationSlack + w.couplingBudget + w.slack

theorem totalVariationCoupling_budget_le_certificate
    (w : TotalVariationCouplingCertificateWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold TotalVariationCouplingCertificateWindow.certificate
  omega

def sampleTotalVariationCouplingCertificateWindow :
    TotalVariationCouplingCertificateWindow :=
  { variationWindow := 5, couplingWindow := 7, variationSlack := 2,
    couplingBudget := 14, slack := 2 }

example : totalVariationCouplingCertificateReady
    sampleTotalVariationCouplingCertificateWindow := by
  norm_num [totalVariationCouplingCertificateReady,
    TotalVariationCouplingCertificateWindow.couplingControlled,
    sampleTotalVariationCouplingCertificateWindow]


structure TotalVariationCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TotalVariationCouplingWindowSchemasBudgetCertificate.controlled
    (c : TotalVariationCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TotalVariationCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : TotalVariationCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TotalVariationCouplingWindowSchemasBudgetCertificate.Ready
    (c : TotalVariationCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TotalVariationCouplingWindowSchemasBudgetCertificate.size
    (c : TotalVariationCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem totalVariationCouplingWindowSchemas_budgetCertificate_le_size
    (c : TotalVariationCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTotalVariationCouplingWindowSchemasBudgetCertificate :
    TotalVariationCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTotalVariationCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.controlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]

example : sampleTotalVariationCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.controlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]

example :
    sampleTotalVariationCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate.size := by
  apply totalVariationCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.controlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]
  · norm_num [TotalVariationCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleTotalVariationCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTotalVariationCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TotalVariationCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTotalVariationCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTotalVariationCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TotalVariationCouplingWindowSchemas
