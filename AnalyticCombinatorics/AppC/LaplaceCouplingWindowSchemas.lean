import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laplace coupling window schemas.

This module records finite bookkeeping for Laplace coupling windows.
-/

namespace AnalyticCombinatorics.AppC.LaplaceCouplingWindowSchemas

structure LaplaceCouplingWindowData where
  laplaceScale : ℕ
  couplingWindow : ℕ
  laplaceSlack : ℕ
deriving DecidableEq, Repr

def hasLaplaceScale (d : LaplaceCouplingWindowData) : Prop :=
  0 < d.laplaceScale

def couplingWindowControlled (d : LaplaceCouplingWindowData) : Prop :=
  d.couplingWindow ≤ d.laplaceScale + d.laplaceSlack

def laplaceCouplingReady (d : LaplaceCouplingWindowData) : Prop :=
  hasLaplaceScale d ∧ couplingWindowControlled d

def laplaceCouplingBudget (d : LaplaceCouplingWindowData) : ℕ :=
  d.laplaceScale + d.couplingWindow + d.laplaceSlack

theorem laplaceCouplingReady.hasLaplaceScale
    {d : LaplaceCouplingWindowData}
    (h : laplaceCouplingReady d) :
    hasLaplaceScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : LaplaceCouplingWindowData) :
    d.couplingWindow ≤ laplaceCouplingBudget d := by
  unfold laplaceCouplingBudget
  omega

def sampleLaplaceCouplingWindowData : LaplaceCouplingWindowData :=
  { laplaceScale := 6, couplingWindow := 8, laplaceSlack := 3 }

example : laplaceCouplingReady sampleLaplaceCouplingWindowData := by
  norm_num [laplaceCouplingReady, hasLaplaceScale]
  norm_num [couplingWindowControlled, sampleLaplaceCouplingWindowData]

example : laplaceCouplingBudget sampleLaplaceCouplingWindowData = 17 := by
  native_decide

structure LaplaceCouplingCertificateWindow where
  scaleWindow : ℕ
  couplingWindow : ℕ
  laplaceSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceCouplingCertificateWindow.couplingControlled
    (w : LaplaceCouplingCertificateWindow) : Prop :=
  w.couplingWindow ≤ w.scaleWindow + w.laplaceSlack + w.slack

def laplaceCouplingCertificateReady (w : LaplaceCouplingCertificateWindow) : Prop :=
  0 < w.scaleWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.scaleWindow + w.couplingWindow + w.slack

def LaplaceCouplingCertificateWindow.certificate
    (w : LaplaceCouplingCertificateWindow) : ℕ :=
  w.scaleWindow + w.couplingWindow + w.laplaceSlack + w.couplingBudget + w.slack

theorem laplaceCoupling_couplingBudget_le_certificate
    (w : LaplaceCouplingCertificateWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold LaplaceCouplingCertificateWindow.certificate
  omega

def sampleLaplaceCouplingCertificateWindow : LaplaceCouplingCertificateWindow :=
  { scaleWindow := 5, couplingWindow := 7, laplaceSlack := 2,
    couplingBudget := 14, slack := 2 }

example : laplaceCouplingCertificateReady sampleLaplaceCouplingCertificateWindow := by
  norm_num [laplaceCouplingCertificateReady,
    LaplaceCouplingCertificateWindow.couplingControlled,
    sampleLaplaceCouplingCertificateWindow]


structure LaplaceCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceCouplingWindowSchemasBudgetCertificate.controlled
    (c : LaplaceCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LaplaceCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : LaplaceCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LaplaceCouplingWindowSchemasBudgetCertificate.Ready
    (c : LaplaceCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplaceCouplingWindowSchemasBudgetCertificate.size
    (c : LaplaceCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem laplaceCouplingWindowSchemas_budgetCertificate_le_size
    (c : LaplaceCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceCouplingWindowSchemasBudgetCertificate :
    LaplaceCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLaplaceCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.controlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]

example : sampleLaplaceCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.controlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]

example :
    sampleLaplaceCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceCouplingWindowSchemasBudgetCertificate.size := by
  apply laplaceCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.controlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]
  · norm_num [LaplaceCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleLaplaceCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLaplaceCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LaplaceCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLaplaceCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLaplaceCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LaplaceCouplingWindowSchemas
