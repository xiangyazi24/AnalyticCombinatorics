import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Kolmogorov coupling window schemas.

This module records finite bookkeeping for Kolmogorov coupling windows.
-/

namespace AnalyticCombinatorics.AppC.KolmogorovCouplingWindowSchemas

structure KolmogorovCouplingWindowData where
  metricScale : ℕ
  couplingWindow : ℕ
  metricSlack : ℕ
deriving DecidableEq, Repr

def hasMetricScale (d : KolmogorovCouplingWindowData) : Prop :=
  0 < d.metricScale

def couplingWindowControlled (d : KolmogorovCouplingWindowData) : Prop :=
  d.couplingWindow ≤ d.metricScale + d.metricSlack

def kolmogorovCouplingReady (d : KolmogorovCouplingWindowData) : Prop :=
  hasMetricScale d ∧ couplingWindowControlled d

def kolmogorovCouplingBudget (d : KolmogorovCouplingWindowData) : ℕ :=
  d.metricScale + d.couplingWindow + d.metricSlack

theorem kolmogorovCouplingReady.hasMetricScale
    {d : KolmogorovCouplingWindowData}
    (h : kolmogorovCouplingReady d) :
    hasMetricScale d ∧ couplingWindowControlled d ∧
      d.couplingWindow ≤ kolmogorovCouplingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold kolmogorovCouplingBudget
  omega

theorem couplingWindow_le_budget (d : KolmogorovCouplingWindowData) :
    d.couplingWindow ≤ kolmogorovCouplingBudget d := by
  unfold kolmogorovCouplingBudget
  omega

def sampleKolmogorovCouplingWindowData : KolmogorovCouplingWindowData :=
  { metricScale := 6, couplingWindow := 8, metricSlack := 3 }

example : kolmogorovCouplingReady sampleKolmogorovCouplingWindowData := by
  norm_num [kolmogorovCouplingReady, hasMetricScale]
  norm_num [couplingWindowControlled, sampleKolmogorovCouplingWindowData]

example : kolmogorovCouplingBudget sampleKolmogorovCouplingWindowData = 17 := by
  native_decide

structure KolmogorovCouplingCertificateWindow where
  metricWindow : ℕ
  couplingWindow : ℕ
  metricSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KolmogorovCouplingCertificateWindow.couplingControlled
    (w : KolmogorovCouplingCertificateWindow) : Prop :=
  w.couplingWindow ≤ w.metricWindow + w.metricSlack + w.slack

def kolmogorovCouplingCertificateReady
    (w : KolmogorovCouplingCertificateWindow) : Prop :=
  0 < w.metricWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.metricWindow + w.couplingWindow + w.slack

def KolmogorovCouplingCertificateWindow.certificate
    (w : KolmogorovCouplingCertificateWindow) : ℕ :=
  w.metricWindow + w.couplingWindow + w.metricSlack + w.couplingBudget + w.slack

theorem kolmogorovCoupling_couplingBudget_le_certificate
    (w : KolmogorovCouplingCertificateWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold KolmogorovCouplingCertificateWindow.certificate
  omega

def sampleKolmogorovCouplingCertificateWindow :
    KolmogorovCouplingCertificateWindow :=
  { metricWindow := 5, couplingWindow := 7, metricSlack := 2,
    couplingBudget := 14, slack := 2 }

example : kolmogorovCouplingCertificateReady
    sampleKolmogorovCouplingCertificateWindow := by
  norm_num [kolmogorovCouplingCertificateReady,
    KolmogorovCouplingCertificateWindow.couplingControlled,
    sampleKolmogorovCouplingCertificateWindow]


structure KolmogorovCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def KolmogorovCouplingWindowSchemasBudgetCertificate.controlled
    (c : KolmogorovCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def KolmogorovCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : KolmogorovCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def KolmogorovCouplingWindowSchemasBudgetCertificate.Ready
    (c : KolmogorovCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def KolmogorovCouplingWindowSchemasBudgetCertificate.size
    (c : KolmogorovCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem kolmogorovCouplingWindowSchemas_budgetCertificate_le_size
    (c : KolmogorovCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleKolmogorovCouplingWindowSchemasBudgetCertificate :
    KolmogorovCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleKolmogorovCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.controlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]

example : sampleKolmogorovCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.controlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]

example :
    sampleKolmogorovCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate.size := by
  apply kolmogorovCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.controlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]
  · norm_num [KolmogorovCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleKolmogorovCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleKolmogorovCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List KolmogorovCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleKolmogorovCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleKolmogorovCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.KolmogorovCouplingWindowSchemas
