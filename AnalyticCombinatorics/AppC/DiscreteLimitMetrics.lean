import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite metrics for comparing discrete laws.

These executable versions are useful for checking small distributions before
lifting the same inequalities to asymptotic probability schemas.
-/

namespace AnalyticCombinatorics.AppC.DiscreteLimitMetrics

def natAbsDiff (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

def l1Distance (p q : List ℕ) : ℕ :=
  (p.zip q).map (fun pair => natAbsDiff pair.1 pair.2) |>.sum

def distanceControlled (p q : List ℕ) (budget : ℕ) : Prop :=
  l1Distance p q ≤ budget

theorem natAbsDiff_self (a : ℕ) :
    natAbsDiff a a = 0 := by
  simp [natAbsDiff]

theorem l1Distance_nil_left (q : List ℕ) :
    l1Distance [] q = 0 := by
  simp [l1Distance]

theorem l1Distance_nil_right (p : List ℕ) :
    l1Distance p [] = 0 := by
  cases p <;> simp [l1Distance]

example : natAbsDiff 3 7 = 4 := by
  native_decide

example : l1Distance [1, 3, 5] [2, 1, 5] = 3 := by
  native_decide

example : distanceControlled [1, 3, 5] [2, 1, 5] 4 := by
  norm_num [distanceControlled, l1Distance, natAbsDiff]

structure DiscreteLimitWindow where
  supportSize : ℕ
  l1Budget : ℕ
  couplingMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteLimitWindow.supportControlled (w : DiscreteLimitWindow) : Prop :=
  w.couplingMass ≤ w.supportSize + w.slack

def DiscreteLimitWindow.distanceReady (w : DiscreteLimitWindow) : Prop :=
  w.l1Budget ≤ w.couplingMass + w.slack

def DiscreteLimitWindow.ready (w : DiscreteLimitWindow) : Prop :=
  w.supportControlled ∧ w.distanceReady

def DiscreteLimitWindow.certificate (w : DiscreteLimitWindow) : ℕ :=
  w.supportSize + w.l1Budget + w.couplingMass + w.slack

theorem l1Budget_le_certificate (w : DiscreteLimitWindow) :
    w.l1Budget ≤ w.certificate := by
  unfold DiscreteLimitWindow.certificate
  omega

def sampleDiscreteLimitWindow : DiscreteLimitWindow :=
  { supportSize := 3, l1Budget := 3, couplingMass := 3, slack := 0 }

example : sampleDiscreteLimitWindow.ready := by
  norm_num [sampleDiscreteLimitWindow, DiscreteLimitWindow.ready,
    DiscreteLimitWindow.supportControlled, DiscreteLimitWindow.distanceReady]

structure DiscreteMetricCertificateWindow where
  supportWindow : ℕ
  distanceWindow : ℕ
  couplingWindow : ℕ
  metricBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteMetricCertificateWindow.distanceControlled
    (w : DiscreteMetricCertificateWindow) : Prop :=
  w.distanceWindow ≤ w.couplingWindow + w.slack

def discreteMetricCertificateReady (w : DiscreteMetricCertificateWindow) : Prop :=
  0 < w.supportWindow ∧ w.distanceControlled ∧
    w.metricBudget ≤ w.supportWindow + w.distanceWindow + w.couplingWindow + w.slack

def DiscreteMetricCertificateWindow.certificate
    (w : DiscreteMetricCertificateWindow) : ℕ :=
  w.supportWindow + w.distanceWindow + w.couplingWindow + w.metricBudget + w.slack

theorem discreteMetric_metricBudget_le_certificate
    (w : DiscreteMetricCertificateWindow) :
    w.metricBudget ≤ w.certificate := by
  unfold DiscreteMetricCertificateWindow.certificate
  omega

def sampleDiscreteMetricCertificateWindow : DiscreteMetricCertificateWindow :=
  { supportWindow := 3, distanceWindow := 3, couplingWindow := 3, metricBudget := 10, slack := 1 }

example : discreteMetricCertificateReady sampleDiscreteMetricCertificateWindow := by
  norm_num [discreteMetricCertificateReady,
    DiscreteMetricCertificateWindow.distanceControlled, sampleDiscreteMetricCertificateWindow]


structure DiscreteLimitMetricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DiscreteLimitMetricsBudgetCertificate.controlled
    (c : DiscreteLimitMetricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DiscreteLimitMetricsBudgetCertificate.budgetControlled
    (c : DiscreteLimitMetricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DiscreteLimitMetricsBudgetCertificate.Ready
    (c : DiscreteLimitMetricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DiscreteLimitMetricsBudgetCertificate.size
    (c : DiscreteLimitMetricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem discreteLimitMetrics_budgetCertificate_le_size
    (c : DiscreteLimitMetricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDiscreteLimitMetricsBudgetCertificate :
    DiscreteLimitMetricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDiscreteLimitMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteLimitMetricsBudgetCertificate.controlled,
      sampleDiscreteLimitMetricsBudgetCertificate]
  · norm_num [DiscreteLimitMetricsBudgetCertificate.budgetControlled,
      sampleDiscreteLimitMetricsBudgetCertificate]

example :
    sampleDiscreteLimitMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleDiscreteLimitMetricsBudgetCertificate.size := by
  apply discreteLimitMetrics_budgetCertificate_le_size
  constructor
  · norm_num [DiscreteLimitMetricsBudgetCertificate.controlled,
      sampleDiscreteLimitMetricsBudgetCertificate]
  · norm_num [DiscreteLimitMetricsBudgetCertificate.budgetControlled,
      sampleDiscreteLimitMetricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDiscreteLimitMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [DiscreteLimitMetricsBudgetCertificate.controlled,
      sampleDiscreteLimitMetricsBudgetCertificate]
  · norm_num [DiscreteLimitMetricsBudgetCertificate.budgetControlled,
      sampleDiscreteLimitMetricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDiscreteLimitMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleDiscreteLimitMetricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DiscreteLimitMetricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDiscreteLimitMetricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDiscreteLimitMetricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DiscreteLimitMetrics
