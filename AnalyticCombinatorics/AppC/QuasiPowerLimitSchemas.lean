import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quasi-power limit-law schemas.

The data structure records the hypotheses normally checked from a uniform
moment-generating-function expansion.
-/

namespace AnalyticCombinatorics.AppC.QuasiPowerLimitSchemas

structure QuasiPowerSchema where
  analyticUniform : Prop
  varianceNondegenerate : Prop
  remainderControlled : Prop

def gaussianLimitReady (s : QuasiPowerSchema) : Prop :=
  s.analyticUniform ∧ s.varianceNondegenerate ∧ s.remainderControlled

def meanNumerator (slope intercept n : ℕ) : ℕ :=
  slope * n + intercept

def varianceNumerator (slope floor n : ℕ) : ℕ :=
  slope * n + floor

theorem gaussianLimitReady_intro {s : QuasiPowerSchema}
    (ha : s.analyticUniform) (hv : s.varianceNondegenerate)
    (hr : s.remainderControlled) :
    gaussianLimitReady s := by
  exact ⟨ha, hv, hr⟩

theorem gaussianLimitReady.analytic {s : QuasiPowerSchema}
    (h : gaussianLimitReady s) :
    s.analyticUniform := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem gaussianLimitReady.variance {s : QuasiPowerSchema}
    (h : gaussianLimitReady s) :
    s.varianceNondegenerate := h.2.1

theorem meanNumerator_succ (slope intercept n : ℕ) :
    meanNumerator slope intercept (n + 1) =
      meanNumerator slope intercept n + slope := by
  unfold meanNumerator
  rw [Nat.mul_succ]
  omega

theorem varianceNumerator_succ (slope floor n : ℕ) :
    varianceNumerator slope floor (n + 1) =
      varianceNumerator slope floor n + slope := by
  unfold varianceNumerator
  rw [Nat.mul_succ]
  omega

example : meanNumerator 3 2 5 = 17 := by
  native_decide

example : varianceNumerator 4 1 6 = 25 := by
  native_decide

structure QuasiPowerWindow where
  analyticWindow : ℕ
  varianceWindow : ℕ
  remainderWindow : ℕ
  gaussianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerWindow.remainderControlled (w : QuasiPowerWindow) : Prop :=
  w.remainderWindow ≤ w.analyticWindow + w.varianceWindow + w.slack

def quasiPowerWindowReady (w : QuasiPowerWindow) : Prop :=
  0 < w.analyticWindow ∧ 0 < w.varianceWindow ∧ w.remainderControlled ∧
    w.gaussianBudget ≤ w.analyticWindow + w.varianceWindow + w.remainderWindow + w.slack

def QuasiPowerWindow.certificate (w : QuasiPowerWindow) : ℕ :=
  w.analyticWindow + w.varianceWindow + w.remainderWindow + w.gaussianBudget + w.slack

theorem quasiPower_gaussianBudget_le_certificate (w : QuasiPowerWindow) :
    w.gaussianBudget ≤ w.certificate := by
  unfold QuasiPowerWindow.certificate
  omega

def sampleQuasiPowerWindow : QuasiPowerWindow :=
  { analyticWindow := 5, varianceWindow := 3, remainderWindow := 4,
    gaussianBudget := 13, slack := 1 }

example : quasiPowerWindowReady sampleQuasiPowerWindow := by
  norm_num [quasiPowerWindowReady, QuasiPowerWindow.remainderControlled,
    sampleQuasiPowerWindow]


structure QuasiPowerLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerLimitSchemasBudgetCertificate.controlled
    (c : QuasiPowerLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QuasiPowerLimitSchemasBudgetCertificate.budgetControlled
    (c : QuasiPowerLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QuasiPowerLimitSchemasBudgetCertificate.Ready
    (c : QuasiPowerLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuasiPowerLimitSchemasBudgetCertificate.size
    (c : QuasiPowerLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem quasiPowerLimitSchemas_budgetCertificate_le_size
    (c : QuasiPowerLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuasiPowerLimitSchemasBudgetCertificate :
    QuasiPowerLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleQuasiPowerLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.controlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]

example :
    sampleQuasiPowerLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerLimitSchemasBudgetCertificate.size := by
  apply quasiPowerLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.controlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleQuasiPowerLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.controlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]
  · norm_num [QuasiPowerLimitSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQuasiPowerLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List QuasiPowerLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQuasiPowerLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQuasiPowerLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.QuasiPowerLimitSchemas
