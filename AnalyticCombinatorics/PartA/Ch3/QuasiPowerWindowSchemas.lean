import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quasi-power window schemas.

The finite record stores analytic window, variance scale, and cumulant
slack.
-/

namespace AnalyticCombinatorics.PartA.Ch3.QuasiPowerWindowSchemas

structure QuasiPowerWindowData where
  analyticWindow : ℕ
  varianceScale : ℕ
  cumulantSlack : ℕ
deriving DecidableEq, Repr

def varianceScalePositive (d : QuasiPowerWindowData) : Prop :=
  0 < d.varianceScale

def analyticWindowControlled (d : QuasiPowerWindowData) : Prop :=
  d.analyticWindow ≤ d.varianceScale + d.cumulantSlack

def quasiPowerWindowReady (d : QuasiPowerWindowData) : Prop :=
  varianceScalePositive d ∧ analyticWindowControlled d

def quasiPowerWindowBudget (d : QuasiPowerWindowData) : ℕ :=
  d.analyticWindow + d.varianceScale + d.cumulantSlack

theorem quasiPowerWindowReady.variance {d : QuasiPowerWindowData}
    (h : quasiPowerWindowReady d) :
    varianceScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem analyticWindow_le_quasiPowerBudget (d : QuasiPowerWindowData) :
    d.analyticWindow ≤ quasiPowerWindowBudget d := by
  unfold quasiPowerWindowBudget
  omega

def sampleQuasiPowerWindowData : QuasiPowerWindowData :=
  { analyticWindow := 7, varianceScale := 5, cumulantSlack := 3 }

example : quasiPowerWindowReady sampleQuasiPowerWindowData := by
  norm_num [quasiPowerWindowReady, varianceScalePositive]
  norm_num [analyticWindowControlled, sampleQuasiPowerWindowData]

example : quasiPowerWindowBudget sampleQuasiPowerWindowData = 15 := by
  native_decide

structure QuasiPowerCertificateWindow where
  analyticWindow : ℕ
  varianceScale : ℕ
  cumulantSlack : ℕ
  transformBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerCertificateWindow.analyticControlled
    (w : QuasiPowerCertificateWindow) : Prop :=
  w.analyticWindow ≤ w.varianceScale + w.cumulantSlack + w.slack

def QuasiPowerCertificateWindow.transformControlled
    (w : QuasiPowerCertificateWindow) : Prop :=
  w.transformBudget ≤ w.analyticWindow + w.varianceScale + w.cumulantSlack + w.slack

def quasiPowerCertificateReady (w : QuasiPowerCertificateWindow) : Prop :=
  0 < w.varianceScale ∧
    w.analyticControlled ∧
    w.transformControlled

def QuasiPowerCertificateWindow.certificate (w : QuasiPowerCertificateWindow) : ℕ :=
  w.analyticWindow + w.varianceScale + w.cumulantSlack + w.slack

theorem quasiPower_transformBudget_le_certificate {w : QuasiPowerCertificateWindow}
    (h : quasiPowerCertificateReady w) :
    w.transformBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransform⟩
  exact htransform

def sampleQuasiPowerCertificateWindow : QuasiPowerCertificateWindow :=
  { analyticWindow := 7, varianceScale := 5, cumulantSlack := 3, transformBudget := 14,
    slack := 0 }

example : quasiPowerCertificateReady sampleQuasiPowerCertificateWindow := by
  norm_num [quasiPowerCertificateReady, QuasiPowerCertificateWindow.analyticControlled,
    QuasiPowerCertificateWindow.transformControlled, sampleQuasiPowerCertificateWindow]

example : sampleQuasiPowerCertificateWindow.certificate = 15 := by
  native_decide


structure QuasiPowerWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerWindowSchemasBudgetCertificate.controlled
    (c : QuasiPowerWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QuasiPowerWindowSchemasBudgetCertificate.budgetControlled
    (c : QuasiPowerWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QuasiPowerWindowSchemasBudgetCertificate.Ready
    (c : QuasiPowerWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuasiPowerWindowSchemasBudgetCertificate.size
    (c : QuasiPowerWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem quasiPowerWindowSchemas_budgetCertificate_le_size
    (c : QuasiPowerWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuasiPowerWindowSchemasBudgetCertificate :
    QuasiPowerWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQuasiPowerWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.controlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQuasiPowerWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleQuasiPowerWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.controlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]

example :
    sampleQuasiPowerWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerWindowSchemasBudgetCertificate.size := by
  apply quasiPowerWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.controlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]
  · norm_num [QuasiPowerWindowSchemasBudgetCertificate.budgetControlled,
      sampleQuasiPowerWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List QuasiPowerWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQuasiPowerWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQuasiPowerWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.QuasiPowerWindowSchemas
