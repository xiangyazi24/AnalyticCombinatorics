import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exponential Tauberian schema bookkeeping.

The finite record stores exponential scale, positivity, and remainder
budgets.
-/

namespace AnalyticCombinatorics.AppC.ExponentialTauberianSchemas

structure ExponentialTauberianData where
  exponentialScale : ℕ
  positivityBudget : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def positiveExponentialScale (d : ExponentialTauberianData) : Prop :=
  0 < d.exponentialScale

def positiveTauberianMass (d : ExponentialTauberianData) : Prop :=
  0 < d.positivityBudget

def exponentialTauberianReady (d : ExponentialTauberianData) : Prop :=
  positiveExponentialScale d ∧ positiveTauberianMass d

def exponentialTauberianBudget (d : ExponentialTauberianData) : ℕ :=
  d.exponentialScale + d.positivityBudget + d.remainderBudget

theorem exponentialTauberianReady.scale {d : ExponentialTauberianData}
    (h : exponentialTauberianReady d) :
    positiveExponentialScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem scale_le_budget (d : ExponentialTauberianData) :
    d.exponentialScale ≤ exponentialTauberianBudget d := by
  unfold exponentialTauberianBudget
  omega

def sampleExponentialTauberian : ExponentialTauberianData :=
  { exponentialScale := 5, positivityBudget := 3, remainderBudget := 4 }

example : exponentialTauberianReady sampleExponentialTauberian := by
  norm_num
    [exponentialTauberianReady, positiveExponentialScale, positiveTauberianMass,
      sampleExponentialTauberian]

example : exponentialTauberianBudget sampleExponentialTauberian = 12 := by
  native_decide

structure ExponentialTauberianWindow where
  scaleWindow : ℕ
  positivityWindow : ℕ
  remainderWindow : ℕ
  tauberianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialTauberianWindow.remainderControlled
    (w : ExponentialTauberianWindow) : Prop :=
  w.remainderWindow ≤ w.scaleWindow + w.positivityWindow + w.slack

def exponentialTauberianWindowReady (w : ExponentialTauberianWindow) : Prop :=
  0 < w.scaleWindow ∧ 0 < w.positivityWindow ∧ w.remainderControlled ∧
    w.tauberianBudget ≤ w.scaleWindow + w.positivityWindow + w.remainderWindow + w.slack

def ExponentialTauberianWindow.certificate (w : ExponentialTauberianWindow) : ℕ :=
  w.scaleWindow + w.positivityWindow + w.remainderWindow + w.tauberianBudget + w.slack

theorem exponentialTauberian_tauberianBudget_le_certificate
    (w : ExponentialTauberianWindow) :
    w.tauberianBudget ≤ w.certificate := by
  unfold ExponentialTauberianWindow.certificate
  omega

def sampleExponentialTauberianWindow : ExponentialTauberianWindow :=
  { scaleWindow := 5, positivityWindow := 3, remainderWindow := 4,
    tauberianBudget := 13, slack := 1 }

example : exponentialTauberianWindowReady sampleExponentialTauberianWindow := by
  norm_num [exponentialTauberianWindowReady,
    ExponentialTauberianWindow.remainderControlled, sampleExponentialTauberianWindow]


structure ExponentialTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialTauberianSchemasBudgetCertificate.controlled
    (c : ExponentialTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExponentialTauberianSchemasBudgetCertificate.budgetControlled
    (c : ExponentialTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialTauberianSchemasBudgetCertificate.Ready
    (c : ExponentialTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialTauberianSchemasBudgetCertificate.size
    (c : ExponentialTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialTauberianSchemas_budgetCertificate_le_size
    (c : ExponentialTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialTauberianSchemasBudgetCertificate :
    ExponentialTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExponentialTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.controlled,
      sampleExponentialTauberianSchemasBudgetCertificate]
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTauberianSchemasBudgetCertificate]

example : sampleExponentialTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.controlled,
      sampleExponentialTauberianSchemasBudgetCertificate]
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTauberianSchemasBudgetCertificate]

example :
    sampleExponentialTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTauberianSchemasBudgetCertificate.size := by
  apply exponentialTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.controlled,
      sampleExponentialTauberianSchemasBudgetCertificate]
  · norm_num [ExponentialTauberianSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleExponentialTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExponentialTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExponentialTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ExponentialTauberianSchemas
