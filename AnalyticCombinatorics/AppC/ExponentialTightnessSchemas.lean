import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Exponential tightness schemas.

The finite schema records compact scale, exponential rate, and tail
slack.
-/

namespace AnalyticCombinatorics.AppC.ExponentialTightnessSchemas

structure ExponentialTightnessData where
  compactScale : ℕ
  exponentialRate : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def compactScalePositive (d : ExponentialTightnessData) : Prop :=
  0 < d.compactScale

def rateControlled (d : ExponentialTightnessData) : Prop :=
  d.exponentialRate ≤ d.compactScale + d.tailSlack

def exponentialTightnessReady (d : ExponentialTightnessData) : Prop :=
  compactScalePositive d ∧ rateControlled d

def exponentialTightnessBudget (d : ExponentialTightnessData) : ℕ :=
  d.compactScale + d.exponentialRate + d.tailSlack

theorem exponentialTightnessReady.compact
    {d : ExponentialTightnessData}
    (h : exponentialTightnessReady d) :
    compactScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem exponentialRate_le_exponentialTightnessBudget
    (d : ExponentialTightnessData) :
    d.exponentialRate ≤ exponentialTightnessBudget d := by
  unfold exponentialTightnessBudget
  omega

def sampleExponentialTightnessData : ExponentialTightnessData :=
  { compactScale := 6, exponentialRate := 8, tailSlack := 3 }

example : exponentialTightnessReady sampleExponentialTightnessData := by
  norm_num [exponentialTightnessReady, compactScalePositive]
  norm_num [rateControlled, sampleExponentialTightnessData]

example : exponentialTightnessBudget sampleExponentialTightnessData = 17 := by
  native_decide

structure ExponentialTightnessWindow where
  compactWindow : ℕ
  rateWindow : ℕ
  tailSlack : ℕ
  tightnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialTightnessWindow.rateControlled (w : ExponentialTightnessWindow) : Prop :=
  w.rateWindow ≤ w.compactWindow + w.tailSlack + w.slack

def exponentialTightnessWindowReady (w : ExponentialTightnessWindow) : Prop :=
  0 < w.compactWindow ∧ w.rateControlled ∧
    w.tightnessBudget ≤ w.compactWindow + w.rateWindow + w.slack

def ExponentialTightnessWindow.certificate (w : ExponentialTightnessWindow) : ℕ :=
  w.compactWindow + w.rateWindow + w.tailSlack + w.tightnessBudget + w.slack

theorem exponentialTightness_tightnessBudget_le_certificate
    (w : ExponentialTightnessWindow) :
    w.tightnessBudget ≤ w.certificate := by
  unfold ExponentialTightnessWindow.certificate
  omega

def sampleExponentialTightnessWindow : ExponentialTightnessWindow :=
  { compactWindow := 5, rateWindow := 7, tailSlack := 2, tightnessBudget := 14, slack := 2 }

example : exponentialTightnessWindowReady sampleExponentialTightnessWindow := by
  norm_num [exponentialTightnessWindowReady, ExponentialTightnessWindow.rateControlled,
    sampleExponentialTightnessWindow]


structure ExponentialTightnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialTightnessSchemasBudgetCertificate.controlled
    (c : ExponentialTightnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExponentialTightnessSchemasBudgetCertificate.budgetControlled
    (c : ExponentialTightnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialTightnessSchemasBudgetCertificate.Ready
    (c : ExponentialTightnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialTightnessSchemasBudgetCertificate.size
    (c : ExponentialTightnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialTightnessSchemas_budgetCertificate_le_size
    (c : ExponentialTightnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialTightnessSchemasBudgetCertificate :
    ExponentialTightnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleExponentialTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.controlled,
      sampleExponentialTightnessSchemasBudgetCertificate]
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTightnessSchemasBudgetCertificate]

example : sampleExponentialTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.controlled,
      sampleExponentialTightnessSchemasBudgetCertificate]
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTightnessSchemasBudgetCertificate]

example :
    sampleExponentialTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTightnessSchemasBudgetCertificate.size := by
  apply exponentialTightnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.controlled,
      sampleExponentialTightnessSchemasBudgetCertificate]
  · norm_num [ExponentialTightnessSchemasBudgetCertificate.budgetControlled,
      sampleExponentialTightnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleExponentialTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTightnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExponentialTightnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialTightnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExponentialTightnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ExponentialTightnessSchemas
