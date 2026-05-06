import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Zero-one law schemas.

The finite record stores event count, threshold scale, and dependency
slack.
-/

namespace AnalyticCombinatorics.AppC.ZeroOneLawSchemas

structure ZeroOneLawData where
  eventCount : ℕ
  thresholdScale : ℕ
  dependencySlack : ℕ
deriving DecidableEq, Repr

def eventCountPositive (d : ZeroOneLawData) : Prop :=
  0 < d.eventCount

def thresholdScaleControlled (d : ZeroOneLawData) : Prop :=
  d.thresholdScale ≤ d.eventCount + d.dependencySlack

def zeroOneLawReady (d : ZeroOneLawData) : Prop :=
  eventCountPositive d ∧ thresholdScaleControlled d

def zeroOneLawBudget (d : ZeroOneLawData) : ℕ :=
  d.eventCount + d.thresholdScale + d.dependencySlack

theorem zeroOneLawReady.events {d : ZeroOneLawData}
    (h : zeroOneLawReady d) :
    eventCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem thresholdScale_le_zeroOneLawBudget (d : ZeroOneLawData) :
    d.thresholdScale ≤ zeroOneLawBudget d := by
  unfold zeroOneLawBudget
  omega

def sampleZeroOneLawData : ZeroOneLawData :=
  { eventCount := 7, thresholdScale := 9, dependencySlack := 3 }

example : zeroOneLawReady sampleZeroOneLawData := by
  norm_num [zeroOneLawReady, eventCountPositive]
  norm_num [thresholdScaleControlled, sampleZeroOneLawData]

example : zeroOneLawBudget sampleZeroOneLawData = 19 := by
  native_decide

structure ZeroOneLawWindow where
  eventCount : ℕ
  thresholdScale : ℕ
  dependencySlack : ℕ
  witnessBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ZeroOneLawWindow.thresholdControlled (w : ZeroOneLawWindow) : Prop :=
  w.thresholdScale ≤ w.eventCount + w.dependencySlack + w.slack

def ZeroOneLawWindow.witnessControlled (w : ZeroOneLawWindow) : Prop :=
  w.witnessBudget ≤ w.eventCount + w.thresholdScale + w.dependencySlack + w.slack

def zeroOneLawWindowReady (w : ZeroOneLawWindow) : Prop :=
  0 < w.eventCount ∧
    w.thresholdControlled ∧
    w.witnessControlled

def ZeroOneLawWindow.certificate (w : ZeroOneLawWindow) : ℕ :=
  w.eventCount + w.thresholdScale + w.dependencySlack + w.slack

theorem zeroOneLaw_witnessBudget_le_certificate {w : ZeroOneLawWindow}
    (h : zeroOneLawWindowReady w) :
    w.witnessBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hwitness⟩
  exact hwitness

def sampleZeroOneLawWindow : ZeroOneLawWindow :=
  { eventCount := 7, thresholdScale := 9, dependencySlack := 3, witnessBudget := 18, slack := 0 }

example : zeroOneLawWindowReady sampleZeroOneLawWindow := by
  norm_num [zeroOneLawWindowReady, ZeroOneLawWindow.thresholdControlled,
    ZeroOneLawWindow.witnessControlled, sampleZeroOneLawWindow]

example : sampleZeroOneLawWindow.certificate = 19 := by
  native_decide


structure ZeroOneLawSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ZeroOneLawSchemasBudgetCertificate.controlled
    (c : ZeroOneLawSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ZeroOneLawSchemasBudgetCertificate.budgetControlled
    (c : ZeroOneLawSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ZeroOneLawSchemasBudgetCertificate.Ready
    (c : ZeroOneLawSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ZeroOneLawSchemasBudgetCertificate.size
    (c : ZeroOneLawSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem zeroOneLawSchemas_budgetCertificate_le_size
    (c : ZeroOneLawSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleZeroOneLawSchemasBudgetCertificate :
    ZeroOneLawSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleZeroOneLawSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ZeroOneLawSchemasBudgetCertificate.controlled,
      sampleZeroOneLawSchemasBudgetCertificate]
  · norm_num [ZeroOneLawSchemasBudgetCertificate.budgetControlled,
      sampleZeroOneLawSchemasBudgetCertificate]

example : sampleZeroOneLawSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ZeroOneLawSchemasBudgetCertificate.controlled,
      sampleZeroOneLawSchemasBudgetCertificate]
  · norm_num [ZeroOneLawSchemasBudgetCertificate.budgetControlled,
      sampleZeroOneLawSchemasBudgetCertificate]

example :
    sampleZeroOneLawSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleZeroOneLawSchemasBudgetCertificate.size := by
  apply zeroOneLawSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ZeroOneLawSchemasBudgetCertificate.controlled,
      sampleZeroOneLawSchemasBudgetCertificate]
  · norm_num [ZeroOneLawSchemasBudgetCertificate.budgetControlled,
      sampleZeroOneLawSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleZeroOneLawSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleZeroOneLawSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ZeroOneLawSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleZeroOneLawSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleZeroOneLawSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ZeroOneLawSchemas
