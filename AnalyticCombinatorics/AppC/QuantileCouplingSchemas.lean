import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quantile coupling schemas.

This module records finite bookkeeping for quantile couplings: a positive
coupling scale controls quantile error with calibration slack.
-/

namespace AnalyticCombinatorics.AppC.QuantileCouplingSchemas

structure QuantileCouplingData where
  couplingScale : ℕ
  quantileError : ℕ
  calibrationSlack : ℕ
deriving DecidableEq, Repr

def hasCouplingScale (d : QuantileCouplingData) : Prop :=
  0 < d.couplingScale

def quantileErrorControlled (d : QuantileCouplingData) : Prop :=
  d.quantileError ≤ d.couplingScale + d.calibrationSlack

def quantileCouplingReady (d : QuantileCouplingData) : Prop :=
  hasCouplingScale d ∧ quantileErrorControlled d

def quantileCouplingBudget (d : QuantileCouplingData) : ℕ :=
  d.couplingScale + d.quantileError + d.calibrationSlack

theorem quantileCouplingReady.hasCouplingScale {d : QuantileCouplingData}
    (h : quantileCouplingReady d) :
    hasCouplingScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem quantileError_le_budget (d : QuantileCouplingData) :
    d.quantileError ≤ quantileCouplingBudget d := by
  unfold quantileCouplingBudget
  omega

def sampleQuantileCouplingData : QuantileCouplingData :=
  { couplingScale := 6, quantileError := 8, calibrationSlack := 3 }

example : quantileCouplingReady sampleQuantileCouplingData := by
  norm_num [quantileCouplingReady, hasCouplingScale]
  norm_num [quantileErrorControlled, sampleQuantileCouplingData]

example : quantileCouplingBudget sampleQuantileCouplingData = 17 := by
  native_decide

structure QuantileCouplingWindow where
  couplingWindow : ℕ
  quantileErrorWindow : ℕ
  calibrationSlack : ℕ
  quantileBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuantileCouplingWindow.errorControlled (w : QuantileCouplingWindow) : Prop :=
  w.quantileErrorWindow ≤ w.couplingWindow + w.calibrationSlack + w.slack

def quantileCouplingWindowReady (w : QuantileCouplingWindow) : Prop :=
  0 < w.couplingWindow ∧ w.errorControlled ∧
    w.quantileBudget ≤ w.couplingWindow + w.quantileErrorWindow + w.slack

def QuantileCouplingWindow.certificate (w : QuantileCouplingWindow) : ℕ :=
  w.couplingWindow + w.quantileErrorWindow + w.calibrationSlack + w.quantileBudget + w.slack

theorem quantileCoupling_quantileBudget_le_certificate
    (w : QuantileCouplingWindow) :
    w.quantileBudget ≤ w.certificate := by
  unfold QuantileCouplingWindow.certificate
  omega

def sampleQuantileCouplingWindow : QuantileCouplingWindow :=
  { couplingWindow := 5, quantileErrorWindow := 7, calibrationSlack := 2,
    quantileBudget := 14, slack := 2 }

example : quantileCouplingWindowReady sampleQuantileCouplingWindow := by
  norm_num [quantileCouplingWindowReady, QuantileCouplingWindow.errorControlled,
    sampleQuantileCouplingWindow]


structure QuantileCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuantileCouplingSchemasBudgetCertificate.controlled
    (c : QuantileCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QuantileCouplingSchemasBudgetCertificate.budgetControlled
    (c : QuantileCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QuantileCouplingSchemasBudgetCertificate.Ready
    (c : QuantileCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuantileCouplingSchemasBudgetCertificate.size
    (c : QuantileCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem quantileCouplingSchemas_budgetCertificate_le_size
    (c : QuantileCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuantileCouplingSchemasBudgetCertificate :
    QuantileCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQuantileCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuantileCouplingSchemasBudgetCertificate.controlled,
      sampleQuantileCouplingSchemasBudgetCertificate]
  · norm_num [QuantileCouplingSchemasBudgetCertificate.budgetControlled,
      sampleQuantileCouplingSchemasBudgetCertificate]

example : sampleQuantileCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuantileCouplingSchemasBudgetCertificate.controlled,
      sampleQuantileCouplingSchemasBudgetCertificate]
  · norm_num [QuantileCouplingSchemasBudgetCertificate.budgetControlled,
      sampleQuantileCouplingSchemasBudgetCertificate]

example :
    sampleQuantileCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuantileCouplingSchemasBudgetCertificate.size := by
  apply quantileCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [QuantileCouplingSchemasBudgetCertificate.controlled,
      sampleQuantileCouplingSchemasBudgetCertificate]
  · norm_num [QuantileCouplingSchemasBudgetCertificate.budgetControlled,
      sampleQuantileCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleQuantileCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuantileCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List QuantileCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQuantileCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQuantileCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.QuantileCouplingSchemas
