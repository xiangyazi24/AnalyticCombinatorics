import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quantile tightness schemas.

The schema stores finite quantile, sample, and tail budgets for tightness
checks.
-/

namespace AnalyticCombinatorics.AppC.QuantileTightnessSchemas

structure QuantileTightnessData where
  quantileRank : ℕ
  sampleSize : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def quantileWithinSample (d : QuantileTightnessData) : Prop :=
  d.quantileRank ≤ d.sampleSize

def tailControlledBySample (d : QuantileTightnessData) : Prop :=
  d.tailBudget ≤ d.sampleSize + d.quantileRank

def quantileTightnessReady (d : QuantileTightnessData) : Prop :=
  quantileWithinSample d ∧ tailControlledBySample d

def quantileTightnessBudget (d : QuantileTightnessData) : ℕ :=
  d.quantileRank + d.sampleSize + d.tailBudget

theorem quantileTightnessReady.quantile {d : QuantileTightnessData}
    (h : quantileTightnessReady d) :
    quantileWithinSample d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem tailBudget_le_quantileBudget (d : QuantileTightnessData) :
    d.tailBudget ≤ quantileTightnessBudget d := by
  unfold quantileTightnessBudget
  omega

def sampleQuantileTightnessData : QuantileTightnessData :=
  { quantileRank := 3, sampleSize := 9, tailBudget := 10 }

example : quantileTightnessReady sampleQuantileTightnessData := by
  norm_num [quantileTightnessReady, quantileWithinSample]
  norm_num [tailControlledBySample, sampleQuantileTightnessData]

example : quantileTightnessBudget sampleQuantileTightnessData = 22 := by
  native_decide

structure QuantileTightnessWindow where
  quantileRank : ℕ
  sampleSize : ℕ
  tailBudget : ℕ
  modulusBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuantileTightnessWindow.quantileControlled (w : QuantileTightnessWindow) : Prop :=
  w.quantileRank ≤ w.sampleSize + w.slack

def QuantileTightnessWindow.modulusControlled (w : QuantileTightnessWindow) : Prop :=
  w.modulusBudget ≤ w.quantileRank + w.sampleSize + w.tailBudget + w.slack

def quantileTightnessWindowReady (w : QuantileTightnessWindow) : Prop :=
  w.quantileControlled ∧
    w.tailBudget ≤ w.sampleSize + w.quantileRank + w.slack ∧
    w.modulusControlled

def QuantileTightnessWindow.certificate (w : QuantileTightnessWindow) : ℕ :=
  w.quantileRank + w.sampleSize + w.tailBudget + w.slack

theorem quantileTightness_modulusBudget_le_certificate {w : QuantileTightnessWindow}
    (h : quantileTightnessWindowReady w) :
    w.modulusBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmodulus⟩
  exact hmodulus

def sampleQuantileTightnessWindow : QuantileTightnessWindow :=
  { quantileRank := 3, sampleSize := 9, tailBudget := 10, modulusBudget := 21, slack := 0 }

example : quantileTightnessWindowReady sampleQuantileTightnessWindow := by
  norm_num [quantileTightnessWindowReady, QuantileTightnessWindow.quantileControlled,
    QuantileTightnessWindow.modulusControlled, sampleQuantileTightnessWindow]

example : sampleQuantileTightnessWindow.certificate = 22 := by
  native_decide


structure QuantileTightnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuantileTightnessSchemasBudgetCertificate.controlled
    (c : QuantileTightnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def QuantileTightnessSchemasBudgetCertificate.budgetControlled
    (c : QuantileTightnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def QuantileTightnessSchemasBudgetCertificate.Ready
    (c : QuantileTightnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuantileTightnessSchemasBudgetCertificate.size
    (c : QuantileTightnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem quantileTightnessSchemas_budgetCertificate_le_size
    (c : QuantileTightnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuantileTightnessSchemasBudgetCertificate :
    QuantileTightnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQuantileTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuantileTightnessSchemasBudgetCertificate.controlled,
      sampleQuantileTightnessSchemasBudgetCertificate]
  · norm_num [QuantileTightnessSchemasBudgetCertificate.budgetControlled,
      sampleQuantileTightnessSchemasBudgetCertificate]

example : sampleQuantileTightnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [QuantileTightnessSchemasBudgetCertificate.controlled,
      sampleQuantileTightnessSchemasBudgetCertificate]
  · norm_num [QuantileTightnessSchemasBudgetCertificate.budgetControlled,
      sampleQuantileTightnessSchemasBudgetCertificate]

example :
    sampleQuantileTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuantileTightnessSchemasBudgetCertificate.size := by
  apply quantileTightnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [QuantileTightnessSchemasBudgetCertificate.controlled,
      sampleQuantileTightnessSchemasBudgetCertificate]
  · norm_num [QuantileTightnessSchemasBudgetCertificate.budgetControlled,
      sampleQuantileTightnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleQuantileTightnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleQuantileTightnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List QuantileTightnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQuantileTightnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleQuantileTightnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.QuantileTightnessSchemas
