import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Boltzmann sampler limit schema bookkeeping.

The finite record tracks parameter budget, expected size, and variance
budget.
-/

namespace AnalyticCombinatorics.PartA.Ch3.BoltzmannLimitSchemas

structure BoltzmannData where
  parameterBudget : ℕ
  expectedSizeBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveParameter (d : BoltzmannData) : Prop :=
  0 < d.parameterBudget

def positiveVariance (d : BoltzmannData) : Prop :=
  0 < d.varianceBudget

def boltzmannLimitReady (d : BoltzmannData) : Prop :=
  positiveParameter d ∧ positiveVariance d

def boltzmannBudget (d : BoltzmannData) : ℕ :=
  d.parameterBudget + d.expectedSizeBudget + d.varianceBudget

theorem boltzmannLimitReady.parameter {d : BoltzmannData}
    (h : boltzmannLimitReady d) :
    positiveParameter d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem parameterBudget_le_boltzmannBudget (d : BoltzmannData) :
    d.parameterBudget ≤ boltzmannBudget d := by
  unfold boltzmannBudget
  omega

def sampleBoltzmann : BoltzmannData :=
  { parameterBudget := 4, expectedSizeBudget := 9, varianceBudget := 5 }

example : boltzmannLimitReady sampleBoltzmann := by
  norm_num [boltzmannLimitReady, positiveParameter, positiveVariance, sampleBoltzmann]

example : boltzmannBudget sampleBoltzmann = 18 := by
  native_decide

structure BoltzmannWindow where
  parameterBudget : ℕ
  expectedSize : ℕ
  varianceBudget : ℕ
  samplingError : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoltzmannWindow.expectedControlled (w : BoltzmannWindow) : Prop :=
  w.expectedSize ≤ w.parameterBudget * w.varianceBudget + w.slack

def BoltzmannWindow.errorControlled (w : BoltzmannWindow) : Prop :=
  w.samplingError ≤ w.parameterBudget + w.varianceBudget + w.slack

def boltzmannWindowReady (w : BoltzmannWindow) : Prop :=
  0 < w.parameterBudget ∧
    0 < w.varianceBudget ∧
    w.expectedControlled ∧
    w.errorControlled

def BoltzmannWindow.certificate (w : BoltzmannWindow) : ℕ :=
  w.parameterBudget + w.varianceBudget + w.slack

theorem boltzmann_samplingError_le_certificate {w : BoltzmannWindow}
    (h : boltzmannWindowReady w) :
    w.samplingError ≤ w.certificate := by
  rcases h with ⟨_, _, _, herror⟩
  exact herror

def sampleBoltzmannWindow : BoltzmannWindow :=
  { parameterBudget := 4, expectedSize := 9, varianceBudget := 5, samplingError := 3, slack := 0 }

example : boltzmannWindowReady sampleBoltzmannWindow := by
  norm_num [boltzmannWindowReady, BoltzmannWindow.expectedControlled,
    BoltzmannWindow.errorControlled, sampleBoltzmannWindow]

example : sampleBoltzmannWindow.certificate = 9 := by
  native_decide


structure BoltzmannLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoltzmannLimitSchemasBudgetCertificate.controlled
    (c : BoltzmannLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoltzmannLimitSchemasBudgetCertificate.budgetControlled
    (c : BoltzmannLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoltzmannLimitSchemasBudgetCertificate.Ready
    (c : BoltzmannLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoltzmannLimitSchemasBudgetCertificate.size
    (c : BoltzmannLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boltzmannLimitSchemas_budgetCertificate_le_size
    (c : BoltzmannLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoltzmannLimitSchemasBudgetCertificate :
    BoltzmannLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoltzmannLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.controlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.budgetControlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBoltzmannLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoltzmannLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBoltzmannLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.controlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.budgetControlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]

example :
    sampleBoltzmannLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoltzmannLimitSchemasBudgetCertificate.size := by
  apply boltzmannLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.controlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]
  · norm_num [BoltzmannLimitSchemasBudgetCertificate.budgetControlled,
      sampleBoltzmannLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List BoltzmannLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoltzmannLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBoltzmannLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.BoltzmannLimitSchemas
