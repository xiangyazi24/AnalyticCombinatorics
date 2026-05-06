import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Chapter VI asymptotic coefficient checks.

The analytic transfer statements are represented here by finite executable
coefficient envelopes.
-/

namespace AnalyticCombinatorics.PartB.Ch6.Asymptotics

structure TransferEnvelope where
  coefficient : ℕ
  exponentialScale : ℕ
  polynomialSlack : ℕ
deriving DecidableEq, Repr

def envelopeControlled (e : TransferEnvelope) : Prop :=
  e.coefficient ≤ e.exponentialScale + e.polynomialSlack

def envelopeBudget (e : TransferEnvelope) : ℕ :=
  e.coefficient + e.exponentialScale + e.polynomialSlack

theorem coefficient_le_budget (e : TransferEnvelope) :
    e.coefficient ≤ envelopeBudget e := by
  unfold envelopeBudget
  omega

def sampleEnvelope : TransferEnvelope :=
  { coefficient := 42, exponentialScale := 64, polynomialSlack := 7 }

example : envelopeControlled sampleEnvelope := by
  norm_num [envelopeControlled, sampleEnvelope]

example : envelopeBudget sampleEnvelope = 113 := by
  native_decide

structure SingularityTransferWindow where
  order : ℕ
  radiusNumerator : ℕ
  radiusDenominator : ℕ
  coefficientBound : ℕ
  remainderBound : ℕ
deriving DecidableEq, Repr

def SingularityTransferWindow.radiusPositive (w : SingularityTransferWindow) : Prop :=
  0 < w.radiusNumerator ∧ 0 < w.radiusDenominator

def SingularityTransferWindow.remainderControlled (w : SingularityTransferWindow) : Prop :=
  w.remainderBound ≤ w.coefficientBound + w.order

def SingularityTransferWindow.certificate (w : SingularityTransferWindow) : ℕ :=
  w.order + w.radiusNumerator + w.radiusDenominator + w.coefficientBound + w.remainderBound

theorem remainderBound_le_certificate (w : SingularityTransferWindow) :
    w.remainderBound ≤ w.certificate := by
  unfold SingularityTransferWindow.certificate
  omega

def sampleSingularityTransferWindow : SingularityTransferWindow :=
  { order := 3, radiusNumerator := 1, radiusDenominator := 2,
    coefficientBound := 64, remainderBound := 12 }

example : sampleSingularityTransferWindow.radiusPositive := by
  norm_num [sampleSingularityTransferWindow, SingularityTransferWindow.radiusPositive]

example : sampleSingularityTransferWindow.remainderControlled := by
  norm_num [sampleSingularityTransferWindow, SingularityTransferWindow.remainderControlled]


structure AsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticsBudgetCertificate.controlled
    (c : AsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticsBudgetCertificate.budgetControlled
    (c : AsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticsBudgetCertificate.Ready
    (c : AsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticsBudgetCertificate.size
    (c : AsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptotics_budgetCertificate_le_size
    (c : AsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticsBudgetCertificate :
    AsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticsBudgetCertificate.controlled,
      sampleAsymptoticsBudgetCertificate]
  · norm_num [AsymptoticsBudgetCertificate.budgetControlled,
      sampleAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticsBudgetCertificate.controlled,
      sampleAsymptoticsBudgetCertificate]
  · norm_num [AsymptoticsBudgetCertificate.budgetControlled,
      sampleAsymptoticsBudgetCertificate]

example :
    sampleAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticsBudgetCertificate.size := by
  apply asymptotics_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticsBudgetCertificate.controlled,
      sampleAsymptoticsBudgetCertificate]
  · norm_num [AsymptoticsBudgetCertificate.budgetControlled,
      sampleAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.Asymptotics
