import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer bookkeeping for Cauchy coefficient estimates.

The analytic estimate contributes a radius and boundary bound; this file
records the finite arithmetic used by coefficient majorants.
-/

namespace AnalyticCombinatorics.AppB.CauchyEstimates

structure CauchyDatum where
  radius : ℕ
  boundaryBound : ℕ
  coeffIndex : ℕ
deriving DecidableEq, Repr

def radiusPositive (d : CauchyDatum) : Prop :=
  0 < d.radius

def cauchyMajorantNumerator (d : CauchyDatum) : ℕ :=
  d.boundaryBound

def cauchyMajorantDenominator (d : CauchyDatum) : ℕ :=
  d.radius ^ d.coeffIndex

def cauchyAdmissible (d : CauchyDatum) : Prop :=
  radiusPositive d ∧ 0 < cauchyMajorantDenominator d

theorem denominator_positive {d : CauchyDatum}
    (h : radiusPositive d) :
    0 < cauchyMajorantDenominator d := by
  unfold cauchyMajorantDenominator radiusPositive at *
  exact pow_pos h d.coeffIndex

theorem cauchyAdmissible_intro {d : CauchyDatum}
    (h : radiusPositive d) :
    cauchyAdmissible d := by
  exact ⟨h, denominator_positive h⟩

def sampleCauchy : CauchyDatum :=
  { radius := 2, boundaryBound := 9, coeffIndex := 4 }

example : cauchyMajorantNumerator sampleCauchy = 9 := by
  native_decide

example : cauchyMajorantDenominator sampleCauchy = 16 := by
  native_decide

example : cauchyAdmissible sampleCauchy := by
  norm_num [cauchyAdmissible, radiusPositive, cauchyMajorantDenominator, sampleCauchy]

/-- Finite executable Cauchy-admissibility audit. -/
def cauchyAdmissibleListReady (data : List CauchyDatum) : Bool :=
  data.all fun d => 0 < d.radius && 0 < cauchyMajorantDenominator d

theorem cauchyAdmissibleList_readyWindow :
    cauchyAdmissibleListReady
      [{ radius := 2, boundaryBound := 9, coeffIndex := 4 },
       { radius := 3, boundaryBound := 7, coeffIndex := 2 }] = true := by
  unfold cauchyAdmissibleListReady cauchyMajorantDenominator
  native_decide


structure CauchyEstimatesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CauchyEstimatesBudgetCertificate.controlled
    (c : CauchyEstimatesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CauchyEstimatesBudgetCertificate.budgetControlled
    (c : CauchyEstimatesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CauchyEstimatesBudgetCertificate.Ready
    (c : CauchyEstimatesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CauchyEstimatesBudgetCertificate.size
    (c : CauchyEstimatesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cauchyEstimates_budgetCertificate_le_size
    (c : CauchyEstimatesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCauchyEstimatesBudgetCertificate :
    CauchyEstimatesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCauchyEstimatesBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyEstimatesBudgetCertificate.controlled,
      sampleCauchyEstimatesBudgetCertificate]
  · norm_num [CauchyEstimatesBudgetCertificate.budgetControlled,
      sampleCauchyEstimatesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCauchyEstimatesBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyEstimatesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCauchyEstimatesBudgetCertificate.Ready := by
  constructor
  · norm_num [CauchyEstimatesBudgetCertificate.controlled,
      sampleCauchyEstimatesBudgetCertificate]
  · norm_num [CauchyEstimatesBudgetCertificate.budgetControlled,
      sampleCauchyEstimatesBudgetCertificate]

example :
    sampleCauchyEstimatesBudgetCertificate.certificateBudgetWindow ≤
      sampleCauchyEstimatesBudgetCertificate.size := by
  apply cauchyEstimates_budgetCertificate_le_size
  constructor
  · norm_num [CauchyEstimatesBudgetCertificate.controlled,
      sampleCauchyEstimatesBudgetCertificate]
  · norm_num [CauchyEstimatesBudgetCertificate.budgetControlled,
      sampleCauchyEstimatesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CauchyEstimatesBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCauchyEstimatesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCauchyEstimatesBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.CauchyEstimates
