import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: equivalent definitions of analyticity.

Finite consistency windows for power-series, Cauchy, and derivative data.
-/

namespace AnalyticCombinatorics.AppB.AnalyticityEquivalence

/-- Finite power-series coefficient bound. -/
def powerSeriesRadiusCheck
    (coeff : ℕ → ℕ) (majorant N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ majorant ^ n

/-- Finite Cauchy-derivative bound using factorial-scaled samples. -/
def cauchyDerivativeBoundCheck
    (derivative : ℕ → ℕ) (majorant N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => derivative n ≤ n.factorial * majorant ^ n

def geometricCoeff (base n : ℕ) : ℕ :=
  base ^ n

def geometricDerivativeProxy (base n : ℕ) : ℕ :=
  n.factorial * base ^ n

theorem geometric_analyticityEquivalenceWindow :
    powerSeriesRadiusCheck (geometricCoeff 2) 2 12 = true ∧
      cauchyDerivativeBoundCheck (geometricDerivativeProxy 2) 2 12 = true := by
  unfold powerSeriesRadiusCheck cauchyDerivativeBoundCheck
    geometricCoeff geometricDerivativeProxy
  native_decide

structure AnalyticityWitness where
  seriesRadius : ℕ
  cauchyRadius : ℕ
  derivativeOrder : ℕ
deriving DecidableEq, Repr

def radiiCompatible (w : AnalyticityWitness) : Prop :=
  0 < w.seriesRadius ∧ 0 < w.cauchyRadius

def derivativeWindowControlled (w : AnalyticityWitness) : Prop :=
  w.derivativeOrder ≤ w.seriesRadius + w.cauchyRadius

def analyticityWitnessReady (w : AnalyticityWitness) : Prop :=
  radiiCompatible w ∧ derivativeWindowControlled w

def analyticityWitnessBudget (w : AnalyticityWitness) : ℕ :=
  w.seriesRadius + w.cauchyRadius + w.derivativeOrder

theorem derivativeOrder_le_budget (w : AnalyticityWitness) :
    w.derivativeOrder ≤ analyticityWitnessBudget w := by
  unfold analyticityWitnessBudget
  omega

def sampleAnalyticityWitness : AnalyticityWitness :=
  { seriesRadius := 5, cauchyRadius := 4, derivativeOrder := 7 }

example : analyticityWitnessReady sampleAnalyticityWitness := by
  norm_num [analyticityWitnessReady, radiiCompatible,
    derivativeWindowControlled, sampleAnalyticityWitness]

structure AnalyticityEquivalenceBudgetCertificate where
  seriesWindow : ℕ
  cauchyWindow : ℕ
  derivativeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticityEquivalenceBudgetCertificate.controlled
    (c : AnalyticityEquivalenceBudgetCertificate) : Prop :=
  0 < c.seriesWindow ∧ 0 < c.cauchyWindow ∧
    c.derivativeWindow ≤ c.seriesWindow + c.cauchyWindow + c.slack

def AnalyticityEquivalenceBudgetCertificate.budgetControlled
    (c : AnalyticityEquivalenceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.seriesWindow + c.cauchyWindow + c.derivativeWindow + c.slack

def AnalyticityEquivalenceBudgetCertificate.Ready
    (c : AnalyticityEquivalenceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticityEquivalenceBudgetCertificate.size
    (c : AnalyticityEquivalenceBudgetCertificate) : ℕ :=
  c.seriesWindow + c.cauchyWindow + c.derivativeWindow + c.slack

theorem analyticityEquivalence_budgetCertificate_le_size
    (c : AnalyticityEquivalenceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAnalyticityEquivalenceBudgetCertificate :
    AnalyticityEquivalenceBudgetCertificate :=
  { seriesWindow := 5
    cauchyWindow := 4
    derivativeWindow := 7
    certificateBudgetWindow := 17
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticityEquivalenceBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticityEquivalenceBudgetCertificate.controlled,
      sampleAnalyticityEquivalenceBudgetCertificate]
  · norm_num [AnalyticityEquivalenceBudgetCertificate.budgetControlled,
      sampleAnalyticityEquivalenceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticityEquivalenceBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticityEquivalenceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticityEquivalenceBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticityEquivalenceBudgetCertificate.controlled,
      sampleAnalyticityEquivalenceBudgetCertificate]
  · norm_num [AnalyticityEquivalenceBudgetCertificate.budgetControlled,
      sampleAnalyticityEquivalenceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticityEquivalenceBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAnalyticityEquivalenceBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAnalyticityEquivalenceBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticityEquivalence
