import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Ratio Tauberian schemas.

The module stores finite ratio bounds that are used as hypotheses for
coefficient-level Tauberian conclusions.
-/

namespace AnalyticCombinatorics.AppC.RatioTauberianSchemas

structure RatioData where
  numerator : ℕ
  denominator : ℕ
  lowerBound : ℕ
  upperBound : ℕ
deriving DecidableEq, Repr

def positiveDenominator (d : RatioData) : Prop :=
  0 < d.denominator

def ratioBracketed (d : RatioData) : Prop :=
  d.lowerBound * d.denominator ≤ d.numerator ∧
    d.numerator ≤ d.upperBound * d.denominator

def ratioReady (d : RatioData) : Prop :=
  positiveDenominator d ∧ ratioBracketed d

theorem ratioReady.bracket {d : RatioData}
    (h : ratioReady d) :
    ratioBracketed d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

def sampleRatio : RatioData :=
  { numerator := 9, denominator := 3, lowerBound := 2, upperBound := 4 }

example : ratioReady sampleRatio := by
  norm_num [ratioReady, positiveDenominator, ratioBracketed, sampleRatio]

example : ratioBracketed sampleRatio := by
  norm_num [ratioBracketed, sampleRatio]

structure RatioWindow where
  index : ℕ
  numerator : ℕ
  denominator : ℕ
  targetRatio : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RatioWindow.denominatorReady (w : RatioWindow) : Prop :=
  0 < w.denominator

def RatioWindow.targetControlled (w : RatioWindow) : Prop :=
  w.numerator ≤ w.targetRatio * w.denominator + w.slack

def RatioWindow.ready (w : RatioWindow) : Prop :=
  w.denominatorReady ∧ w.targetControlled

def RatioWindow.certificate (w : RatioWindow) : ℕ :=
  w.index + w.numerator + w.denominator + w.targetRatio + w.slack

theorem numerator_le_certificate (w : RatioWindow) :
    w.numerator ≤ w.certificate := by
  unfold RatioWindow.certificate
  omega

def sampleRatioWindow : RatioWindow :=
  { index := 5, numerator := 21, denominator := 7, targetRatio := 3, slack := 0 }

example : sampleRatioWindow.ready := by
  norm_num [sampleRatioWindow, RatioWindow.ready, RatioWindow.denominatorReady,
    RatioWindow.targetControlled]

structure RatioRefinementWindow where
  indexWindow : ℕ
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  ratioBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RatioRefinementWindow.numeratorControlled
    (w : RatioRefinementWindow) : Prop :=
  w.numeratorWindow ≤ w.ratioBudget * w.denominatorWindow + w.slack

def ratioRefinementWindowReady (w : RatioRefinementWindow) : Prop :=
  0 < w.denominatorWindow ∧ w.numeratorControlled ∧
    w.ratioBudget ≤ w.indexWindow + w.numeratorWindow + w.slack

def RatioRefinementWindow.certificate (w : RatioRefinementWindow) : ℕ :=
  w.indexWindow + w.numeratorWindow + w.denominatorWindow + w.ratioBudget + w.slack

theorem ratioRefinement_ratioBudget_le_certificate
    (w : RatioRefinementWindow) :
    w.ratioBudget ≤ w.certificate := by
  unfold RatioRefinementWindow.certificate
  omega

def sampleRatioRefinementWindow : RatioRefinementWindow :=
  { indexWindow := 5, numeratorWindow := 21, denominatorWindow := 7,
    ratioBudget := 3, slack := 0 }

example : ratioRefinementWindowReady sampleRatioRefinementWindow := by
  norm_num [ratioRefinementWindowReady,
    RatioRefinementWindow.numeratorControlled, sampleRatioRefinementWindow]


structure RatioTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RatioTauberianSchemasBudgetCertificate.controlled
    (c : RatioTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RatioTauberianSchemasBudgetCertificate.budgetControlled
    (c : RatioTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RatioTauberianSchemasBudgetCertificate.Ready
    (c : RatioTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RatioTauberianSchemasBudgetCertificate.size
    (c : RatioTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem ratioTauberianSchemas_budgetCertificate_le_size
    (c : RatioTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRatioTauberianSchemasBudgetCertificate :
    RatioTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRatioTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RatioTauberianSchemasBudgetCertificate.controlled,
      sampleRatioTauberianSchemasBudgetCertificate]
  · norm_num [RatioTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRatioTauberianSchemasBudgetCertificate]

example : sampleRatioTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RatioTauberianSchemasBudgetCertificate.controlled,
      sampleRatioTauberianSchemasBudgetCertificate]
  · norm_num [RatioTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRatioTauberianSchemasBudgetCertificate]

example :
    sampleRatioTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRatioTauberianSchemasBudgetCertificate.size := by
  apply ratioTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RatioTauberianSchemasBudgetCertificate.controlled,
      sampleRatioTauberianSchemasBudgetCertificate]
  · norm_num [RatioTauberianSchemasBudgetCertificate.budgetControlled,
      sampleRatioTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRatioTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRatioTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RatioTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRatioTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRatioTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RatioTauberianSchemas
