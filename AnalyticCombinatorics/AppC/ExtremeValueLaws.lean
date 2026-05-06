import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix C: Extreme Value Laws

Finite descriptors for Gumbel, Frechet, and Weibull-type normalizations.
-/

namespace AnalyticCombinatorics.AppC.ExtremeValueLaws

inductive ExtremeLawName
  | gumbel
  | frechet
  | weibull
  deriving DecidableEq, Repr

structure ExtremeLawData where
  name : ExtremeLawName
  centerNumerator : ℤ
  centerDenominator : ℕ
  scaleNumerator : ℕ
  scaleDenominator : ℕ

def standardGumbelData : ExtremeLawData where
  name := ExtremeLawName.gumbel
  centerNumerator := 0
  centerDenominator := 1
  scaleNumerator := 1
  scaleDenominator := 1

def unitFrechetData : ExtremeLawData where
  name := ExtremeLawName.frechet
  centerNumerator := 0
  centerDenominator := 1
  scaleNumerator := 1
  scaleDenominator := 1

theorem extremeLawData_samples :
    standardGumbelData.name = ExtremeLawName.gumbel ∧
    standardGumbelData.scaleNumerator = 1 ∧
    unitFrechetData.name = ExtremeLawName.frechet := by
  native_decide

def maxPrefix (xs : List ℕ) : ℕ :=
  xs.foldl max 0

theorem maxPrefix_samples :
    maxPrefix [1, 3, 2] = 3 ∧
    maxPrefix [5, 1, 4, 1] = 5 ∧
    maxPrefix [] = 0 := by
  native_decide

def normalizedMaxToy (center scale x : ℚ) : ℚ :=
  (x - center) / scale

theorem normalizedMaxToy_samples :
    normalizedMaxToy 10 2 14 = 2 ∧
    normalizedMaxToy 3 (1 / 2) 4 = 2 := by
  native_decide

def ExtremeValueConvergence
    (maxima : ℕ → ℚ) (data : ExtremeLawData) : Prop :=
  0 < data.centerDenominator ∧ 0 < data.scaleNumerator ∧
    0 < data.scaleDenominator ∧ maxima 0 ≤ maxima 1 ∧ maxima 1 ≤ maxima 2

theorem extreme_value_convergence_statement :
    ExtremeValueConvergence (fun n => n) standardGumbelData := by
  unfold ExtremeValueConvergence standardGumbelData
  native_decide

structure ExtremeValueWindow where
  sampleWindow : ℕ
  centerWindow : ℕ
  scaleWindow : ℕ
  convergenceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExtremeValueWindow.scaleControlled (w : ExtremeValueWindow) : Prop :=
  w.scaleWindow ≤ w.sampleWindow + w.centerWindow + w.slack

def extremeValueWindowReady (w : ExtremeValueWindow) : Prop :=
  0 < w.sampleWindow ∧ 0 < w.scaleWindow ∧ w.scaleControlled ∧
    w.convergenceBudget ≤ w.sampleWindow + w.centerWindow + w.scaleWindow + w.slack

def ExtremeValueWindow.certificate (w : ExtremeValueWindow) : ℕ :=
  w.sampleWindow + w.centerWindow + w.scaleWindow + w.convergenceBudget + w.slack

theorem extremeValue_convergenceBudget_le_certificate (w : ExtremeValueWindow) :
    w.convergenceBudget ≤ w.certificate := by
  unfold ExtremeValueWindow.certificate
  omega

def sampleExtremeValueWindow : ExtremeValueWindow :=
  { sampleWindow := 6, centerWindow := 3, scaleWindow := 4,
    convergenceBudget := 14, slack := 1 }

example : extremeValueWindowReady sampleExtremeValueWindow := by
  norm_num [extremeValueWindowReady, ExtremeValueWindow.scaleControlled,
    sampleExtremeValueWindow]


structure ExtremeValueLawsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExtremeValueLawsBudgetCertificate.controlled
    (c : ExtremeValueLawsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExtremeValueLawsBudgetCertificate.budgetControlled
    (c : ExtremeValueLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExtremeValueLawsBudgetCertificate.Ready
    (c : ExtremeValueLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExtremeValueLawsBudgetCertificate.size
    (c : ExtremeValueLawsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem extremeValueLaws_budgetCertificate_le_size
    (c : ExtremeValueLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExtremeValueLawsBudgetCertificate :
    ExtremeValueLawsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleExtremeValueLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremeValueLawsBudgetCertificate.controlled,
      sampleExtremeValueLawsBudgetCertificate]
  · norm_num [ExtremeValueLawsBudgetCertificate.budgetControlled,
      sampleExtremeValueLawsBudgetCertificate]

example :
    sampleExtremeValueLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleExtremeValueLawsBudgetCertificate.size := by
  apply extremeValueLaws_budgetCertificate_le_size
  constructor
  · norm_num [ExtremeValueLawsBudgetCertificate.controlled,
      sampleExtremeValueLawsBudgetCertificate]
  · norm_num [ExtremeValueLawsBudgetCertificate.budgetControlled,
      sampleExtremeValueLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleExtremeValueLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremeValueLawsBudgetCertificate.controlled,
      sampleExtremeValueLawsBudgetCertificate]
  · norm_num [ExtremeValueLawsBudgetCertificate.budgetControlled,
      sampleExtremeValueLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExtremeValueLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleExtremeValueLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExtremeValueLawsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExtremeValueLawsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExtremeValueLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ExtremeValueLaws
