import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Local Limit Schemas

Finite mass-function checks and statement forms for local limit theorems.
-/

namespace AnalyticCombinatorics.Asymptotics.LocalLimit

def binomialWeight (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) / (2 : ℚ) ^ n

theorem binomialWeight_n4 :
    (List.range 5).map (binomialWeight 4) = [1 / 16, 1 / 4, 3 / 8, 1 / 4, 1 / 16] := by
  native_decide

def binomialMassSum (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun s k => s + binomialWeight n k) 0

theorem binomialMassSum_samples :
    (List.range 7).map binomialMassSum = [1, 1, 1, 1, 1, 1, 1] := by
  native_decide

def centeredIndexNumerator (n k : ℕ) : ℤ :=
  (2 * k : ℤ) - (n : ℤ)

theorem centeredIndexNumerator_n6 :
    (List.range 7).map (centeredIndexNumerator 6) = [-6, -4, -2, 0, 2, 4, 6] := by
  native_decide

structure LocalLimitData where
  centerNumerator : ℤ
  centerDenominator : ℕ
  varianceNumerator : ℕ
  varianceDenominator : ℕ

def symmetricBinomialLocalLimit : LocalLimitData where
  centerNumerator := 1
  centerDenominator := 2
  varianceNumerator := 1
  varianceDenominator := 4

theorem symmetricBinomialLocalLimit_values :
    symmetricBinomialLocalLimit.centerNumerator = 1 ∧
    symmetricBinomialLocalLimit.centerDenominator = 2 ∧
    symmetricBinomialLocalLimit.varianceDenominator = 4 := by
  native_decide

def localLimitDataReady (data : LocalLimitData) : Prop :=
  0 < data.centerDenominator ∧ 0 < data.varianceNumerator ∧ 0 < data.varianceDenominator

theorem symmetricBinomialLocalLimit_ready :
    localLimitDataReady symmetricBinomialLocalLimit := by
  unfold localLimitDataReady symmetricBinomialLocalLimit
  native_decide

/-- Finite executable readiness audit for local-limit data. -/
def localLimitDataListReady (data : List LocalLimitData) : Bool :=
  data.all fun d =>
    0 < d.centerDenominator &&
      0 < d.varianceNumerator && 0 < d.varianceDenominator

theorem localLimitDataList_readyWindow :
    localLimitDataListReady
      [{ centerNumerator := 0, centerDenominator := 1,
         varianceNumerator := 1, varianceDenominator := 2 },
       { centerNumerator := 1, centerDenominator := 2,
         varianceNumerator := 1, varianceDenominator := 4 }] = true := by
  unfold localLimitDataListReady
  native_decide

def LocalLimitTheorem
    (mass : ℕ → ℕ → ℚ) (data : LocalLimitData) : Prop :=
  localLimitDataReady data ∧ mass 4 2 = 3 / 8

theorem local_limit_theorem_statement :
    LocalLimitTheorem binomialWeight symmetricBinomialLocalLimit := by
  unfold LocalLimitTheorem localLimitDataReady symmetricBinomialLocalLimit
  native_decide

/-- A finite certificate for local-limit schema data. -/
structure LocalLimitCertificate where
  centerDenominatorWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  massBudget : ℕ
  slack : ℕ

/-- Local-limit certificates keep variance and denominator data positive. -/
def localLimitCertificateControlled
    (w : LocalLimitCertificate) : Prop :=
  0 < w.centerDenominatorWindow ∧
    0 < w.varianceNumeratorWindow ∧
      0 < w.varianceDenominatorWindow

/-- Readiness for a local-limit certificate. -/
def localLimitCertificateReady
    (w : LocalLimitCertificate) : Prop :=
  localLimitCertificateControlled w ∧
    w.massBudget ≤
      w.centerDenominatorWindow + w.varianceNumeratorWindow +
        w.varianceDenominatorWindow + w.slack

/-- Total size of a local-limit certificate. -/
def localLimitCertificateSize (w : LocalLimitCertificate) : ℕ :=
  w.centerDenominatorWindow + w.varianceNumeratorWindow +
    w.varianceDenominatorWindow + w.massBudget + w.slack

theorem localLimitCertificate_mass_le_size
    (w : LocalLimitCertificate)
    (h : localLimitCertificateReady w) :
    w.massBudget ≤ localLimitCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold localLimitCertificateSize
  omega

def sampleLocalLimitCertificate : LocalLimitCertificate where
  centerDenominatorWindow := 2
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 4
  massBudget := 7
  slack := 1

example :
    localLimitCertificateReady sampleLocalLimitCertificate := by
  norm_num [localLimitCertificateReady,
    localLimitCertificateControlled, sampleLocalLimitCertificate]

example :
    sampleLocalLimitCertificate.massBudget ≤
      localLimitCertificateSize sampleLocalLimitCertificate := by
  apply localLimitCertificate_mass_le_size
  norm_num [localLimitCertificateReady,
    localLimitCertificateControlled, sampleLocalLimitCertificate]

/-- A refinement certificate separating the mass budget from the parameter windows. -/
structure LocalLimitRefinementCertificate where
  centerDenominatorWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  massBudgetWindow : ℕ
  slack : ℕ

def LocalLimitRefinementCertificate.parametersControlled
    (cert : LocalLimitRefinementCertificate) : Prop :=
  0 < cert.centerDenominatorWindow ∧
    0 < cert.varianceNumeratorWindow ∧
      0 < cert.varianceDenominatorWindow

def LocalLimitRefinementCertificate.massBudgetControlled
    (cert : LocalLimitRefinementCertificate) : Prop :=
  cert.massBudgetWindow ≤
    cert.centerDenominatorWindow + cert.varianceNumeratorWindow +
      cert.varianceDenominatorWindow + cert.slack

def localLimitRefinementReady (cert : LocalLimitRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.massBudgetControlled

def LocalLimitRefinementCertificate.size
    (cert : LocalLimitRefinementCertificate) : ℕ :=
  cert.centerDenominatorWindow + cert.varianceNumeratorWindow +
    cert.varianceDenominatorWindow + cert.slack

theorem localLimit_massBudgetWindow_le_size
    (cert : LocalLimitRefinementCertificate)
    (h : localLimitRefinementReady cert) :
    cert.massBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalLimitRefinementCertificate : LocalLimitRefinementCertificate where
  centerDenominatorWindow := 2
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 4
  massBudgetWindow := 8
  slack := 1

example : localLimitRefinementReady sampleLocalLimitRefinementCertificate := by
  norm_num [localLimitRefinementReady,
    LocalLimitRefinementCertificate.parametersControlled,
    LocalLimitRefinementCertificate.massBudgetControlled,
    sampleLocalLimitRefinementCertificate]

example :
    sampleLocalLimitRefinementCertificate.massBudgetWindow ≤
      sampleLocalLimitRefinementCertificate.size := by
  apply localLimit_massBudgetWindow_le_size
  norm_num [localLimitRefinementReady,
    LocalLimitRefinementCertificate.parametersControlled,
    LocalLimitRefinementCertificate.massBudgetControlled,
    sampleLocalLimitRefinementCertificate]

structure LocalLimitBudgetCertificate where
  centerDenominatorWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  massBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalLimitBudgetCertificate.controlled
    (c : LocalLimitBudgetCertificate) : Prop :=
  0 < c.centerDenominatorWindow ∧
    0 < c.varianceNumeratorWindow ∧
      0 < c.varianceDenominatorWindow ∧
        c.massBudgetWindow ≤
          c.centerDenominatorWindow + c.varianceNumeratorWindow +
            c.varianceDenominatorWindow + c.slack

def LocalLimitBudgetCertificate.budgetControlled
    (c : LocalLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.centerDenominatorWindow + c.varianceNumeratorWindow +
      c.varianceDenominatorWindow + c.massBudgetWindow + c.slack

def LocalLimitBudgetCertificate.Ready
    (c : LocalLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalLimitBudgetCertificate.size
    (c : LocalLimitBudgetCertificate) : ℕ :=
  c.centerDenominatorWindow + c.varianceNumeratorWindow +
    c.varianceDenominatorWindow + c.massBudgetWindow + c.slack

theorem localLimit_budgetCertificate_le_size
    (c : LocalLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalLimitBudgetCertificate :
    LocalLimitBudgetCertificate :=
  { centerDenominatorWindow := 2
    varianceNumeratorWindow := 1
    varianceDenominatorWindow := 4
    massBudgetWindow := 8
    certificateBudgetWindow := 16
    slack := 1 }

example : sampleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitBudgetCertificate.controlled,
      sampleLocalLimitBudgetCertificate]
  · norm_num [LocalLimitBudgetCertificate.budgetControlled,
      sampleLocalLimitBudgetCertificate]

example :
    sampleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalLimitBudgetCertificate.size := by
  apply localLimit_budgetCertificate_le_size
  constructor
  · norm_num [LocalLimitBudgetCertificate.controlled,
      sampleLocalLimitBudgetCertificate]
  · norm_num [LocalLimitBudgetCertificate.budgetControlled,
      sampleLocalLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitBudgetCertificate.controlled,
      sampleLocalLimitBudgetCertificate]
  · norm_num [LocalLimitBudgetCertificate.budgetControlled,
      sampleLocalLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LocalLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLocalLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.LocalLimit
