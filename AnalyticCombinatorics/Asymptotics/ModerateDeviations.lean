import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Moderate Deviations

Finite exponential-tail and scale-window models for moderate deviation
schemas.
-/

namespace AnalyticCombinatorics.Asymptotics.ModerateDeviations

def gaussianTailProxy (k : ℕ) : ℚ :=
  1 / (2 : ℚ) ^ (k * k)

theorem gaussianTailProxy_samples :
    (List.range 5).map gaussianTailProxy = [1, 1 / 2, 1 / 16, 1 / 512, 1 / 65536] := by
  native_decide

def scaleWindow (n alphaNumerator alphaDenominator : ℕ) : ℕ :=
  n ^ alphaNumerator / alphaDenominator

theorem scaleWindow_samples :
    scaleWindow 10 2 5 = 20 ∧
    scaleWindow 8 3 4 = 128 := by
  native_decide

def tailDominanceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun k => gaussianTailProxy (k + 1) ≤ gaussianTailProxy k

theorem tailDominanceCheck_12 :
    tailDominanceCheck 12 = true := by
  native_decide

structure ModerateDeviationData where
  varianceNumerator : ℕ
  varianceDenominator : ℕ
  windowPowerNumerator : ℕ
  windowPowerDenominator : ℕ

def gaussianModerateDeviationData : ModerateDeviationData where
  varianceNumerator := 1
  varianceDenominator := 1
  windowPowerNumerator := 2
  windowPowerDenominator := 3

theorem gaussianModerateDeviationData_values :
    gaussianModerateDeviationData.varianceNumerator = 1 ∧
    gaussianModerateDeviationData.windowPowerNumerator = 2 ∧
    gaussianModerateDeviationData.windowPowerDenominator = 3 := by
  native_decide

def moderateDeviationDataReady (data : ModerateDeviationData) : Prop :=
  0 < data.varianceNumerator ∧ 0 < data.varianceDenominator ∧
    0 < data.windowPowerDenominator

theorem gaussianModerateDeviationData_ready :
    moderateDeviationDataReady gaussianModerateDeviationData := by
  unfold moderateDeviationDataReady gaussianModerateDeviationData
  native_decide

/-- Finite executable readiness audit for moderate-deviation data. -/
def moderateDeviationDataListReady
    (data : List ModerateDeviationData) : Bool :=
  data.all fun d =>
    0 < d.varianceNumerator &&
      0 < d.varianceDenominator && 0 < d.windowPowerDenominator

theorem moderateDeviationDataList_readyWindow :
    moderateDeviationDataListReady
      [{ varianceNumerator := 1, varianceDenominator := 2,
         windowPowerNumerator := 1, windowPowerDenominator := 2 },
       { varianceNumerator := 1, varianceDenominator := 1,
         windowPowerNumerator := 2, windowPowerDenominator := 3 }] = true := by
  unfold moderateDeviationDataListReady
  native_decide

def ModerateDeviationSchema
    (mass : ℕ → ℕ → ℚ) (data : ModerateDeviationData) : Prop :=
  moderateDeviationDataReady data ∧ mass 0 0 = 1 ∧ mass 0 3 = 1 / 512

def moderateMassWitness (_n k : ℕ) : ℚ :=
  gaussianTailProxy k

theorem moderate_deviation_schema_statement :
    ModerateDeviationSchema moderateMassWitness gaussianModerateDeviationData := by
  unfold ModerateDeviationSchema moderateDeviationDataReady gaussianModerateDeviationData
    moderateMassWitness gaussianTailProxy
  native_decide

/-- A finite certificate for moderate-deviation schema data. -/
structure ModerateDeviationCertificate where
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  powerDenominatorWindow : ℕ
  tailBudget : ℕ
  slack : ℕ

/-- Moderate-deviation certificates keep variance and window denominators positive. -/
def moderateDeviationCertificateControlled
    (w : ModerateDeviationCertificate) : Prop :=
  0 < w.varianceNumeratorWindow ∧
    0 < w.varianceDenominatorWindow ∧
      0 < w.powerDenominatorWindow

/-- Readiness for a moderate-deviation certificate. -/
def moderateDeviationCertificateReady
    (w : ModerateDeviationCertificate) : Prop :=
  moderateDeviationCertificateControlled w ∧
    w.tailBudget ≤
      w.varianceNumeratorWindow + w.varianceDenominatorWindow +
        w.powerDenominatorWindow + w.slack

/-- Total size of a moderate-deviation certificate. -/
def moderateDeviationCertificateSize
    (w : ModerateDeviationCertificate) : ℕ :=
  w.varianceNumeratorWindow + w.varianceDenominatorWindow +
    w.powerDenominatorWindow + w.tailBudget + w.slack

theorem moderateDeviationCertificate_tail_le_size
    (w : ModerateDeviationCertificate)
    (h : moderateDeviationCertificateReady w) :
    w.tailBudget ≤ moderateDeviationCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold moderateDeviationCertificateSize
  omega

def sampleModerateDeviationCertificate : ModerateDeviationCertificate where
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 1
  powerDenominatorWindow := 3
  tailBudget := 5
  slack := 1

example :
    moderateDeviationCertificateReady sampleModerateDeviationCertificate := by
  norm_num [moderateDeviationCertificateReady,
    moderateDeviationCertificateControlled, sampleModerateDeviationCertificate]

example :
    sampleModerateDeviationCertificate.tailBudget ≤
      moderateDeviationCertificateSize sampleModerateDeviationCertificate := by
  apply moderateDeviationCertificate_tail_le_size
  norm_num [moderateDeviationCertificateReady,
    moderateDeviationCertificateControlled, sampleModerateDeviationCertificate]

/-- A refinement certificate with the tail budget separated from size. -/
structure ModerateDeviationRefinementCertificate where
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  powerDenominatorWindow : ℕ
  tailBudgetWindow : ℕ
  slack : ℕ

def ModerateDeviationRefinementCertificate.parametersControlled
    (cert : ModerateDeviationRefinementCertificate) : Prop :=
  0 < cert.varianceNumeratorWindow ∧
    0 < cert.varianceDenominatorWindow ∧
      0 < cert.powerDenominatorWindow

def ModerateDeviationRefinementCertificate.tailControlled
    (cert : ModerateDeviationRefinementCertificate) : Prop :=
  cert.tailBudgetWindow ≤
    cert.varianceNumeratorWindow + cert.varianceDenominatorWindow +
      cert.powerDenominatorWindow + cert.slack

def moderateDeviationRefinementReady
    (cert : ModerateDeviationRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.tailControlled

def ModerateDeviationRefinementCertificate.size
    (cert : ModerateDeviationRefinementCertificate) : ℕ :=
  cert.varianceNumeratorWindow + cert.varianceDenominatorWindow +
    cert.powerDenominatorWindow + cert.slack

theorem moderateDeviation_tailBudgetWindow_le_size
    (cert : ModerateDeviationRefinementCertificate)
    (h : moderateDeviationRefinementReady cert) :
    cert.tailBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, htail⟩
  exact htail

def sampleModerateDeviationRefinementCertificate :
    ModerateDeviationRefinementCertificate where
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 1
  powerDenominatorWindow := 3
  tailBudgetWindow := 6
  slack := 1

example :
    moderateDeviationRefinementReady sampleModerateDeviationRefinementCertificate := by
  norm_num [moderateDeviationRefinementReady,
    ModerateDeviationRefinementCertificate.parametersControlled,
    ModerateDeviationRefinementCertificate.tailControlled,
    sampleModerateDeviationRefinementCertificate]

example :
    sampleModerateDeviationRefinementCertificate.tailBudgetWindow ≤
      sampleModerateDeviationRefinementCertificate.size := by
  apply moderateDeviation_tailBudgetWindow_le_size
  norm_num [moderateDeviationRefinementReady,
    ModerateDeviationRefinementCertificate.parametersControlled,
    ModerateDeviationRefinementCertificate.tailControlled,
    sampleModerateDeviationRefinementCertificate]


structure ModerateDeviationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationsBudgetCertificate.controlled
    (c : ModerateDeviationsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ModerateDeviationsBudgetCertificate.budgetControlled
    (c : ModerateDeviationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ModerateDeviationsBudgetCertificate.Ready
    (c : ModerateDeviationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ModerateDeviationsBudgetCertificate.size
    (c : ModerateDeviationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem moderateDeviations_budgetCertificate_le_size
    (c : ModerateDeviationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleModerateDeviationsBudgetCertificate :
    ModerateDeviationsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleModerateDeviationsBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationsBudgetCertificate.controlled,
      sampleModerateDeviationsBudgetCertificate]
  · norm_num [ModerateDeviationsBudgetCertificate.budgetControlled,
      sampleModerateDeviationsBudgetCertificate]

example :
    sampleModerateDeviationsBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationsBudgetCertificate.size := by
  apply moderateDeviations_budgetCertificate_le_size
  constructor
  · norm_num [ModerateDeviationsBudgetCertificate.controlled,
      sampleModerateDeviationsBudgetCertificate]
  · norm_num [ModerateDeviationsBudgetCertificate.budgetControlled,
      sampleModerateDeviationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleModerateDeviationsBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationsBudgetCertificate.controlled,
      sampleModerateDeviationsBudgetCertificate]
  · norm_num [ModerateDeviationsBudgetCertificate.budgetControlled,
      sampleModerateDeviationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleModerateDeviationsBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ModerateDeviationsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleModerateDeviationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleModerateDeviationsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ModerateDeviations
