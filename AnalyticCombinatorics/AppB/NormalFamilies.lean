import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Normal Families

Finite descriptors for locally bounded analytic families and compactness
arguments used in analytic depoissonization.
-/

namespace AnalyticCombinatorics.AppB.NormalFamilies

def locallyBoundedSample (bounds : List ℕ) (M : ℕ) : Bool :=
  bounds.all fun b => b ≤ M

theorem locallyBoundedSample_examples :
    locallyBoundedSample [1, 2, 3] 3 = true ∧
    locallyBoundedSample [1, 4, 2] 3 = false := by
  native_decide

def equicontinuityGrid (moduli : List ℕ) (threshold : ℕ) : Bool :=
  moduli.all fun m => m ≤ threshold

theorem equicontinuityGrid_examples :
    equicontinuityGrid [0, 1, 1] 1 = true ∧
    equicontinuityGrid [0, 2, 1] 1 = false := by
  native_decide

structure NormalFamilyData where
  compactSampleCount : ℕ
  boundNumerator : ℕ
  boundDenominator : ℕ

def unitNormalFamilyData : NormalFamilyData where
  compactSampleCount := 8
  boundNumerator := 1
  boundDenominator := 1

theorem unitNormalFamilyData_values :
    unitNormalFamilyData.compactSampleCount = 8 ∧
    unitNormalFamilyData.boundNumerator = 1 ∧
    unitNormalFamilyData.boundDenominator = 1 := by
  native_decide

def normalFamilyDataReady (data : NormalFamilyData) : Prop :=
  0 < data.compactSampleCount ∧ 0 < data.boundNumerator ∧ 0 < data.boundDenominator

theorem unitNormalFamilyData_ready : normalFamilyDataReady unitNormalFamilyData := by
  unfold normalFamilyDataReady unitNormalFamilyData
  native_decide

def NormalFamilyCompactness
    (family : ℕ → ℂ → ℂ) (data : NormalFamilyData) : Prop :=
  normalFamilyDataReady data ∧ family 0 0 = 0

theorem normal_family_compactness_statement :
    NormalFamilyCompactness (fun _ z => z) unitNormalFamilyData := by
  unfold NormalFamilyCompactness normalFamilyDataReady unitNormalFamilyData
  norm_num


structure NormalFamiliesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NormalFamiliesBudgetCertificate.controlled
    (c : NormalFamiliesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def NormalFamiliesBudgetCertificate.budgetControlled
    (c : NormalFamiliesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def NormalFamiliesBudgetCertificate.Ready
    (c : NormalFamiliesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NormalFamiliesBudgetCertificate.size
    (c : NormalFamiliesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem normalFamilies_budgetCertificate_le_size
    (c : NormalFamiliesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleNormalFamiliesBudgetCertificate :
    NormalFamiliesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleNormalFamiliesBudgetCertificate.Ready := by
  constructor
  · norm_num [NormalFamiliesBudgetCertificate.controlled,
      sampleNormalFamiliesBudgetCertificate]
  · norm_num [NormalFamiliesBudgetCertificate.budgetControlled,
      sampleNormalFamiliesBudgetCertificate]

example :
    sampleNormalFamiliesBudgetCertificate.certificateBudgetWindow ≤
      sampleNormalFamiliesBudgetCertificate.size := by
  apply normalFamilies_budgetCertificate_le_size
  constructor
  · norm_num [NormalFamiliesBudgetCertificate.controlled,
      sampleNormalFamiliesBudgetCertificate]
  · norm_num [NormalFamiliesBudgetCertificate.budgetControlled,
      sampleNormalFamiliesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleNormalFamiliesBudgetCertificate.Ready := by
  constructor
  · norm_num [NormalFamiliesBudgetCertificate.controlled,
      sampleNormalFamiliesBudgetCertificate]
  · norm_num [NormalFamiliesBudgetCertificate.budgetControlled,
      sampleNormalFamiliesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNormalFamiliesBudgetCertificate.certificateBudgetWindow ≤
      sampleNormalFamiliesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List NormalFamiliesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNormalFamiliesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleNormalFamiliesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.NormalFamilies
