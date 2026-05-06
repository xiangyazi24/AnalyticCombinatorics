import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Rouche Models

Finite boundary dominance descriptors for Rouche-style zero counting.
-/

namespace AnalyticCombinatorics.AppB.RoucheModels

def dominatesOnSamples (f g : List ℚ) : Bool :=
  (List.range (max f.length g.length)).all fun i => g.getD i 0 < f.getD i 0

theorem dominatesOnSamples_examples :
    dominatesOnSamples [3, 4, 5] [1, 2, 3] = true ∧
    dominatesOnSamples [3, 1, 5] [1, 2, 3] = false := by
  native_decide

structure RoucheData where
  boundarySamples : ℕ
  dominantMarginNumerator : ℕ
  dominantMarginDenominator : ℕ

def basicRoucheData : RoucheData where
  boundarySamples := 16
  dominantMarginNumerator := 1
  dominantMarginDenominator := 10

theorem basicRoucheData_values :
    basicRoucheData.boundarySamples = 16 ∧
    basicRoucheData.dominantMarginNumerator = 1 ∧
    basicRoucheData.dominantMarginDenominator = 10 := by
  native_decide

def zeroCountToy (degree : ℕ) : ℕ :=
  degree

theorem zeroCountToy_samples :
    zeroCountToy 0 = 0 ∧ zeroCountToy 3 = 3 := by
  native_decide

def roucheDataReady (data : RoucheData) : Prop :=
  0 < data.boundarySamples ∧ 0 < data.dominantMarginNumerator ∧
    0 < data.dominantMarginDenominator

theorem basicRoucheData_ready : roucheDataReady basicRoucheData := by
  unfold roucheDataReady basicRoucheData
  native_decide

def RoucheTheoremSchema
    (f g : ℂ → ℂ) (data : RoucheData) : Prop :=
  roucheDataReady data ∧ f 0 = 0 ∧ g 0 = 1

theorem rouche_theorem_schema_statement :
    RoucheTheoremSchema (fun z => z) (fun _ => 1) basicRoucheData := by
  unfold RoucheTheoremSchema roucheDataReady basicRoucheData
  norm_num


structure RoucheModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoucheModelsBudgetCertificate.controlled
    (c : RoucheModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RoucheModelsBudgetCertificate.budgetControlled
    (c : RoucheModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RoucheModelsBudgetCertificate.Ready
    (c : RoucheModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RoucheModelsBudgetCertificate.size
    (c : RoucheModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem roucheModels_budgetCertificate_le_size
    (c : RoucheModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRoucheModelsBudgetCertificate :
    RoucheModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRoucheModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RoucheModelsBudgetCertificate.controlled,
      sampleRoucheModelsBudgetCertificate]
  · norm_num [RoucheModelsBudgetCertificate.budgetControlled,
      sampleRoucheModelsBudgetCertificate]

example :
    sampleRoucheModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRoucheModelsBudgetCertificate.size := by
  apply roucheModels_budgetCertificate_le_size
  constructor
  · norm_num [RoucheModelsBudgetCertificate.controlled,
      sampleRoucheModelsBudgetCertificate]
  · norm_num [RoucheModelsBudgetCertificate.budgetControlled,
      sampleRoucheModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRoucheModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RoucheModelsBudgetCertificate.controlled,
      sampleRoucheModelsBudgetCertificate]
  · norm_num [RoucheModelsBudgetCertificate.budgetControlled,
      sampleRoucheModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRoucheModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRoucheModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RoucheModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRoucheModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRoucheModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.RoucheModels
