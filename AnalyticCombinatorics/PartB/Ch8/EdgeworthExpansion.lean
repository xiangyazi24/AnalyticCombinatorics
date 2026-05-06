import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VIII: Edgeworth Expansion

Finite cumulant and correction-polynomial models for Edgeworth expansions.
-/

namespace AnalyticCombinatorics.PartB.Ch8.EdgeworthExpansion

def hermite3 (x : ℤ) : ℤ :=
  x ^ 3 - 3 * x

def hermite4 (x : ℤ) : ℤ :=
  x ^ 4 - 6 * x ^ 2 + 3

theorem hermite_samples :
    (List.map hermite3 [-2, -1, 0, 1, 2]) = [-2, 2, 0, -2, 2] ∧
    (List.map hermite4 [-1, 0, 1]) = [-2, 3, -2] := by
  native_decide

def edgeworthCorrection1 (skewNumerator skewDenominator : ℚ) (x : ℤ) : ℚ :=
  skewNumerator / skewDenominator * (hermite3 x : ℚ)

theorem edgeworthCorrection1_samples :
    edgeworthCorrection1 1 6 2 = 1 / 3 ∧
    edgeworthCorrection1 1 6 0 = 0 := by
  native_decide

structure EdgeworthData where
  skewNumerator : ℤ
  skewDenominator : ℕ
  kurtosisNumerator : ℤ
  kurtosisDenominator : ℕ

def symmetricEdgeworthData : EdgeworthData where
  skewNumerator := 0
  skewDenominator := 1
  kurtosisNumerator := 0
  kurtosisDenominator := 1

theorem symmetricEdgeworthData_values :
    symmetricEdgeworthData.skewNumerator = 0 ∧
    symmetricEdgeworthData.skewDenominator = 1 ∧
    symmetricEdgeworthData.kurtosisNumerator = 0 := by
  native_decide

def edgeworthDataReady (data : EdgeworthData) : Prop :=
  0 < data.skewDenominator ∧ 0 < data.kurtosisDenominator

theorem symmetricEdgeworthData_ready : edgeworthDataReady symmetricEdgeworthData := by
  unfold edgeworthDataReady symmetricEdgeworthData
  native_decide

def EdgeworthExpansionSchema
    (mass : ℕ → ℕ → ℚ) (data : EdgeworthData) : Prop :=
  edgeworthDataReady data ∧ mass 0 0 = 0

theorem edgeworth_expansion_schema_statement :
    EdgeworthExpansionSchema (fun _ _ => 0) symmetricEdgeworthData := by
  unfold EdgeworthExpansionSchema edgeworthDataReady symmetricEdgeworthData
  native_decide


structure EdgeworthExpansionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthExpansionBudgetCertificate.controlled
    (c : EdgeworthExpansionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EdgeworthExpansionBudgetCertificate.budgetControlled
    (c : EdgeworthExpansionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EdgeworthExpansionBudgetCertificate.Ready
    (c : EdgeworthExpansionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EdgeworthExpansionBudgetCertificate.size
    (c : EdgeworthExpansionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem edgeworthExpansion_budgetCertificate_le_size
    (c : EdgeworthExpansionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEdgeworthExpansionBudgetCertificate :
    EdgeworthExpansionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleEdgeworthExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthExpansionBudgetCertificate.controlled,
      sampleEdgeworthExpansionBudgetCertificate]
  · norm_num [EdgeworthExpansionBudgetCertificate.budgetControlled,
      sampleEdgeworthExpansionBudgetCertificate]

example :
    sampleEdgeworthExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthExpansionBudgetCertificate.size := by
  apply edgeworthExpansion_budgetCertificate_le_size
  constructor
  · norm_num [EdgeworthExpansionBudgetCertificate.controlled,
      sampleEdgeworthExpansionBudgetCertificate]
  · norm_num [EdgeworthExpansionBudgetCertificate.budgetControlled,
      sampleEdgeworthExpansionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEdgeworthExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthExpansionBudgetCertificate.controlled,
      sampleEdgeworthExpansionBudgetCertificate]
  · norm_num [EdgeworthExpansionBudgetCertificate.budgetControlled,
      sampleEdgeworthExpansionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEdgeworthExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthExpansionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EdgeworthExpansionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEdgeworthExpansionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEdgeworthExpansionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.EdgeworthExpansion
